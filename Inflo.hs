{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module Inflo (doTurn) where

import Control.Monad (filterM, when, forM_, liftM, liftM2, foldM)
import GHC.Arr (unsafeIndex)
import Data.Functor ((<$>))
import Data.Array.Base (unsafeRead, unsafeAt)
import Data.Array.Unboxed
import Data.Array.IO
import Data.List
import Data.Ord
import qualified Data.Map as M
import Data.Maybe (fromJust, catMaybes)
import Data.Ord (comparing)
import qualified Data.Set as S
import System.IO
import System.Random
import Debug.Trace

import StateT
import Ants
import AStar
import Fight
import Stats

-- Data structure for internal state
data MyState = MyState {
         stPars    :: !GameParams,		-- game params
         stState   :: GameState Persist,	-- game state (extern)
         stPersist :: !Persist,			-- persistent internal state
         stBusy    :: !BitMap,			-- busy fields
         stUpper   :: !Point,			-- upper bound of the world
         stOrders  :: [Order],			-- accumulates orders
         stPlans   :: [(Point, Plan)],		-- accumulates plans
         stHills   :: [(Point, Int)],		-- alive hills
         stFrFood  :: !Food,			-- still untargeted food
         stLibGrad :: !LibGrad,			-- which ant can move where
         stHotSpots:: [Point],			-- battle centres
         stOurCnt  :: !Int,			-- total count of our ants
         stCanStay :: !Bool,			-- current ant can wait?
         stValDirs :: [(Dir, Point)],		-- valid directions for current ant
         stStatsFi :: !Stats,	-- time statistics for fight
         stStatsAs :: !Stats,	-- time statistics for aStar
         stCParam  :: !Int,	-- last calculation parameter (fight, astar)
         -- stTimeRem :: !Int,	-- time remaining (last measured)
         stDeltat  :: !Int	-- time for the next action (astar)
     }

data Persist = Persist {
         peSeen    :: !BitMap,	-- fields where we were (reduced by visibility radius)
         pePlMemo  :: !PlanMemo,	-- our plans
         peHills   :: [(Point, Int)],	-- hills we remember (not known to be razed)
         peVisi    :: Double,	-- visibility radius
         peStatsFi :: !Stats,	-- time statistics for fight
         peStatsAs :: !Stats,	-- time statistics for aStar
         peIMap    :: !InfMap,	-- general influence map
         peRndAttr :: [(Point, Int)]	-- random attractors in unseen regions
     }

type MyGame a = forall r. CPS r MyState IO a

-- Plans we calculate and must remember: priority, target and path
data Prio = Green | Yellow | Red deriving (Eq, Ord, Show)
data Plan = Plan {
                plPrio :: Prio,
                plTarget :: !Point,
                plPath :: ![PathInfo],
                plPLen :: !Int,
                plWait :: !Int
            } deriving Show
type PlanMemo = M.Map Point Plan
type LibGrad  = M.Map Point [EDir]

type InfMap  = UArray Point Int
type RBitMap = UArray Point Bool

-- Some constants and constant-like definitions:
msReserve = 120		-- reserve time for answer back (ms)
msDecrAst = 300		-- under this time we decrese the AStar searches per turn
msIncrAst = 450		-- over this time we increse the AStar searches per turn
maxMaxASt = 60		-- maximum AStar searches per turn
maxJumps  = 20		-- maximum jump length for jump point search
minAgrWhenEqual = 20	-- minimum of our ants to be aggresive when equal fight
attMajority = 0		-- used when attacking (beeing more aggresive)
hotMajority = 3		-- used when creating hot spots
maxPlanWait = 5		-- how long to wait in a plan when path is blocked
checkEasyFood = 10	-- how often to check for easy food?
maxSmellPath = 50	-- max steps for smell blood paths
cntLastAttack = 200	-- when we are so many, go to last attack
stepsToBlood = 15	-- afterwhich we reconsider
viewRadius   = (1*) . viewradius2	-- visibility radius
foodRadius   = (1*) . const 100	-- in which we go to food
homeRadius   = (1*) . const  50	-- in which we consider to be at home
homeRadius2  = (1*) . const 225	-- in which we consider to be at home
razeRadius   =        const 1900	-- in which we consider to raze enemy hills
dangerRadius = (1*) . attackradius2	-- in which we are in danger
foodIMMax = 1000	-- maximum influence for food
enhiIMMax0 = 2000	-- influence for enemy hill: constant factor
enhiIMMax1 =  10	-- influence for enemy hill: linear factor (* our ants)
hotsIMMax =  500	-- maximum influence for hot spots
enanIMMax =  800	-- maximum influence for enemy ants in home zone
ouspIMMax =  900	-- maximum influence for our ants (negative influence)
rndmIMMax = 1000	-- maximum influence for random spots
homeDefProc = 10	-- percent of our ants which should defend
homeDefRate = 100	-- increase per missing ant for home defend
timeIMDec = 20		-- time decay for food in percent (remaining)
spaceIMDec = 90		-- space decay for all in percent (remaining)
radNetDensity = 3	-- density of ants on the defence radius (ants / visibility)
circIMMax = 100		-- maximum influence on the home circumference
maxAttrsTries = 5	-- maximum tries to put new attractors
maxAttrsAtOnce = 1	-- maximum new random attractors per turn
timeToLive    = 50	-- how many turns random attractors live

doTurn :: GameParams -> GameState Persist -> IO ([Order], GameState Persist)
doTurn gp gs = do
  busy <- initBusy gs
  b <- getBounds $ water gs
  let upper = snd b
  -- get the persistent information (between turns)
  npers <- case userState gs of
               -- Just pers -> return $ cleanDeadPlans gs pers	-- is it necessary?
               Just pers -> return pers
               Nothing   -> do
                   let vs = 0.5 * sqrt (fromIntegral $ viewradius2 gp)
                   let sb = (pointToSeen (fst b) vs, pointToSeen upper vs)
                   nseen <- newArray sb False
                   let empIM = listArray b $ repeat 0
                   return $ Persist { peSeen = nseen, pePlMemo = M.empty, peHills = [],
                                      peIMap = empIM, peRndAttr = [], peVisi = vs,
                                      peStatsFi = newStats 1 25, peStatsAs = newStats 10 25 }
  remra <- updateSeen gs (peSeen npers) (peVisi npers) (peRndAttr npers)
  -- these are enemy hills we see this turn
  let hAlive = aliveHills upper (viewRadius gp) (hills gs) (peHills npers) (ours gs)
      (hio', hinow') = partition ((== 0) . snd) hAlive
      hio = map fst hio'
      hi  = map fst hinow'
      !st0 = MyState {
                   stPars = gp, stState = gs, stBusy = busy,
                   stPersist = npers { peHills = hAlive }, stUpper = upper,
                   stOrders = [], stPlans = [], stOurCnt = length (ours gs),
                   stHills = hAlive, stLibGrad = M.empty,
                   stHotSpots = [], stFrFood = food gs, -- `S.difference` tfood
                   -- stHotSpots = [], stFrFood = S.empty, -- `S.difference` tfood
                   -- stCanStay = True, stValDirs = [], stTimeRem = restTime, stCParam = 0,
                   stCanStay = True, stValDirs = [], stCParam = 0,
                   stStatsFi = peStatsFi npers, stStatsAs = peStatsAs npers, stDeltat = 0
               }
      -- zoneRadius1 = hellSteps (attackradius2 gp) 1
      zoneRadius2 = hellSteps (attackradius2 gp) 2
      fzs = fightZones upper zoneRadius2 (ours gs) (ants gs) []
  -- when (not $ null fzs) $ hPutStrLn stderr $ "Fight zones:\n" ++ show fzs
  st1 <- execState (fightAnts fzs) st0	-- first the fighting ants
  restTime <- timeRemaining gp gs
  hPutStrLn stderr $ "Time remaining (ms) after fight: " ++ show restTime
  -- some random attractors in the unseen zone when not enough food
  randat <- randomAttractors upper (peVisi npers) (peSeen npers) (foodP gs)
  uwater <- unsafeFreeze (water gs)
  let as = map snd $ ants gs
      randatn = randat ++ remra	-- random attractors - remaining & new ones
      -- set a net of attractors around our homes
      reseaux = fishNet upper (viewRadius gp) hio (ours gs) (turnno gs)
      -- collect all our homes with deficit in defence and the attacking enemy ants
      (hattrs, enants) = foldl collect ([], [])
                             $ map (homeDefenders gp upper (stOurCnt st1) (ours gs) as) hio
      enhi = enhiIMMax0 + enhiIMMax1 * stOurCnt st0	-- when we have more ants, stronger attack
      attrs = [(foodP gs, foodIMMax),		-- food
               (enants, enanIMMax),		-- enemy ants near our home
               (hi, enhi),			-- enemy hills
               (stHotSpots st1, hotsIMMax),	-- hotspots
               (map fst randatn, rndmIMMax)]		-- random spots
      oattrs = [(ours gs, ouspIMMax)]
  -- hPutStrLn stderr $ "Rnd.Attractors: " ++ show randatn
  -- im  <- updateIM (timeRemaining gp gs) False uwater (peIMap npers) $ attrs ++ hattrs ++ reseaux
  im  <- updateIM (timeRemaining gp gs) False uwater (peIMap npers) $ attrs ++ hattrs
  let sours = sortAnts st1 (ours gs)
  stf <- execState (freeAnts im (ours gs)) st1	-- then the free ants
  restTime <- timeRemaining gp gs
  let plans = M.fromList $ stPlans stf
      !fpers = (stPersist stf) { pePlMemo = plans, peIMap = im, peRndAttr = randatn,
                                 peStatsFi = stStatsFi stf, peStatsAs = stStatsAs stf }
      orders = stOrders stf
  hPutStrLn stderr $ "Time remaining (ms): " ++ show restTime
                        ++ ", ants: " ++ show (stOurCnt stf)
  let gsf = gs { ants = [], ours = [], foodP = [], userState = Just fpers }
      tn  = turnno gs
  when (tn `mod` 100 == 0) $ do
    hPutStrLn stderr "Statistics for fight:"
    hPutStrLn stderr $ showStats (stStatsFi stf)
    -- hPutStrLn stderr "Statistics for AStar:"
    -- hPutStrLn stderr $ showStats (stStatsAs stf)
  return (orders, gsf)

-- Attacs and defences of enemy hills: how many ants of us and of them are there?
hillAttacs :: Point -> Int -> Int -> [Point] -> [Point] -> Point -> (Point, (Int, Int))
hillAttacs bound rr hr os as h = (h, (us, them))
    where us   = length $ inRadius2 id rr bound h os
          them = length $ inRadius2 id hr bound h as

-- This is just a help function to collect the attacked own hills and the attacking
-- enemy ants in a form acceptable for updateIM
collect :: ([([Point], Int)], [Point]) -> (Point, Int, [Point]) -> ([([Point], Int)], [Point])
collect (hs, as) (h, v, as') = (([h], v):hs, as' ++ as)

-- We consider a home in danger when the number of defenders is less
-- then the number of attackers + some margin
-- For such homes we set an attract value proportional to the deficit
-- Also the attacking enemy ants get some attractor value
homeDefenders :: GameParams -> Point -> Int -> [Point] -> [Point] -> Point -> (Point, Int, [Point])
homeDefenders gp u cnt os as pt = (pt, v, aa)
    where d1 = length $ inRadius2 id (homeRadius  gp) u pt os
          d2 = length $ inRadius2 id (homeRadius2 gp) u pt os
          d  = d1 + (d2 - d1) `div` 2
          aa = inRadius2 id (homeRadius2 gp) u pt as
          a  = length aa
          c  = cnt * homeDefProc `div` 100
          v  = max 0 $ (c + a - d) * homeDefRate

-- Sort the ants by liberty grads -- less comes before
sortAnts :: MyState -> [Point] -> [Point]
sortAnts st = map fst . sortBy (comparing snd) . map (libs (stLibGrad st))
    where libs grds p = case M.lookup p grds of
                          Nothing -> (p, 5)	-- this is completely free
                          Just [] -> (p, 10)	-- this is involved in fight (already moved)
                          Just fr -> (p, length fr)	-- this is limited

-- Orders for the free ants (i.e. not fighting)
-- freeAnts :: InfMap -> [Point] -> MyGame ()
freeAnts foim = mapM_ (perAnt foim)

-- simple per ant
perAnt :: InfMap -> Point -> MyGame ()
perAnt foim pt = do
    (_, dps) <- getValidDirs pt
    if null dps
       then return ()	-- perhaps was already moved or cannot move at all
       else do
           hasPlan <- followPlan pt
           when (not hasPlan) $ do
               let infs = map inf dps
                   (v:vs) = map fst infs
                   -- alle = all (== v) vs
               followInfMap pt infs
    where inf (d, p) = (foim!p, d)

followInfMap pt infs = do
    let mi   = minimum $ map fst infs
        prs  = map (sqrm mi) infs
    d <- choose prs
    orderMove pt d "perAnt"
    return ()
    where -- which means: we weight the food and the enemy hills with different factors
          -- and multiply with another factor to get an entry for choose
          -- sqrm m (s, d) = let s1 = s - m in (s1*s1, d)
          sqrm m (s, d) = let s1 = s - m in (s1, d)

updateIM :: IO Int -> Bool -> RBitMap -> InfMap -> [([Point], Int)] -> IO InfMap
updateIM trio once rbm im phs = go $ amap decay im // asc
    where go a = do
             let a' = a `seq` difStep rbm a
             if once || a' == a
                then return a'
                else do
                   tr <- trio
                   if tr <= msReserve
                      then return a'
                      else go a'
          decay x = x * timeIMDec `div` 100
          asc = concatMap (\(ps, v) -> zip ps $ repeat v) phs

-- Our ants not involved in any fight zone
myFreeAnts :: [Point] -> [Point] -> [Point]
-- myFreeAnts os osf = S.toList $ S.fromList os `S.difference` (S.fromList $ concatMap fst fzs)
myFreeAnts os osf = S.toList $ S.fromList os `S.difference` S.fromList osf

hellSteps :: Int -> Int -> Int
hellSteps ar x = ar + x*x + ceiling (2 * fromIntegral x * sqrt (fromIntegral ar))

-- To select the fight zones (only the small ones can be calculated) we need an
-- intermediate data structure
data FZoneV = FZoneV { fzTotal, fzUs, fzThem :: !Int }

-- Orders for the fighting ants
fightAnts fs
    | null fs'  = return ()
    | otherwise = do
        st <- get
        let gp = stPars st
            gs = stState st
            u  = stUpper st
            r1 = hellSteps (attackradius2 gp) 1
            r0  = attackradius2 gp
        tr <- lift $ timeRemaining gp gs
        go r0 r1 tr fs'
    where fs' = map fst $ reverse $ sortBy (comparing $ fzTotal . snd)
                        $ filter (fzAccept . snd)
                        $ map fzVol fs
          fzVol fz@(ps, tm) = let lps = length ps
                                  ptm = points tm
                              in (fz, FZoneV { fzTotal = lps + ptm, fzUs = lps, fzThem = ptm })
          fzAccept fzv =  fzTotal fzv <= zoneMax
                       || fzTotal fzv <= zoneMaxMax && fzUs fzv <= zoneMaxUs
          go _ _ _   [] = return ()
          go a b tr0 (fz@(us, tm):fzs) = do
             st <- get
             let deltat = tr0 - msReserve
                 usl = length us
                 thl = points tm
                 lp  = usl + thl
                 maj = usl - thl
                 sf  = stStatsFi st
                 tn  = estimateTime sf lp
             -- debug $ "Remaining: " ++ show tr0 ++ ", estimate time: " ++ show tn
             tr' <- if (deltat < tn)
                       then return tr0
                       else do
                         perFightZone a b fz maj
                         let gp = stPars st
                             gs = stState st
                         tr <- lift $ timeRemaining gp gs
                         let fis = addParVal sf lp (tr0 - tr)
                         -- debug $ "Actually: " ++ show (tr0 - tr)
                         modify $ \s -> s { stStatsFi = fis }
                         return tr
             go a b tr' fzs

perFightZone r0 r1 fz@(us, themm) maj = do
    ho <- makeHotSpot fz maj
    st <- get
    ibusy <- liftIO $ do
             busy <- mapArray id (stBusy st)
             forM_ us $ \p -> writeArray busy p False
             unsafeFreeze busy
    let u   = stUpper st
        -- here are the parameter of the evaluation
        epar = fightParams st fz ho maj
        (sco, cfs) = nextTurn r0 r1 (valDirs ibusy u) epar us themm
        oac = fst cfs
    -- debug $ "Fight zone: us = " ++ show us ++ ", them = " ++ show themm
    let oacs = sortBy orderOrd oac
    -- debug $ "Params: " ++ show epar ++ " score = " ++ show sco ++ "\nOur moves: " ++ show oacs
    mapM_ extOrderMove oacs
    where valDirs :: UArray Point Bool -> Point -> Point -> [(Dir, Point)]
          valDirs w u pt = filter (not . (w!) . snd) $ map (\d -> (d, move u pt d)) allDirs

points tm = sum $ map length $ M.elems tm

fightParams st fz@(us, themm) ho maj
    = EvalPars { bnd = u, pes = pes', opt = 0, reg = reg',
                 agr = agr', tgt = tgt', tgs = tgs' }
    where u   = stUpper st
          gp  = stPars st
          gs  = stState st
          c   = stOurCnt st
          nhills = inRadius2 fst (homeRadius gp) u ho $ stHills st
          (ohills, ehills) = partition ((==0) . snd) nhills
          reg' = min 60 $ c * c `div` 200	-- by 0 is 0, by 100 is 50, maximum is 100
          agr' = maj >= attMajority && c > minAgrWhenEqual || maj > attMajority
          pes' = 100	-- if null nhills then 75 else 90
          (tgt', tgs') | null ohills && null ehills = (Nothing, (0, 0))
                       | null ohills = (Just $ fst $ head ehills, (100, 0))
                       | otherwise   = (Just $ fst $ head ohills, (0, -100))

extOrderMove :: (Point, EDir) -> MyGame ()
extOrderMove (pt, edir) = do
    case edir of
        Go d   -> orderMove pt d "fight" >> libGrad pt []
        Stay   -> markWait pt >> libGrad pt []
        Any ms -> libGrad pt ms

orderOrd :: (Point, EDir) -> (Point, EDir) ->  Ordering
orderOrd (_, Any _) _          = GT
orderOrd _          (_, Any _) = LT
orderOrd _          _          = EQ

libGrad :: Point -> [EDir] -> MyGame ()
libGrad p es = modify $ \s -> s { stLibGrad = M.insert p es (stLibGrad s) }

-- hotSpot (us, tm) = head us
hotSpot (us, tm) = gravCenter $ us ++ concat (M.elems tm)

makeHotSpot fz maj = do
    let gc = hotSpot fz
    when (maj < hotMajority) $ modify $ \s -> s { stHotSpots = gc : stHotSpots s }
    return gc

markWait pt = do
    st <- get
    let busy = stBusy st
    liftIO $ writeArray busy pt True
    return True

-- If we are very near to a food: try to pick it
easyFood :: Point -> Int -> MyGame (Maybe (Point, [PathInfo]))
easyFood pt maxl = do
  st <- get
  let frf = stFrFood st
  if S.null frf
     then return Nothing
     else do
         let fo = S.toList frf
             -- take the nearest food in visibility radius
             u  = stUpper st
             gp = stPars st
             foods = map fst $ takeWhile ((<= viewRadius gp) . snd) $ sortByDist id u pt fo
             deltat = stDeltat st
             stats = stStatsAs st
         if null foods
            then return Nothing
            else do
               let et = estimateTime stats ep
                   ep = viewRadius gp
               if et > deltat
                  then wanted "easyFood" ep et deltat >> return Nothing
                  else do
                      putLastAsParam (viewRadius gp)
                      toNearest pt foods maxl

toNearest :: Point -> [Point] -> Int -> MyGame (Maybe (Point, [PathInfo]))
toNearest pt pts maxl = do
    st <- get
    let u = stUpper st
        w = water . stState $ st
        ptsset = S.fromList pts
        ff = (`S.member` ptsset)	-- fulfill function (target hit condition)
    -- debug $ "Astar from " ++ show pt ++ " to " ++ show pts ++ ":"
    mpath <- liftIO $ aStar (natfoDirs w u ff) (listDistance u pts) pt ff (Just maxl)
    case mpath of
        Nothing    -> return Nothing
        Just path' -> if null path'
            then return Nothing
            else do
              let np = piPoint $ head path'
                  path = reverse path'
              -- debug $ "Path: " ++ show path
              return $ Just (np, path)
    where listDistance u list p = minimum $ map (distance u p) list

-- If we have a plan: execute it
-- But take care if the path is secure, i.e. the first step is allowed
-- Also if there is some easy food, try to take it (sometimes)
followPlan :: Point -> MyGame Bool
followPlan pt = do
    mplan <- getOldPlan pt
    case mplan of
        Nothing   -> return False	-- no plan
        Just plan -> do
            measy <- if (plPLen plan) `mod` checkEasyFood == 0	-- do we have an easy food?
                        then easyFood pt (plPLen plan)		-- check only now and then
                        else return Nothing
            case measy of
                Nothing          -> executePlan pt plan
                Just (fo, fpath) -> do
                    let lfo = sum (map piTimes fpath)
                        fplan = Plan { plPrio = Green, plTarget = fo, plPath = fpath,
                                       plPLen = lfo, plWait = 0 }
                    act <- choose [
                               (lfo, executePlan pt plan),
                               (plPLen plan, executePlan pt fplan)
                           ]
                    act

attacProbs :: Int -> Int -> Int -> Int -> (Int, Int)
attacProbs x us them ours = (us * us * ours `div` afact, them * them * dfact `div` ours)
    where afact = 10 * x
          dfact = 10 * x

getOldPlan :: Point -> MyGame (Maybe Plan)
getOldPlan pt = do
  plans <- gets (pePlMemo . stPersist)
  return $ M.lookup pt plans

-- Plans section
-- This is used when, having a plan, we can pick food (so we must wait), and then
-- we can continue later with the plan. So it's always returning True
replicatePlan :: Point -> MyGame Bool
replicatePlan pt = do
  mplan <- getOldPlan pt
  case mplan of
      Nothing   -> markWait pt
      Just plan -> do
          newPlan pt plan
          markWait pt

newPlan :: Point -> Plan -> MyGame ()
newPlan pt plan = modify $ \s -> s { stPlans = (pt, plan) : stPlans s }

-- Go to a point if there is no water in between
gotoPoint :: Bool -> Point -> Point -> MyGame Bool
gotoPoint _ pt to | pt == to = return False
gotoPoint isFood pt to = do
  st <- get
  let w = water . stState $ st
      u = stUpper st
      deltat = stDeltat st
      stats = stStatsAs st
      par = distance u pt to
  let et = estimateTime stats par
  if et > deltat
     then wanted "gotoPoint" par et deltat
     else do
       let ff = (== to)	-- target hit condition
       putLastAsParam par
       -- debug $ "Astar from " ++ show pt ++ " to " ++ show to ++ ":"
       mpath <- liftIO $ aStar (natfoDirs w u ff) (distance u to) pt ff Nothing
       case mpath of
         Nothing    -> return False
         Just path' -> do
           let path = reverse path'
               plan = Plan { plPrio = Green, plTarget = to, plPath = path,
                             plPLen = sum (map piTimes path), plWait = maxPlanWait }
           -- debug $ "Path: " ++ show path
           executePlan pt plan

-- Given a bitmap of "busy" points, and a source point, find
-- the valid directions to move
validDirs :: BitMap -> Point -> [Dir] -> Point -> IO [(Dir, Point)]
validDirs w u ds pt = notBitMap w u $ map (\d -> (d, move u pt d)) ds

-- For jump point search: only natural & forced neighbours are generated
natfoDirs :: BitMap -> Point -> (Point -> Bool) -> (Point, Maybe JPInfo) -> IO [(Point, JPInfo)]
natfoDirs w u fulf (pt, Nothing)  = map pathInfoToPJPInfo <$> validDirs w u allDirs pt
natfoDirs w u fulf (pt, Just jpi) = do
    let d = jpDir jpi
    mjp <- findJumpPoint w u fulf pt d 1				-- the jump point
    ts  <- map pathInfoToPJPInfo <$> validDirs w u (lrDirs d) pt	-- the turns
    return $ case mjp of
        Just jp -> jp : ts
        _       -> ts

pathInfoToPJPInfo :: (Dir, Point) -> (Point, JPInfo)
pathInfoToPJPInfo (d, p) = (p, JPInfo { jpDir = d, jpCost = 1 })

findJumpPoint :: BitMap -> Point -> (Point -> Bool) -> Point -> Dir -> Int
              -> IO (Maybe (Point, JPInfo))
findJumpPoint w u fulf pt d k = do
    let p = move u pt d
    if fulf p
       then return $ Just (p, jpi)	-- end points are jump points
       else do
           b <- readArray w p
           if b then return Nothing	-- dead end
                else if k >= maxJumps
                        then return $ Just (p, jpi)	-- reached max jump length
                        else do
                            blr <- bitMap w u $ map (\d -> (d, move u pt d)) (lrDirs d)
                            if null blr
                               then findJumpPoint w u fulf p d (k+1)
                               else return $ Just (p, jpi)
    where jpi = JPInfo { jpDir = d, jpCost = k }

lrDirs :: Dir -> [Dir]
lrDirs d = [dirdir succ d, dirdir pred d]
    where dirdir f = toEnum . (`mod` 4) . f . fromEnum

-- Gets the valid dirs to move (or stay), considering busy cells
-- and ants with less liberty grades (because they are
-- part of a fight zone)
getValidDirs :: Point -> MyGame (Bool, [(Dir, Point)])
getValidDirs pt = do
  st <- get
  let busy = stBusy st
      u = stUpper st
      mfg = M.lookup pt (stLibGrad st)
      (stp, ds) = maybe (True, allDirs) (edirToDirs False []) mfg
  bst <- liftIO $ readArray busy pt
  pi  <- liftIO $ validDirs busy u ds pt
  return (not bst && stp, pi)
  where edirToDirs bstay acc [] = (bstay, acc)
        edirToDirs bstay acc (ed:eds)
            = case ed of
                  Stay -> edirToDirs True acc eds
                  Go d -> edirToDirs bstay (d:acc) eds
                  _    -> edirToDirs bstay acc eds

-- The list cannot be null!
choose :: [(Int, a)] -> MyGame a
choose ias = do
    let iass = sortBy (comparing (negate . fst)) ias
        len  = sum $ map fst ias
    r <- liftIO $ randomRIO (1, len)
    let choosen = go r iass
    return choosen
    where go _ [a]    = snd a
          go r (a:as) = let i = fst a
                        in if r <= i then snd a else go (r - i) as

orderMove :: Point -> Dir -> String -> MyGame Bool
orderMove p d lo = do
    st <- get
    let busy = stBusy st
        u = stUpper st
        mvo = Order { source = p, direction = d, logic = lo }
        i = move u p d
    liftIO $ writeArray busy p False
    liftIO $ writeArray busy i True
    -- debug $ "Order: " ++ show p ++ " -> " ++ show d ++ " (= " ++ show i ++ ")"
    put st { stOrders = mvo : stOrders st }
    return True

executePlan :: Point -> Plan -> MyGame Bool
executePlan pt plan | null (plPath plan) = return False
executePlan pt plan = do
    let (pi : path) = plPath plan
        p = piPoint pi
    w <- isWater p
    if w
       then return False
       else do
           b  <- isBusy p
           vs <- gets stValDirs
           let d = piDir pi
               dp = (d, p)
           if b || not (dp `elem` vs)
              then do	-- we cannot (yet) move to follow the plan
                  cst <- gets stCanStay
                  if not cst
                     then return False	-- we cannot wait, cannot move - abort the plan
                     else do
                         act <- choose [
                             (1, return False),
                             (plWait plan - 1, 
                                 newPlan p plan { plWait = plWait plan - 1 } >> markWait pt)
                             ]
                         act
              else do
                  npath <- stepMultPath pi path
                  newPlan p plan { plPath = npath, plPLen = plPLen plan - 1, plWait = maxPlanWait }
                  orderMove pt d "execPlan"

stepMultPath :: PathInfo -> [PathInfo] -> MyGame [PathInfo]
stepMultPath pi pis
    | piTimes pi == 1 = return pis
    | otherwise = do
        u <- gets stUpper
        let p = move u (piPoint pi) (piDir pi)
        return $ pi { piPoint = p, piTimes = piTimes pi - 1 } : pis

putLastAsParam :: Int -> MyGame ()
putLastAsParam x = modify $ \s -> s { stCParam = x }

aliveHills :: Point -> Int -> [(Point, Int)] -> [(Point, Int)] -> [Point] -> [(Point, Int)]
aliveHills bound vr2 hinow himem myants = hinow ++ filter inviz notseen
    where notseen = himem \\ hinow	-- remembered but not seen now
          inviz (h, _) = null $ inRadius2 id vr2 bound h myants

aliveFood :: Point -> Int -> [Point] -> [Point] -> [Point] -> [Point]
aliveFood bound vr2 fnow fmem myants = fnow ++ filter inviz notseen
    where notseen = fmem \\ fnow
          inviz p = null $ inRadius2 id vr2 bound p myants

fishNet :: Point -> Int -> [Point] -> [Point] -> Int -> [([Point], Int)]
fishNet _ _  [] _  _    = []
fishNet u v2 hs as turn
    = trace ("Trace fishNet:\n" ++ "apn=" ++ show apn ++ ", r=" ++ show r
                       ++ ", np = " ++ show np
            )
            map circumvent hs
    where n   = fromIntegral (length hs) :: Double
          v'  = fromIntegral v2
          vr  = sqrt v'
          apn = fromIntegral (length as) / n
          -- r = -pi * v' + vr * sqrt (pi * pi * v' + apn)
          r = max (2 * vr) $ apn / 10	-- approximate
          ptpa = 3
          np = ceiling $ 2 * pi * r / ptpa
          sel = turn `mod` np
          pts h = [ sumPoint u h (cirp t) | x <- [1..3], let t = x * sel]
          cco = 2 * pi / fromIntegral np
          cirp t = let t' = fromIntegral t * cco
                   in (ceiling $ r * sin t', ceiling $ r * cos t')
          circumvent h = (pts h, circIMMax)

-- Try to set (at most) maxAttrsAtOnce attractors in unseen regions
-- by maxAttrsTries tries
randomAttractors :: Point -> Double -> BitMap -> [Point] -> IO [(Point, Int)]
randomAttractors u v bm fo = go maxAttrsTries maxAttrsAtOnce []
    where mx = fst u - 1
          my = snd u - 1
          go _ 0 acc = return acc
          go 0 _ acc = return acc
          go try k acc = do
             rx <- randomRIO (0, mx)
             ry <- randomRIO (0, my)
             let rp = pointToSeen (rx, ry) v
             se <- readArray bm rp
             if se then go (try-1) k acc else go (try-1) (k-1) (((rx, ry), timeToLive):acc)

wanted :: String -> Int -> Int -> Int -> MyGame Bool
wanted what ep et deltat = return False
--    debug $ "Wanted " ++ what ++ " with ep/et = " ++ show ep ++ " / " ++ show et
--           ++ " but deltat = " ++ show deltat
--    return False

-- Init bad/busy squares: just a copy of water
-- plus the food and the current own ants
initBusy :: GameState Persist -> IO BitMap
initBusy gs = do
    busy <- mapArray id (water gs)
    forM_ (ours gs ++ foodP gs) $ \p -> writeArray busy p True
    -- forM_ (foodP gs) $ \p -> writeArray busy p True
    return busy

updateSeen :: GameState Persist -> BitMap -> Double -> [(Point, Int)] -> IO [(Point, Int)]
updateSeen gs seen vs ras = do
    forM_ (ours gs) $ \p -> writeArray seen (pointToSeen p vs) True
    let ras' = map (\(p, t) -> (p, t-1)) $ filter ((>1) . snd) ras
    filterM (\(p, _) -> not <$> readArray seen (pointToSeen p vs)) ras'

realToSeen :: Int -> Double -> Int
realToSeen x v = ceiling $ fromIntegral x / v + 0.5 

pointToSeen :: Point -> Double -> Point
pointToSeen (x, y) v = (realToSeen x v, realToSeen y v)

isBitMap :: (MyState -> BitMap) -> Point -> MyGame Bool
isBitMap f p = do
    bm <- gets f
    lift $ readArray bm p

isWater = isBitMap (water . stState)

isBusy = isBitMap stBusy

canStay :: MyGame Bool -> MyGame Bool -> MyGame Bool
canStay ifYes ifNo = do
    cs <- gets stCanStay
    if cs then ifYes else ifNo

filterBusy :: (a -> Point) -> [a] -> MyGame [a]
filterBusy f as = do
    st <- get
    let busy = stBusy st
    lift $ filterM (\a -> liftM not $ readArray busy (f a)) as

bitMap, notBitMap :: BitMap -> Point -> [(a, Point)] -> IO [(a, Point)]
bitMap    w u = filterM (            unsafeRead w . unsafeIndex ((0, 0), u) . snd)
notBitMap w u = filterM (liftM not . unsafeRead w . unsafeIndex ((0, 0), u) . snd)

difStep :: RBitMap -> InfMap -> InfMap
difStep rbm im = array bs $ inter ++ left ++ right ++ up ++ down ++ [corld, corlu, corrd, corru]
    where bs@((x0, y0), (x1, y1)) = bounds im
          inter = [ finter x y | x <- [x0+1..x1-1], y <- [y0+1..y1-1]]
          left  = [ fleft x0 y | y <- [y0+1..y1-1]]
          right = [ fright x1 y | y <- [y0+1..y1-1]]
          up    = [ fup x y1 | x <- [x0+1..x1-1]]
          down  = [ fdown x y0 | x <- [x0+1..x1-1]]
          finter x y = dif x y $ maximum $ map (im!) [(x, y-1), (x, y+1), (x-1, y), (x+1, y)]
          fleft  x y = dif x y $ maximum $ map (im!) [(x0, y-1), (x0, y+1), (x01, y), (x1, y)]
          fright x y = dif x y $ maximum $ map (im!) [(x1, y-1), (x1, y+1), (x11, y), (x0, y)]
          fup    x y = dif x y $ maximum $ map (im!) [(x, y11), (x, y0), (x-1, y1), (x+1, y1)]
          fdown  x y = dif x y $ maximum $ map (im!) [(x, y01), (x, y1), (x-1, y0), (x+1, y0)]
          corld = dif x0 y0 $ maximum $ map (im!) [(x0, y01), (x01, y0), (x0, y1), (x1, y0)]
          corlu = dif x0 y1 $ maximum $ map (im!) [(x0, y11), (x01, y1), (x0, y01), (x1, y1)]
          corrd = dif x1 y0 $ maximum $ map (im!) [(x1, y01), (x11, y0), (x1, y1), (x0, y0)]
          corru = dif x1 y1 $ maximum $ map (im!) [(x1, y11), (x11, y1), (x1, y01), (x0, y1)]
          x01 = x0 + 1
          x11 = x1 - 1
          y11 = y1 - 1
          y01 = y0 + 1
          dif x y m = let xy = (x, y)
                      in if rbm!xy then (xy, 0) else (xy, max (im!xy) (m * spaceIMDec `div` 100))
          a!i = unsafeAt a (unsafeIndex bs i)

difNSteps :: Int -> RBitMap -> InfMap -> InfMap
difNSteps k rbm = head . drop k . iterate (difStep rbm)

debug :: String -> MyGame ()
debug s = liftIO $ hPutStrLn stderr s
-- debug _ = return ()
