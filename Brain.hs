{-# LANGUAGE RankNTypes #-}

module Brain (doTurn) where

import Control.Monad (filterM, when, forM_, liftM, liftM2, foldM)
import Data.Array.Unboxed
import Data.Array.IO
import Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust, catMaybes)
import Data.Ord (comparing)
import qualified Data.Set as S
import System.IO
import System.Random

import StateT
import Ants
import AStar
import Fight

-- Data structure for internal state
data MyState = MyState {
         stPars    :: GameParams,		-- game params
         stState   :: GameState Persist,	-- game state (extern)
         stPersist :: Persist,			-- persistent internal state
         stBusy    :: BitMap,			-- busy fields
         stUpper   :: Point,			-- upper bound of the world
         stOrders  :: [Order],			-- accumulates orders
         stPlans   :: [(Point, Plan)],		-- accumulates plans
         stWeakEH  :: [(Point, (Int, Int))],	-- weakness of enemy hills
         stFrFood  :: Food,			-- still untargeted food
         stLibGrad :: LibGrad,			-- which ant can move where
         stHotSpots:: [Point],			-- battle centres
         stOurCnt  :: Int,			-- total count of our ants
         stCrtASt  :: Int,			-- current astar searches
         stCanStay :: Bool,			-- current ant can wait?
         stValDirs :: [PathInfo]		-- valid directions for current ant
     }

data Persist = Persist {
         peSeen    :: BitMap,	-- fields where we were
         pePlMemo  :: PlanMemo,	-- our plans
         peEnHills :: [Point],	-- enemy hills (not razed by us)
         peMaxPASt :: Int	-- maximum astar searches per turn
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

-- Some constants and constant-like definitions:
msReserve = 150		-- reserve time for answer back (ms)
msDecrAst = 300		-- under this time we decrese the AStar searches per turn
msIncrAst = 650		-- over this time we increse the AStar seraches per turn
maxMaxASt = 70		-- maximum AStar searches per turn
attMajority = 2		-- used when attacking many to many
maxPlanWait = 3		-- how long to wait in a plan when path is blocked
checkEasyFood = 10	-- how often to check for easy food?
zoneMax      = 9	-- max ants in a zone fight
maxSmellPath = 60	-- max steps for smell blood paths
cntLastAttack = 200	-- when we are so many, go to last attack
stepsToBlood = 10	-- afterwhich we reconsider
viewRadius   = (1*) . viewradius2	-- visibility radius
foodRadius   = (1*) . const 100	-- in which we go to food
homeRadius   = (1*) . const 100	-- in which we consider to be at home
razeRadius   =        const 1900	-- in which we consider to raze enemy hills
dangerRadius = (1*) . attackradius2	-- in which we are in danger
kamikaRadius = (1*) . attackradius2	-- we try a one to one fight (as we die anyway)

doTurn :: GameParams -> GameState Persist -> IO ([Order], GameState Persist)
doTurn gp gs = do
  busy <- initBusy gs
  b <- getBounds $ water gs
  -- get the persistent information (between turns)
  npers <- case userState gs of
               -- Just pers -> return $ cleanDeadPlans gs pers	-- is it necessary?
               Just pers -> return pers
               Nothing   -> do
                   nseen <- newArray b False
                   return $ Persist { peSeen = nseen, pePlMemo = M.empty,
                                      peEnHills = [], peMaxPASt = maxMaxASt }
  updateSeen gs (peSeen npers)
  -- these are enemy hills we see this turn
  let hinow = map fst $ filter ((/= 0) . snd) $ hills gs
  -- take only the active ones (actually not razed by us)
  hi <- filterM (liftM not . readArray (peSeen npers)) $ nub $ hinow ++ peEnHills npers
  let attacs = map (hillAttacs (snd b) (razeRadius gp) (homeRadius gp) (ours gs) (map snd $ ants gs)) hi
      tfood = S.fromList $ map plTarget $ M.elems (pePlMemo npers)	-- plan targets
      st0 = MyState {
                   stPars = gp, stState = gs, stBusy = busy,
                   stPersist = npers { peEnHills = hi },
                   stUpper = snd b, stOrders = [], stPlans = [],
                   stOurCnt = length (ours gs), stWeakEH = attacs,
                   stLibGrad = M.empty, stCrtASt = peMaxPASt npers,
                   stHotSpots = [], stFrFood = food gs, -- `S.difference` tfood
                   stCanStay = True, stValDirs = []
               }
      zoneRadius2 = hellSteps (attackradius2 gp) 2
      fzs = fightZones (snd b) zoneRadius2 (ours gs) (ants gs) []
  -- when (not $ null fzs) $ hPutStrLn stderr $ "Fight zones:\n" ++ show fzs
  st1 <- execState (fightAnts fzs) st0	-- first the fighting ants
  stf <- execState (freeAnts 1 (ours gs)) st1	-- then the free ants
  restTime <- timeRemaining gp gs
  let plans = M.fromList $ stPlans stf
      astpt = aStarNextTurn (peMaxPASt npers) restTime
      fpers = (stPersist stf) { pePlMemo = plans, peMaxPASt = astpt }
      orders = stOrders stf
  hPutStrLn stderr $ "Time remaining (ms): " ++ show restTime
  -- hPutStrLn stderr $ "Next aStar per turn: " ++ show astpt
  let gsf = gs { ants = [], ours = [], foodP = [], userState = Just fpers }
  return (orders, gsf)

aStarNextTurn :: Int -> Int -> Int
aStarNextTurn prv tm
    | tm <= msDecrAst = max 1 (prv `div` 2)	-- minimum 1
    | tm >= msIncrAst = min maxMaxASt (prv + 1)	-- maximum as per parameter
    | otherwise       = prv

-- Attacs and defences of enemy hills: how many ants of us and of them are there?
hillAttacs :: Point -> Int -> Int -> [Point] -> [Point] -> Point -> (Point, (Int, Int))
hillAttacs bound rr hr os as h = (h, (us, them))
    where us   = length $ inRadius2 id rr bound h os
          them = length $ inRadius2 id hr bound h as

{--
-- Clean plans of our dead ants
cleanDeadPlans :: GameState Persist -> Persist -> (Persist, [Plan])
cleanDeadPlans gs pe =
    where npl = M.intersection (pePlMemo pe) $ M.fromList $ zip (ours gs) $ repeat True
--}

-- Orders for the free ants (i.e. not fighting
-- makeOrders :: [Point] -> MyGame [Order]
freeAnts :: Int -> [Point] -> MyGame ()
freeAnts _ [] = return ()
freeAnts i points = do
  st <- get
  let gp = stPars  st
      gs = stState st
  tr <- if i `mod` 10 == 0	-- to avoid to take the time so often
           then return msReserve
           else lift $ timeRemaining gp gs
  when (tr >= msReserve) $ do
      perAnt $ head points
      freeAnts (i+1) $ tail points

-- Our ants not involved in any fight zone
myFreeAnts :: [Point] -> [Point] -> [Point]
-- myFreeAnts os osf = S.toList $ S.fromList os `S.difference` (S.fromList $ concatMap fst fzs)
myFreeAnts os osf = S.toList $ S.fromList os `S.difference` S.fromList osf

hellSteps :: Int -> Int -> Int
hellSteps ar x = ar + x*x + ceiling (2 * fromIntegral x * sqrt (fromIntegral ar))

-- Orders for the fighting ants
fightAnts fs
    | null fs'  = return ()
    | otherwise = do
        st <- get
        let gp = stPars st
            u  = stUpper st
            r1 = hellSteps (attackradius2 gp) 1
            r0  = attackradius2 gp
        mapM_ (perFightZone r0 r1) fs'
    where fs' = filter (\(ps, tm) -> length ps + points tm <= zoneMax) fs

perFightZone r0 r1 fz@(us, themm) = do
    ho <- makeHotSpot fz
    st <- get
    ibusy <- liftIO $ do
             busy <- mapArray id (stBusy st)
             forM_ us $ \p -> writeArray busy p False
             unsafeFreeze busy
    let u   = stUpper st
        -- here are the parameter of the evaluation
        epar = fightParams st fz
        (sco, cfs) = nextTurn u r0 r1 (valDirs ibusy u) epar us themm
        oac = fst cfs
    debug $ "Fight zone: us = " ++ show us ++ ", them = " ++ show themm
    debug $ "Params: " ++ show epar ++ " score = " ++ show sco ++ "\nOur moves: " ++ show oac
    mapM_ extOrderMove oac
    where valDirs :: UArray Point Bool -> Point -> Point -> [(Dir, Point)]
          valDirs w u pt = filter (not . (w!) . snd) $ map (\d -> (d, move u pt d)) allDirs

points tm = sum $ map length $ M.elems tm

fightParams st fz@(us, themm) = EvalPars { pes = pes', opt = 0, reg = reg',
                                           agr = agr', tgt = Nothing }
    where u   = stUpper st
          gp  = stPars st
          gs  = stState st
          c   = stOurCnt st
          ho  = hotSpot fz
          nhills = inRadius2 fst (homeRadius gp) u ho $ hills gs
          usl  = length us
          thl  = points themm
          maj  = usl - thl
          reg' = min 100 $ c * c `div` 200	-- by 0 is 0, by 100 is 50, maximum is 100
          agr' = maj >= 1
          pes' = if null nhills then 70 else 20

extOrderMove :: (Point, EDir) -> MyGame ()
extOrderMove (pt, edir) = do
    case edir of
        Go d   -> orderMove pt d "fight" >> libGrad pt []
        Stay   -> markWait pt >> libGrad pt []
        Any ms -> libGrad pt ms

libGrad :: Point -> [EDir] -> MyGame ()
libGrad p es = modify $ \s -> s { stLibGrad = M.insert p es (stLibGrad s) }

hotSpot (us, tm) = gravCenter $ us ++ concat (M.elems tm)

makeHotSpot fz = do
    let gc = hotSpot fz
    modify $ \s -> s { stHotSpots = gc : stHotSpots s }
    return gc

markWait pt = do
    st <- get
    let busy = stBusy st
    liftIO $ writeArray busy pt True
    return True

-- Combine the strategies for the move generation
(<|>) :: MyGame Bool -> MyGame Bool -> MyGame Bool
m1 <|> m2 = m1 >>= \r -> if r then return r else m2

infixr 1 <|> 

perAnt :: Point -> MyGame Bool
perAnt pt = do
    svs <- getValidDirs pt
    if not (fst svs) && null (snd svs)
       then return True	-- it looks this one was already moved
       else do
           modify $ \s -> s { stCanStay = fst svs, stValDirs = snd svs }
           getGoal pt

getGoal :: Point -> MyGame Bool
getGoal pt =
    oneChoice pt <|>	-- if we have only one choice, take it
    immRaze pt <|>	-- if we can immediately raze a hill, do it
    pickFood pt <|>	-- immediate food pick
    followPlan pt <|>	-- follow a plan
    razeAttac pt <|>	-- raze attack
    smellBlood pt <|>	-- if there is some battle, go there
    gotoFood pt <|>	-- find some food
    rest pt		-- whatever...

-- When we have only one choice, take it
oneChoice :: Point -> MyGame Bool
oneChoice pt = do
    st <- get
    if stCanStay st
       then if null $ stValDirs st
               then markWait pt	-- we can only wait
               else return False
       else case stValDirs st of
                [(d, _)] -> orderMove pt d "oneChoice"	-- the only possibility
                _        -> return False

-- When we can raze some hill not defended: do it!
immRaze :: Point -> MyGame Bool
immRaze pt = do
    mhr <- hillToRaze pt viewRadius
    case mhr of
        Nothing     -> return False
        Just (h, x) -> do
            st <- get
            let bound = stUpper st
                as = map snd $ ants $ stState st
            if null $ inRadius2 id x bound h as
               then gotoPoint False pt h
               else return False

-- If we stay near a food square: wait one turn to pick it
pickFood :: Point -> MyGame Bool
pickFood pt = do
  food <- gets $ food . stState
  fs   <- foodPoints pt
  let foods = getFoods food fs
  if null foods
     then return False
     else canStay (deleteTargets foods >> replicatePlan pt) (return False)

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
             mx = stCrtASt st	-- we are limited by aStar searches
             foods = map fst $ takeWhile ((<= viewRadius gp) . snd) $ sortByDist id u pt fo
         if mx <= 0 || null foods
            then return Nothing
            else toNearest pt foods maxl

toNearest :: Point -> [Point] -> Int -> MyGame (Maybe (Point, [PathInfo]))
toNearest pt pts maxl = do
    st <- get
    let u = stUpper st
        w = water . stState $ st
        ptsset = S.fromList pts
    mpath <- liftIO $ aStar (validDirs w u allDirs) (listDistance u pts) pt (`S.member` ptsset) (Just maxl)
    modify $ \s -> s { stCrtASt = stCrtASt s - 1 }
    case mpath of
        Nothing    -> return Nothing
        Just path' -> if null path'
            then return Nothing
            else do
              let np = snd $ head path'
                  path = reverse path'
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
            vs <- gets stValDirs
            let pp = plPath plan
            if null pp || not (head pp `elem` vs)
               then return False	-- path is empty or first step not allowed
               else do
                 measy <- if (plPLen plan) `mod` checkEasyFood == 0	-- do we have an easy food?
                             then easyFood pt (plPLen plan)		-- check only now and then
                             else return Nothing
                 case measy of
                     Nothing          -> executePlan pt plan
                     Just (fo, fpath) -> if (head fpath `elem` vs)
                         then do
                             let lfo = length fpath
                                 fplan = Plan { plPrio = Green, plTarget = fo, plPath = fpath,
                                                plPLen = lfo, plWait = 0 }
                             act <- choose [
                                        (lfo, executePlan pt plan),
                                        (plPLen plan, executePlan pt fplan)
                                    ]
                             act
                         else executePlan pt plan

-- How to attack and raze an enemy hill
razeAttac :: Point -> MyGame Bool
razeAttac pt = do
    mhr <- hillToRaze pt razeRadius
    case mhr of
        Nothing     -> return False
        Just (h, x) -> do
            st <- get
            case lookup h (stWeakEH st) of
                Nothing         -> return False
                Just (us, them) -> do
                    let weall = stOurCnt st
                        (attac, retra) = attacProbs x us them weall
                    -- debug $ "Attack from " ++ show pt ++ " to " ++ show h
                    -- debug $ "- Params: "
                    --         ++ concat (intersperse " / " (map show [x, us, them, weall]))
                    -- debug $ "- Probs:  " ++ show attac ++ " <-> " ++ show retra
                    -- Here we don't check for valid moves - is it ok?
                    act <- choose [(attac, gotoPoint False pt h), (retra, return False)]
                    act

-- If there is some battle, go there
smellBlood :: Point -> MyGame Bool
smellBlood pt = do
  st <- get
  let mx   = stCrtASt st	-- we are limited by aStar searches
      hots = stHotSpots st
  if mx <= 0 || null hots
     then return False
     else do
        mth <- toNearest pt hots maxSmellPath
        case mth of
            Nothing          -> return False
            Just (ho, hpath) -> do
                let hplan = Plan { plPrio = Green, plTarget = ho,
                                   plPath = plp, plPLen = length plp,
                                   plWait = maxPlanWait }
                    plp = take stepsToBlood hpath
                    gp  = stPars st
                    gs  = stState st
                    u   = stUpper st
                    cnt = stOurCnt st
                    nhills = inRadius2 fst (homeRadius gp) u ho $ hills gs
                -- when the hotspot is near some hill, do not delete it, so more ants are comming
                when (null nhills && cnt < cntLastAttack) $
                     modify $ \s -> s { stHotSpots = delete ho hots }
                executePlan pt hplan

-- Go to some free food, in some radius
gotoFood :: Point -> MyGame Bool
gotoFood pt = do
  st <- get
  let frf = stFrFood st
  if S.null frf
     then return False
     else do
         let fo = S.toList frf
         -- take the nearest food in some radius
             u  = stUpper st
             gp = stPars st
             foods = takeWhile ((<= foodRadius gp) . snd) $ sortByDist id u pt fo
         takeFirst (gotoPoint True pt) $ map fst foods

-- When boring:
rest pt = do
    act <- choose [(1, maiRar pt), (3, explore pt), (7, moveRandom pt)]
    act

-- Fight section

moveToList :: Point -> [Point] -> MyGame Bool
moveToList pt as = do
    let gc = gravCenter as
    moveTo True pt gc

moveFromList :: Point -> [Point] -> MyGame Bool
moveFromList pt as = do
    let gc = gravCenter as
    moveTo False pt gc

-- The enemy ants we have around us
antsInZone :: Bool -> Point -> MyGame [Point]
antsInZone friends pt = do
    st <- get
    let u = stUpper st
        gs = stState st
        as = if friends then ours gs else map snd $ ants gs
        gp = stPars st
    return $! inRadius2 id (dangerRadius gp) u pt as

inHomeZone :: Point -> MyGame (Maybe Point)
inHomeZone pt = do
    st <- get
    let u = stUpper st
        gp = stPars st
        gs = stState st
        -- take my hills and sort them by distance
        hs = sortByDist id u pt $ map fst $ filter ((== 0) . snd) $ hills gs
    if null hs
       then return Nothing
       else do
          let (h, x) = head hs
          if x <= homeRadius gp
             then return $ Just h
             else return Nothing

-- Keep close to home
stayNearHome :: Point -> Point -> [PathInfo] -> MyGame Bool
stayNearHome pt h vs = if pt == h then moveRandom pt else moveTo True pt h

-- Move to or from a point if the direction not busy (else wait)
moveTo :: Bool -> Point -> Point -> MyGame Bool
moveTo towards pt to = do
    st <- get
    let u = stUpper st
        (d, n) = if towards then nextTo u pt to else nextAw u pt to
    b <- isBusy n
    if b then markWait pt
         else orderMove pt d "moveTo"

{--
-- If we are more: attack!
dangerAway :: Point -> [Point] -> [PathInfo] -> MyGame Bool
dangerAway pt as vs = do
    os <- antsInZone True pt
    case length os of
      1 -> dangerAlone pt as vs
      _ -> attackManyToMany pt os as

-- We are alone against many: run!
runAway :: Point -> [Point] -> MyGame Bool
runAway pt as = moveFromList pt $ take 3 as

attackIt = moveTo True

attackOne pt _ = moveRandom pt
--}

hillToRaze :: Point -> (GameParams -> Int) -> MyGame (Maybe (Point, Int))
hillToRaze pt rf = do
  st <- get
  let gs = stState st
      -- take the active enemy hills
      hi = peEnHills $ stPersist st
  if null hi
     then return Nothing
     else do
         -- take the nearest hill
         let u  = stUpper st
             (h, x) = head $ sortByDist id u pt hi
             gp = stPars st
         if x > rf gp
            then return Nothing	-- too far
            else return $ Just (h, x)

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

-- Movement section
takeFirst :: (Point -> MyGame Bool) -> [Point] -> MyGame Bool
takeFirst _ []     = return False
takeFirst f (p:ps) = do
    r <- f p
    if r then return r else takeFirst f ps

-- Go to a point if there is no water in between
gotoPoint :: Bool -> Point -> Point -> MyGame Bool
gotoPoint _ pt to | pt == to = return False
gotoPoint isFood pt to = do
  st <- get
  let w = water . stState $ st
      u = stUpper st
      mx = stCrtASt st
  if mx <= 0
     then return False
     else do
       mpath <- liftIO $ aStar (validDirs w u allDirs) (distance u to) pt (== to) Nothing
       modify $ \s -> s { stCrtASt = mx - 1 }
       case mpath of
         Nothing    -> return False
         Just path' -> do
           let path = reverse path'
               plan = Plan { plPrio = Green, plTarget = to, plPath = path,
                             plPLen = length path, plWait = maxPlanWait }
           -- when isFood $ modify $ \s -> s { stFrFood = S.delete to (stFrFood s) }
           executePlan pt plan

-- Given a bitmap of "busy" points, and a source point, find
-- the valid directions to move
validDirs :: BitMap -> Point -> [Dir] -> Point -> IO [PathInfo]
validDirs w u ds pt = notBitMap w $ map (\d -> (d, move u pt d)) ds

-- Given a point, give the neighbour points, where we could find food
-- We don't even check for water, as food will for sure not be there
foodPoints :: Point -> MyGame [Point]
foodPoints pt = do
    st <- get
    let u = stUpper st
    return $ map (\d -> move u pt d) allDirs

-- Gets the valid dirs to move (or stay), considering busy cells
-- and ants with less liberty grades (because they are
-- part of a fight zone)
getValidDirs :: Point -> MyGame (Bool, [PathInfo])
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

-- Take a random (but not bad) direction
moveRandom :: Point -> MyGame Bool
moveRandom pt = do
  vs <- gets stValDirs
  case vs of
    []  -> return False		-- should not come here
    [(d, _)] -> orderMove pt d "random"
    _   -> do
      cst <- gets stCanStay
      let low = if cst then 0 else 1
      r <- liftIO $ randomRIO (low, length vs)
      if r == 0
         then markWait pt	-- means: wait
         else orderMove pt (fst $ vs !! (r - 1)) "random"

maiRar :: Point -> MyGame Bool
maiRar pt = do
    os <- antsInZone True pt
    if null os
       then return False
       else moveFromList pt os

explore :: Point -> MyGame Bool
explore pt = do
  vs <- gets stValDirs
  case vs of
    []       -> return False		-- should not come here
    [(d, _)] -> orderMove pt d "explore"
    _        -> go vs
    where go [] = return False
          go ((d, n) : ds) = do
             se <- seenPoint n
             if se then go ds else orderMove pt d "explore"

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
    let (dp@(d, p) : path) = plPath plan
    w <- isWater p
    if w
       then return False
       else do
           b  <- isBusy p
           vs <- gets stValDirs
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
                  newPlan p plan { plPath = path, plPLen = plPLen plan - 1, plWait = maxPlanWait }
                  orderMove pt d "execPlan"

deleteTargets :: [Point] -> MyGame ()
deleteTargets foods = do
    st <- get
    let food   = stFrFood st
        food'  = foldr S.delete food foods
        pers   = stPersist st
        plans  = pePlMemo pers
        plans' = M.filter ((`elem` foods) . plTarget) plans
    put st { stFrFood = food', stPersist = pers { pePlMemo = plans' }}

-- Init bad/busy squares: just a copy of water
-- plus the food and the current own ants
initBusy :: GameState Persist -> IO BitMap
initBusy gs = do
    busy <- mapArray id (water gs)
    forM_ (ours gs ++ foodP gs) $ \p -> writeArray busy p True
    -- forM_ (foodP gs) $ \p -> writeArray busy p True
    return busy

updateSeen :: GameState Persist -> BitMap -> IO ()
updateSeen gs busy = forM_ (ours gs) $ \p -> writeArray busy p True

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

seenPoint = isBitMap (peSeen . stPersist)

filterBusy :: (a -> Point) -> [a] -> MyGame [a]
filterBusy f as = do
    st <- get
    let busy = stBusy st
    lift $ filterM (\a -> liftM not $ readArray busy (f a)) as

notBitMap :: BitMap -> [(a, Point)] -> IO [(a, Point)]
notBitMap w = filterM (liftM not . readArray w . snd)

debug :: String -> MyGame ()
-- debug s = liftIO $ hPutStrLn stderr s
debug _ = return ()
