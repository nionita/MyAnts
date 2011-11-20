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
         stOurCnt  :: Int,			-- total count of our ants
         stCrtASt  :: Int			-- current astar searches
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
data Plan = Plan { plPrio :: Prio, plTarget :: Point, plPath :: [PathInfo], plWait :: Int } deriving Show
type PlanMemo = M.Map Point Plan

-- Some constants and constant-like definitions:
msReserve = 200		-- reserve time for answer back (ms)
msDecrAst = 400		-- under this time we decrese the AStar seraches per turn
msIncrAst = 700		-- over this time we increse the AStar seraches per turn
maxMaxASt = 80		-- maximum AStar searches per turn
attMajority = 2		-- used when attacking many to many
maxPlanWait = 3		-- how long to wait in a plan when path is blocked
checkEasyFood = 10	-- how often to check for easy food?
zoneMax      = 9	-- max ants in a zone fight
viewRadius   = (1*) . viewradius2	-- visibility radius
foodRadius   = (1*) . const 100	-- in which we go to food
homeRadius   = (1*) . const 100	-- in which we consider to be at home
razeRadius   =        const 1900	-- in which we consider to raze enemy hills
-- dangerRadius = (2*) . attackradius2	-- in which we are in danger
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
                   stCrtASt = peMaxPASt npers, stFrFood = food gs -- `S.difference` tfood
               }
      zoneRadius2 = hellSteps (attackradius2 gp) 2
      fzs = fightZones (near zoneRadius2 (snd b)) (ours gs) (ants gs) []
  when (not $ null fzs) $ hPutStrLn stderr $ "Fight zones:\n" ++ show fzs
  -- (orders, finst) <- runState (makeOrders $ ours gs) initst
  (fzs', st1) <- runState (fightAnts fzs) st0	-- first the fighting ants
  -- let ofree = myFreeAnts (ours gs) fzs'
  let ofree = myFreeAnts (ours gs) fzs'
  stf <- execState (freeAnts ofree) st1	-- then the free ants
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
freeAnts :: [Point] -> MyGame ()
freeAnts [] = return ()
freeAnts points = do
  st <- get
  let gp = stPars  st
      gs = stState st
  tr <- lift $ timeRemaining gp gs
  when (tr > msReserve) $ do
      perAnt $ head points
      freeAnts $ tail points

-- Our ants not involved in any fight zone
myFreeAnts :: [Point] -> [Point] -> [Point]
-- myFreeAnts os osf = S.toList $ S.fromList os `S.difference` (S.fromList $ concatMap fst fzs)
myFreeAnts os osf = S.toList $ S.fromList os `S.difference` S.fromList osf

hellSteps :: Int -> Int -> Int
hellSteps ar x = ar + x*x + ceiling (2 * fromIntegral x * sqrt (fromIntegral ar))

-- Orders for the fighting ants
fightAnts fs
    | null fs'  = return []
    | otherwise = do
        st <- get
        let gp = stPars st
            u  = stUpper st
            ra1 = hellSteps (attackradius2 gp) 1
            nf  = near (attackradius2 gp) u
            nf1 = near ra1 u
        fss <- mapM (perFightZone nf nf1) fs'
        return $ concat $ fss ++ map fst fs''
    where (fs', fs'') = partition (\(ps, tm) -> length ps + points tm <= zoneMax) fs
          points tm = sum $ map length $ M.elems tm

perFightZone nf nf1 fz@(us, themm) = do
    st <- get
    ibusy <- liftIO $ do
             busy <- mapArray id (stBusy st)
             forM_ us $ \p -> writeArray busy p False
             unsafeFreeze busy
    let u  = stUpper st
        -- here are the parameter of the evaluation
        epar = EvalPars { pes = 10, opt = 10, reg = stOurCnt st, tgt = Nothing }
        (sco, cfs) = nextTurn nf nf1 (valDirs ibusy u) epar us themm
        oac = fst cfs
    debug $ "Fight zone: us = " ++ show us ++ ", them = " ++ show themm
    debug $ "Params: " ++ show epar ++ " score = " ++ show sco ++ "\nOur moves: " ++ show oac
    used <- mapM extOrderMove oac
    return $ catMaybes used
    where valDirs :: UArray Point Bool -> Point -> Point -> [(Dir, Point)]
          valDirs w u pt = filter (not . (w!) . snd) $ map (\d -> (d, move u pt d)) allDirs

extOrderMove :: (Point, EDir) -> MyGame (Maybe Point)
extOrderMove (pt, edir) = do
    case edir of
        Go d -> orderMove pt d "fight" >> return (Just pt)
        Stay -> markWait pt >> return (Just pt)
        Any  -> return Nothing

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
    getGoal pt svs

getGoal :: Point -> (Bool, [PathInfo]) -> MyGame Bool
getGoal pt (bst, vs) =
    -- blocked pt bst vs <|>
    oneChoice pt bst vs <|>
    immRaze pt vs <|>
    -- danger pt vs <|>
    pickFood pt vs <|>
    followPlan pt vs <|>
    razeAttac pt vs <|>
    gotoFood pt vs <|>
    rest pt vs

{--
-- If blocked, wait
blocked pt vs
    = if null vs
         then markWait pt
         else return False
--}

-- When we have only one choice, take it
oneChoice :: Point -> Bool -> [PathInfo] -> MyGame Bool
oneChoice pt bst vs =
    if bst
       then if null vs
               then markWait pt	-- we can only wait
               else return False
       else case vs of
                [(d, _)] -> orderMove pt d "oneChoice"	-- the only possibility
                _        -> return False

-- When we can raze some hill not defended: do it!
immRaze :: Point -> [PathInfo] -> MyGame Bool
immRaze pt _ = do
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

-- When we face other ants, we have to take care!
danger :: Point -> [PathInfo] -> MyGame Bool
danger pt vs = do
    as <- antsInZone False pt
    case length as of
      0 -> return False	-- no danger
      1 -> toOneAtHome  pt as vs <|> toOneAway pt as
      _ -> dangerAtHome pt as vs <|> dangerAway  pt as vs

-- If we stay near a food square: wait one turn to pick it
pickFood :: Point -> [PathInfo] -> MyGame Bool
pickFood pt vs = do
  food <- gets $ food . stState
  let foods = getFoods food $ map snd vs
  if null foods
     then return False
     else do
         mustMove <- isBusy pt
         if mustMove
            then return False
            else do
               deleteTargets foods
               replicatePlan pt

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
    mpath <- liftIO $ aStar (validDirs w u) (listDistance u pts) pt (`S.member` ptsset) (Just maxl)
    modify $ \s -> s { stCrtASt = stCrtASt s - 1 }
    case mpath of
        Nothing    -> return Nothing
        Just path' -> do
            let np = snd $ head path'
                path = reverse path'
            return $ Just (np, path)
    where listDistance u list p = minimum $ map (distance u p) list

-- If we have a plan: execute it
followPlan :: Point -> [PathInfo] -> MyGame Bool
followPlan pt vs = do
    mplan <- getOldPlan pt
    case mplan of
        Nothing   -> return False	-- no plan
        Just plan -> do
            let lpl = length (plPath plan)
            measy <- if lpl `mod` checkEasyFood == 0	-- do we have an easy food?
                        then easyFood pt lpl		-- check only now and then
                        else return Nothing
            case measy of
                Nothing          -> executePlan pt plan
                Just (fo, fpath) -> do
                    let lfo = length fpath
                        fplan = Plan { plPrio = Green, plTarget = fo, plPath = fpath, plWait = 0 }
                    act <- choose [(lfo, executePlan pt plan), (lpl, executePlan pt fplan)]
                    act

-- How to attack and raze an enemy hill
razeAttac :: Point -> [PathInfo] -> MyGame Bool
razeAttac pt vs = do
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
                    act <- choose [(attac, gotoPoint False pt h), (retra, return False)]
                    act

-- Go to some free food, in some radius
gotoFood :: Point -> [PathInfo] -> MyGame Bool
gotoFood pt vs = do
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
rest pt vs = do
    act <- choose [(3, maiRar pt), (2, explore pt vs), (1, moveRandom pt vs)]
    act

-- Fight section
-- When we fight to only one at home we have to be carefull
toOneAtHome :: Point -> [Point] -> [PathInfo] -> MyGame Bool
toOneAtHome _ [] _   = return False
toOneAtHome pt as vs = do
    hz <- inHomeZone pt
    case hz of
      Nothing -> return False	-- not at home
      Just h  -> do
          os <- antsInZone True pt
          case length os of
            1 -> stayNearHome pt h vs
            2 -> stayNearHome pt h vs
            _ -> attackManyToOne pt os $ head as

toOneAway :: Point -> [Point] -> MyGame Bool
toOneAway _ []  = return False
toOneAway pt as = do
    os <- antsInZone True pt
    case length os of
      1 -> return False	-- be what it be
      _ -> attackManyToOne pt os $ head as

-- When we are at least 2 to 1:
-- if we are the nearest: stay out of attack zone until at least one friend is at same distance
-- if we are the second or third nearest: go to enemy
-- if we are not one of the nearest 3, forget it
attackManyToOne :: Point -> [Point] -> Point -> MyGame Bool
attackManyToOne pt os en = do
    st <- get
    let u = stUpper st
        as = take 3 $ sortByDist id u en (pt : os)
    if length as == 2	-- can be only 2 or 3
       then do
           let [(fsp, fsx), (sep, sex)] = as
           if pt /= fsp || fsx == sex
              then gotoPoint False pt en
              else return False
       else do
           let [(fsp, fsx), (sep, sex), (thp, thx)] = as
           if pt `elem` [fsp, sep, thp]
              then if pt /= fsp || fsx == sex
                      then gotoPoint False pt en
                      else return False
              else return False

attackManyToMany :: Point -> [Point] -> [Point] -> MyGame Bool
attackManyToMany pt os as = do
    let diff = length os + 1 - length as
    if diff < attMajority
       then moveFromList pt as
       else if diff == attMajority
            then return False	-- or: moveRandom pt vs
            else moveToList pt as

moveToList :: Point -> [Point] -> MyGame Bool
moveToList pt as = do
    let gc = gravCenter as
    moveTo True pt gc

moveFromList :: Point -> [Point] -> MyGame Bool
moveFromList pt as = do
    let gc = gravCenter as
    moveTo False pt gc

-- It must have at least one point!
gravCenter :: [Point] -> Point
gravCenter ps = (x `div` c, y `div` c)
    where ((x, y), c) = foldl' f ((0, 0), 0) ps
          f ((x, y), c) (xc, yc) = ((x + xc, y + yc), c + 1)

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

dangerAtHome :: Point -> [Point] -> [PathInfo] -> MyGame Bool
dangerAtHome pt as vs = do
    hz <- inHomeZone pt
    case hz of
      Nothing -> return False
      Just h  -> do
          act <- choose [(1, stayNearHome pt h vs), (1, dangerAway pt as vs)]
          act

-- Keep close to home
stayNearHome :: Point -> Point -> [PathInfo] -> MyGame Bool
stayNearHome pt h vs = if pt == h then moveRandom pt vs else moveTo True pt h

-- Move to or from a point if the direction not busy (else wait)
moveTo :: Bool -> Point -> Point -> MyGame Bool
moveTo towards pt to = do
    st <- get
    let u = stUpper st
        (d, n) = if towards then nextTo u pt to else nextAw u pt to
    b <- isBusy n
    if b then markWait pt
         else orderMove pt d "moveTo"

-- If we are more: attack!
dangerAway :: Point -> [Point] -> [PathInfo] -> MyGame Bool
dangerAway pt as vs = do
    os <- antsInZone True pt
    case length os of
      1 -> dangerAlone pt as vs
      _ -> attackManyToMany pt os as

dangerAlone :: Point -> [Point] -> [PathInfo] -> MyGame Bool
dangerAlone pt as vs = do
    st <- get
    let u = stUpper st
        gp = stPars st
        gs = stState st
        as' = sortByDist id u pt as
        xs  = take 2 $ inRadius2 fst (kamikaRadius gp) u pt as'
    case length xs of
      0 -> runAway pt $ map fst as'
      1 -> attackIt pt (fst $ head xs)
      2 -> attackOne pt xs vs

-- We are alone against many: run!
runAway :: Point -> [Point] -> MyGame Bool
runAway pt as = moveFromList pt $ take 3 as

attackIt = moveTo True

attackOne pt _ = moveRandom pt

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
       mpath <- liftIO $ aStar (validDirs w u) (distance u to) pt (== to) Nothing
       modify $ \s -> s { stCrtASt = mx - 1 }
       case mpath of
         Nothing    -> return False
         Just path' -> do
           let path = reverse path'
               plan = Plan { plPrio = Green, plTarget = to, plPath = path, plWait = maxPlanWait }
           -- when isFood $ modify $ \s -> s { stFrFood = S.delete to (stFrFood s) }
           executePlan pt plan

-- Given a bitmap of "busy" points, and a source point, find
-- the valid directions to move
validDirs :: BitMap -> Point -> Point -> IO [PathInfo]
validDirs w u pt = notWater w $ map (\d -> (d, move u pt d)) allDirs

getValidDirs :: Point -> MyGame (Bool, [PathInfo])
getValidDirs pt = do
  st <- get
  let busy = stBusy st
      u = stUpper st
  bst <- liftIO $ readArray busy pt
  pi  <- liftIO $ validDirs busy u pt
  return (not bst, pi)

-- Take a random (but not bad) direction
moveRandom :: Point -> [PathInfo] -> MyGame Bool
moveRandom pt vs = do
  case vs of
    []  -> return False		-- should not come here
    [(d, _)] -> orderMove pt d "random"
    _   -> do
      mustMove <- isBusy pt
      let low = if mustMove then 1 else 0
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

explore :: Point -> [PathInfo] -> MyGame Bool
explore pt vs = do
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
    let ((d, p) : path) = plPath plan
    w <- isWater p
    if w
       then return False
       else do
           b <- isBusy p
           if b
              then do
                  mustMove <- isBusy pt
                  if mustMove
                     then return False
                     else do
                         act <- choose [
                             (1, return False),
                             (plWait plan - 1, 
                                 newPlan p plan { plWait = plWait plan - 1 } >> markWait pt)
                             ]
                         act
              else do
                  newPlan p plan { plPath = path, plWait = maxPlanWait }
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

seenPoint = isBitMap (peSeen . stPersist)

filterBusy :: (a -> Point) -> [a] -> MyGame [a]
filterBusy f as = do
    st <- get
    let busy = stBusy st
    lift $ filterM (\a -> liftM not $ readArray busy (f a)) as

notWater :: BitMap -> [(a, Point)] -> IO [(a, Point)]
notWater w = filterM (liftM not . readArray w . snd)

near r u a b = euclidSquare u a b <= r

debug :: String -> MyGame ()
debug s = liftIO $ hPutStrLn stderr s
-- debug _ = return ()
