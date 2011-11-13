{-# LANGUAGE RankNTypes #-}

module Brain (doTurn) where

import Control.Monad (filterM, when, forM_, liftM, liftM2, foldM)
import qualified Control.OldException as E
import Data.Array.Unboxed
import Data.Array.IO
import Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import System.IO
import System.Random

import StateT
import Ants
import AStar

-- Data structure for internal state
data MyState = MyState {
         stPars    :: GameParams,		-- game params
         stState   :: GameState Persist,	-- game state (extern)
         stPersist :: Persist,			-- persistent internal state
         stBusy    :: BitMap,			-- busy fields
         stUpper   :: Point,			-- upper bound of the world
         stOrders  :: [Order],			-- accumulates orders
         stPlans   :: [(Point, Plan)],		-- accumulates plans
         stOurCnt  :: Int,			-- total count of our ants
         stWeakEH  :: [(Point, (Int, Int))]	-- weakness of enemy hills
     }

data Persist = Persist {
         peSeen    :: BitMap,	-- fields where we were
         pePlMemo  :: PlanMemo,	-- our plans
         peEnHills :: [Point]	-- enemy hills (not razed by us)
     }

type MyGame a = forall r. CPS r MyState IO a

-- Plans we calculate and must remember: priority, target and path
data Prio = Green | Yellow | Red deriving (Eq, Ord, Show)
data Plan = Plan { plPrio :: Prio, plTarget :: Point, plPath :: [PathInfo] } deriving Show
type PlanMemo = M.Map Point Plan

-- Some constants and constant-like definitions:
msReserve = 200		-- reserve time for answer back (ms)
foodRadius   = (1*) . const 100	-- in which we go to food
homeRadius   = (1*) . const 100	-- in which we consider to be at home
razeRadius   = (2*) . const 100	-- in which we consider to raze enemy hills
-- dangerRadius = (2*) . attackradius2	-- in which we are in danger
dangerRadius = (1*) . attackradius2	-- in which we are in danger
kamikaRadius = (1*) . attackradius2	-- we try a one to one fight (as we die anyway)

attMajority = 2	-- used when attacking many to many

maxPLen = 40	-- maximum path length for AStar

doTurn :: GameParams -> GameState Persist -> IO ([Order], GameState Persist)
doTurn gp gs = do
  busy <- initBusy gs
  b <- getBounds $ water gs
  -- get the persistent information (between turns)
  npers <- case userState gs of
               Just pers -> return pers
               Nothing   -> do
                   nseen <- newArray b False
                   return $ Persist { peSeen = nseen, pePlMemo = M.empty, peEnHills = [] }
  updateSeen gs (peSeen npers)
  -- these are enemy hills we see this turn
  let hinow = map fst $ filter ((/= 0) . snd) $ hills gs
  -- take only the active ones (actually not razed by us)
  hi <- filterM (liftM not . readArray (peSeen npers)) $ nub $ hinow ++ peEnHills npers
  let attacs = map (hillAttacs (snd b) (razeRadius gp) (homeRadius gp) (ours gs) (ants gs)) hi
      initst = MyState {
                   stPars = gp, stState = gs, stBusy = busy,
                   stPersist = npers { peEnHills = hi },
                   stUpper = snd b, stOrders = [], stPlans = [],
                   stOurCnt = length (ours gs), stWeakEH = attacs
               }
  (orders, finst) <- runState (makeOrders $ ours gs) initst
  let plans = M.fromList $ stPlans finst
      fpers = (stPersist finst) { pePlMemo = plans }
  restTime <- timeRemaining gp gs
  -- hPutStrLn stderr $ "Orders: " ++ show (stOrders finst)
  -- hPutStrLn stderr $ "Plans:"
  -- mapM_ (hPutStrLn stderr . show) $ stPlans finst
  hPutStrLn stderr $ "Time remaining (ms): " ++ show restTime
  -- let gsf = (stState finst) { ants = [], ours = [], foodP = [], userState = stPersist  }
  let gsf = gs { ants = [], ours = [], foodP = [], userState = Just fpers }
  return (orders, gsf)

-- Attacs and defences of enemy hills: how many ants of us and of them are there?
hillAttacs :: Point -> Int -> Int -> [Point] -> [Point] -> Point -> (Point, (Int, Int))
hillAttacs bound rr hr os as h = (h, (us, them))
    where us   = length $ inRadius2 id rr bound h os
          them = length $ inRadius2 id hr bound h as

makeOrders :: [Point] -> MyGame [Order]
makeOrders [] = gets stOrders
makeOrders points = do
  st <- get
  let gp = stPars  st
      gs = stState st
  tr <- lift $ timeRemaining gp gs
  if tr <= msReserve
    then gets stOrders
    else do
      perAnt $ head points
      makeOrders $ tail points

-- Combine the strategies for the move generation
(<|>) :: MyGame Bool -> MyGame Bool -> MyGame Bool
m1 <|> m2 = m1 >>= \r -> if r then return r else m2

infixr 1 <|> 

perAnt :: Point -> MyGame Bool
perAnt pt = do
    vs <- getValidDirs pt
    getGoal pt vs

getGoal :: Point -> [PathInfo] -> MyGame Bool
getGoal pt vs =
    blocked vs
    <|> immRaze pt vs
    <|> danger pt vs
    <|> oneChoice pt vs
    <|> pickFood pt vs
    <|> followPlan pt vs
    <|> razeAttac pt vs
    <|> gotoFood pt vs
    <|> rest pt vs

-- If blocked, wait
blocked vs = return $ null vs

-- When we can raze some hill not defended: do it!
immRaze :: Point -> [PathInfo] -> MyGame Bool
immRaze pt _ = do
    mhr <- hillToRaze pt
    case mhr of
        Nothing     -> return False
        Just (h, x) -> do
            st <- get
            let bound = stUpper st
                as = ants $ stState st
            if null $ inRadius2 id x bound h as
               then gotoPoint pt h
               else return False

-- When we face other ants, we have to take care!
danger :: Point -> [PathInfo] -> MyGame Bool
danger pt vs = do
    as <- antsInZone False pt
    case length as of
      0 -> return False	-- no danger
      1 -> toOneAtHome  pt as vs <|> toOneAway pt as
      _ -> dangerAtHome pt as vs <|> dangerAway  pt as vs

-- When we have only one choice, take it
oneChoice :: Point -> [PathInfo] -> MyGame Bool
oneChoice pt vs =
    case vs of
        [(d, _)] -> orderMove pt d
        _        -> return False

-- If we stay near a food square: wait one turn to pick it
pickFood :: Point -> [PathInfo] -> MyGame Bool
pickFood pt vs = do
  food <- gets $ food . stState
  if anyFood food $ map snd vs
     then replicatePlan pt
     else return False

-- If we have a plan: execute it
followPlan :: Point -> [PathInfo] -> MyGame Bool
followPlan pt vs = do
    mplan <- getOldPlan pt
    case mplan of
        Nothing   -> return False	-- no plan
        Just plan -> executePlan pt plan

-- How to attack and raze an enemy hill
razeAttac :: Point -> [PathInfo] -> MyGame Bool
razeAttac pt vs = do
    mhr <- hillToRaze pt
    case mhr of
        Nothing     -> return False
        Just (h, x) -> do
            st <- get
            case lookup h (stWeakEH st) of
                Nothing         -> return False
                Just (us, them) -> do
                    let (attac, retra) = attacProbs us them (stOurCnt st)
                    act <- choose [(attac, gotoPoint pt h), (retra, return False)]
                    act

-- Go to some food, if easy reachable
gotoFood :: Point -> [PathInfo] -> MyGame Bool
gotoFood pt vs = do
  st <- get
  let gs = stState st
      fo = foodP gs
  if null fo
     then return False
     else do
         -- take the nearest food in some radius
         let u  = stUpper st
             gp = stPars st
             foods = takeWhile ((<= foodRadius gp) . snd) $ sortByDist id u pt fo
         takeFirst (gotoPoint pt) $ map fst foods

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
              then gotoPoint pt en
              else return True
       else do
           let [(fsp, fsx), (sep, sex), (thp, thx)] = as
           if pt `elem` [fsp, sep, thp]
              then if pt /= fsp || fsx == sex
                      then gotoPoint pt en
                      else return True
              else return False

attackManyToMany :: Point -> [Point] -> [Point] -> MyGame Bool
attackManyToMany pt os as = do
    let diff = length os + 1 - length as
    if diff < attMajority
       then moveFromList pt as
       else if diff == attMajority
            then return True	-- or: moveRandom pt vs
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
        as = if friends then ours gs else ants gs
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
    if b then return True
         else orderMove pt d

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

hillToRaze :: Point -> MyGame (Maybe (Point, Int))
hillToRaze pt = do
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
         if x > razeRadius gp
            then return Nothing	-- too far
            else return $ Just (h, x)

attacProbs :: Int -> Int -> Int -> (Int, Int)
attacProbs us them ours = (us * us * ours `div` afact, them * them * dfact `div` ours)
    where afact = 20
          dfact = 20

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
      Nothing   -> return True
      Just plan -> do
          newPlan pt plan
          return True

newPlan :: Point -> Plan -> MyGame ()
newPlan pt plan = modify $ \s -> s { stPlans = (pt, plan) : stPlans s }

-- Movement section
takeFirst :: (Point -> MyGame Bool) -> [Point] -> MyGame Bool
takeFirst _ []     = return False
takeFirst f (p:ps) = do
    r <- f p
    if r then return r else takeFirst f ps

-- Go to a point if there is no water in between
gotoPoint :: Point -> Point -> MyGame Bool
gotoPoint pt to | pt == to = return False
gotoPoint pt to = do
  st <- get
  let w = water . stState $ st
      u = stUpper st
  -- liftIO $ hPutStr stderr $ "Path from " ++ show pt ++ " to " ++ show to ++ ": "
  mpath <- liftIO $
      E.catch (aStar (validDirs w u) (distance u to) pt (== to) (Just maxPLen))
              (\e -> do
                  hPutStrLn stderr $ "Exception in aStar: " ++ show e
                  return Nothing
              )
  case mpath of
    Nothing    -> return False
    Just path' -> do
      let path = reverse path'
      -- liftIO $ hPutStrLn stderr $ show path
      let plan = Plan { plPrio = Green, plTarget = to, plPath = path }
      executePlan pt plan

-- Given a bitmap of "busy" points, and a source point, find
-- the valid directions to move
validDirs :: BitMap -> Point -> Point -> IO [PathInfo]
validDirs w u pt = notWater w $ map (\d -> (d, move u pt d)) allDirs

getValidDirs :: Point -> MyGame [PathInfo]
getValidDirs pt = do
  st <- get
  let busy = stBusy st
      u = stUpper st
  liftIO $ validDirs busy u pt

-- Take a random (but not bad) direction
moveRandom :: Point -> [PathInfo] -> MyGame Bool
moveRandom pt vs = do
  case vs of
    []  -> return False		-- should not come here
    [(d, _)] -> orderMove pt d
    _   -> do
      mustMove <- isBusy pt
      let low = if mustMove then 1 else 0
      r <- liftIO $ randomRIO (low, length vs)
      if r == 0
         then return True	-- means: wait
         else orderMove pt $ fst $ vs !! (r - 1)

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
    [(d, _)] -> orderMove pt d
    _        -> go vs
    where go [] = return False
          go ((d, n) : ds) = do
             se <- seenPoint n
             if se then go ds else orderMove pt d 

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

orderMove :: Point -> Dir -> MyGame Bool
orderMove p d = do
    st <- get
    let busy = stBusy st
        u = stUpper st
        mvo = Order { source = p, direction = d }
        i = move u p d
    liftIO $ writeArray busy i True
    debug $ "Order: " ++ show p ++ " -> " ++ show d ++ " (= " ++ show i ++ ")"
    put st { stOrders = mvo : stOrders st }
    return True

executePlan :: Point -> Plan -> MyGame Bool
executePlan pt plan | null (plPath plan) = return False
executePlan pt plan = do
    let ((d, p) : path) = plPath plan
    b <- isBusy p
    if b then return False else do	-- here: if it's not water, we should wait
       orderMove pt d
       newPlan p plan { plPath = path }
       return True

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

isBusy :: Point -> MyGame Bool
isBusy p = do
    busy <- gets stBusy
    lift $ readArray busy p

filterBusy :: (a -> Point) -> [a] -> MyGame [a]
filterBusy f as = do
    st <- get
    let busy = stBusy st
    lift $ filterM (\a -> liftM not $ readArray busy (f a)) as

someWater :: [Point] -> MyGame Bool
someWater ps = do
    w <- gets $ water . stState
    lift $ waterGo w ps

waterGo :: BitMap -> [Point] -> IO Bool
waterGo w [] = return False
waterGo w (a:as) = do
    b <- readArray w a
    if b
       then return b
       else waterGo w as

notWater :: BitMap -> [(a, Point)] -> IO [(a, Point)]
notWater w = filterM (liftM not . readArray w . snd)

seenPoint :: Point -> MyGame Bool
seenPoint p = do
    seen <- gets (peSeen . stPersist)
    lift $ readArray seen p

debug :: String -> MyGame ()
-- debug s = liftIO $ hPutStrLn stderr s
debug _ = return ()
