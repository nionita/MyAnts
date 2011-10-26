{-# LANGUAGE RankNTypes #-}

module Brain (doTurn) where

import Control.Monad (filterM, when, forM_, liftM)
import Data.Array.Unboxed
import Data.Array.IO
import Data.List
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import System.IO
import System.Random

import StateT
import Ants

data MyState = MyState {
         stPars   :: GameParams,
         stState  :: GameState,
         stBusy   :: Busy,
         stUpper  :: Point,
         stOrders :: [Order]
     }

type MyGame a = forall r. CPS r MyState IO a

-- Points where we cannot move
type Busy = IOUArray Point Bool

-- Some constants and constant-like definitions:
msReserve = 200		-- reserve time for answer back (ms)
foodRadius   = (1*) . const 100	-- in which we go to food
homeRadius   = (1*) . const 100	-- in which we consider to be at home
dangerRadius = (2*) . attackradius2	-- in which we are in danger
kamikaRadius = (1*) . attackradius2	-- we try a one to one fight (as we die anyway)

doTurn :: GameParams -> GameState -> IO ([Order], GameState)
doTurn gp gs = do
  busy <- initBusy gs
  b <- getBounds $ water gs
  let initst = MyState { stPars = gp, stState = gs, stBusy = busy,
                         stUpper = snd b, stOrders = [] }
  (orders, finst) <- runState (makeOrders $ ours gs) initst
  restTime <- timeRemaining gp gs
  hPutStrLn stderr $ "Time remaining (ms): " ++ show restTime
  let gsf = (stState finst) { ants = [], ours = [], foodP = [] }
  return (orders, gsf)

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
perAnt pt = danger pt
        <|> raze pt
        <|> pickFood pt
        <|> gotoFood pt
        -- <|> toLuft pt
        <|> moveRandom pt

oneToOneAtHome = dangerAtHome

oneToOneAway _ _ = return True	-- just wait to see what happens

-- When we face other ants, we have to take care!
danger :: Point -> MyGame Bool
danger pt = do
    as <- antsInZone pt
    case length as of
      0 -> return False	-- no danger
      1 -> oneToOneAtHome pt as <|> oneToOneAway pt as
      _ -> dangerAtHome   pt as <|> dangerAway  pt as

-- The enemy ants we have around us
antsInZone :: Point -> MyGame [Point]
antsInZone pt = do
    st <- get
    let u = stUpper st
        as = ants $ stState st
        gp = stPars st
    return $! inRadius2 id (dangerRadius gp) u pt as

inHomeZone :: Point -> MyGame (Maybe Point)
inHomeZone pt = do
    st <- get
    let u = stUpper st
        gp = stPars st
        gs = stState st
        -- take my hills and sort them by distance
        (h, x) = head $ sortByDist id u pt $ map fst $ filter ((== 0) . snd) $ hills gs
    if x <= homeRadius gp
       then return $ Just h
       else return Nothing

dangerAtHome :: Point -> [Point] -> MyGame Bool
dangerAtHome pt as = do
    hz <- inHomeZone pt
    case hz of
      Nothing -> return False
      Just h  -> if pt == h
         then moveRandom pt	-- we stay on the hill: go away
         else moveTo pt h	-- we get closer to home

moveTo :: Point -> Point -> MyGame Bool
moveTo pt to = do
    st <- get
    let u = stUpper st
        (d, n) = nextTo u pt to
    b <- isBusy n
    if b then return True
         else orderMove pt d

dangerAway :: Point -> [Point] -> MyGame Bool
dangerAway pt as = do	-- try to run away
    st <- get
    let u = stUpper st
        gp = stPars st
        gs = stState st
        as' = sortByDist id u pt as
        xs  = take 2 $ inRadius2 fst (kamikaRadius gp) u pt as'
    case length xs of
      0 -> runAway pt as'
      1 -> attackIt pt (fst $ head xs)
      2 -> attackOne pt xs

runAway pt as = moveRandom pt 	-- return True

attackIt = moveTo

attackOne _ _ = return True

-- When we can raze something: do it!
raze :: Point -> MyGame Bool
raze pt = return False

-- If we stay near a food square: wait one turn to pick it
pickFood :: Point -> MyGame Bool
pickFood pt = do
  st <- get
  b <- lift $ getBounds (stBusy st)
  if nearFood (snd b) (food . stState $ st) pt then return True else return False

-- Go to some food, if easy reachable
gotoFood :: Point -> MyGame Bool
gotoFood pt = do
  st <- get
  let gs = stState st
      fo = foodP gs
  if null fo
     then return False
     else do
         -- take the nearest food
         let u  = stUpper st
             (to, x) = head $ sortByDist id u pt fo
             gp = stPars st
         -- if it's not visible don't care
         if x > foodRadius gp
            then return False
            else do
              -- can we go straight to it?
              let path = straightTo u pt to
              wat <- someWater path
              if wat
                 then return False
                 else do
                   let (d, nx) = nextTo u pt to
                   b <- isBusy nx
                   if b then return False
                        else orderMove pt d

-- Take a random (but not bad) direction
moveRandom :: Point -> MyGame Bool
moveRandom pt = do
  acc <- filterM (acceptableDirs pt) allDirs
  case acc of
    []  -> return False
    [d] -> orderMove pt d
    _   -> do
      r <- liftIO $ randomRIO (0, length acc)
      if r == 0
         then return True	-- means: wait
         else do
             let d = acc !! (r - 1)
             orderMove pt d

-- Here we try to move away from too many friends
-- But currently it does not work well
toLuft :: Point -> MyGame Bool
toLuft pt = do
    st <- get
    let u = stUpper st
        us = ours $ stState st
        gp = stPars st
    dps <- filterBusy snd $ map (\d -> (d, move u pt d)) allDirs
    debug $ "toLuft dps: " ++ show dps
    case dps of
      []  -> return True		-- we can only wait
      [a] -> do
        debug $ "only one"
        act <- choose [(1, orderMove pt (fst a)), (1, return True)]	-- only one move or wait
        act
      _   -> do		-- 2 to 4 moves possible: take the better one
        let dpops = map (\(d, n) -> (d, length $ inRadius2 id (homeRadius gp) u n us)) dps
            -- sdpops = sortBy (comparing snd) dpops
            mx = maximum $ map snd dpops
            alters = (1, return True)
                        : filter ((>0) . fst) (map (\(d, l) -> (mx - l, orderMove pt d)) dpops)
        debug $ "toLuft dpops: " ++ show dpops
        act <- choose alters
        act
{--
            best  = head sdpops
            secb  = head $ tail sdpops
        if snd best == 0
           then return False	-- we are free
           else if snd secb > snd best
                   then orderMove pt (fst best)	-- we take the best
                   else return False		-- will go random
--}

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

orderMove :: Point -> Direction -> MyGame Bool
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

-- Init bad/busy squares: just a copy of water
initBusy :: GameState -> IO Busy
initBusy gs = do
    busy <- mapArray id (water gs)
    forM_ (ours gs ++ foodP gs) $ \p -> writeArray busy p True
    return busy

isBusy :: Point -> MyGame Bool
isBusy p = do
    st <- get
    let busy = stBusy st
    lift $ readArray busy p

filterBusy :: (a -> Point) -> [a] -> MyGame [a]
filterBusy f as = do
    st <- get
    let busy = stBusy st
    lift $ filterM (\a -> liftM not $ readArray busy (f a)) as

acceptableDirs :: Point -> Direction -> MyGame Bool
acceptableDirs p d = do
    st <- get
    let u = stUpper st
        i = move u p d
    b <- isBusy i
    return $! not b

someWater :: [Point] -> MyGame Bool
someWater ps = do
    w <- gets $ water . stState
    lift $ waterGo w ps

waterGo :: Water -> [Point] -> IO Bool
waterGo w [] = return False
waterGo w (a:as) = do
    b <- readArray w a
    if b
       then return b
       else waterGo w as

debug :: String -> MyGame ()
debug s = liftIO $ hPutStrLn stderr s
