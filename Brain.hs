{-# LANGUAGE RankNTypes #-}

module Brain (doTurn) where

import Control.Monad (filterM, when, forM_, liftM, liftM2, foldM)
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

attMajority = 2	-- used when attacking many to many

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
        -- <|> gotoHill pt
        <|> gotoFood pt
        -- <|> toLuft pt
        <|> rest pt

rest pt = do
    act <- choose [(1, maiRar pt), (2, moveRandom pt)]
    act

-- When we fight to only one at home we have to be carefull
toOneAtHome :: Point -> [Point] -> MyGame Bool
toOneAtHome pt as = do
    hz <- inHomeZone pt
    case hz of
      Nothing -> return False	-- not at home
      Just h  -> do
          os <- antsInZone True pt
          case length os of
            1 -> stayNearHome pt h
            2 -> stayNearHome pt h
            _ -> attackManyToOne pt os $ head as

toOneAway :: Point -> [Point] -> MyGame Bool
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
            then moveRandom pt	-- or: wait a bit?
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

-- When we face other ants, we have to take care!
danger :: Point -> MyGame Bool
danger pt = do
    as <- antsInZone False pt
    case length as of
      0 -> return False	-- no danger
      1 -> toOneAtHome  pt as <|> toOneAway pt as
      _ -> dangerAtHome pt as <|> dangerAway  pt as

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
        (h, x) = head $ sortByDist id u pt $ map fst $ filter ((== 0) . snd) $ hills gs
    if x <= homeRadius gp
       then return $ Just h
       else return Nothing

dangerAtHome :: Point -> [Point] -> MyGame Bool
dangerAtHome pt as = do
    hz <- inHomeZone pt
    case hz of
      Nothing -> return False
      Just h  -> stayNearHome pt h

-- Keep close to home
stayNearHome :: Point -> Point -> MyGame Bool
stayNearHome pt h = if pt == h then moveRandom pt else moveTo True pt h

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
dangerAway :: Point -> [Point] -> MyGame Bool
dangerAway pt as = do
    os <- antsInZone True pt
    case length os of
      1 -> dangerAlone pt as
      _ -> attackManyToMany pt os as

dangerAlone :: Point -> [Point] -> MyGame Bool
dangerAlone pt as = do
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

attackIt = moveTo True

attackOne _ _ = return True

-- When we can raze something: do it!
raze :: Point -> MyGame Bool
raze pt = do
  st <- get
  let gs = stState st
      -- take the enemy hills
      hi = map fst $ filter ((/= 0) . snd) $ hills gs
  if null hi
     then return False
     else do
         -- take the nearest hill
         let u  = stUpper st
             (h, x) = head $ sortByDist id u pt hi
             gp = stPars st
         if x > homeRadius gp
            then return False	-- too far
            else gotoPoint pt h

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
         -- take the nearest food in some radius
         let u  = stUpper st
{--
             (to, x) = head $ sortByDist id u pt fo
             gp = stPars st
         -- if it's not visible don't care
         if x > foodRadius gp
            then return False
            else gotoPoint pt to
--}
             gp = stPars st
             foods = takeWhile ((<= foodRadius gp) . snd) $ sortByDist id u pt fo
         takeFirst (gotoPoint pt) $ map fst foods
         -- return False

takeFirst :: (Point -> MyGame Bool) -> [Point] -> MyGame Bool
takeFirst _ []     = return False
takeFirst f (p:ps) = do
    r <- f p
    if r then return r else takeFirst f ps

-- Go to a point if there is no water in between
gotoPoint :: Point -> Point -> MyGame Bool
gotoPoint pt to = do
  u <- gets stUpper
  -- can we go straight to it?
  let path = straightTo u pt to
  wat <- someWater $ map snd path
  if wat
     then return False	-- here we can do some variation - later
     else do
       let (d, nx) = head path
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

maiRar :: Point -> MyGame Bool
maiRar pt = do
    os <- antsInZone True pt
    if null os
       then return False
       else moveFromList pt os

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

acceptableDirs :: Point -> Dir -> MyGame Bool
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
