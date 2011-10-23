module Brain (doTurn) where

import Data.Array
import Data.List
import Data.Maybe (mapMaybe)
import Control.Monad.State
import System.IO
import System.Random

import Ants

doTurn :: GameParams -> GameState -> IO [Order]
doTurn gp gs = do
  -- generate orders for all ants belonging to me
  let initst = MyState { stPars = gp, stState = gs, stBusy = initBusy (world gs), stOrders = [] }
  orders <- evalStateT (makeOrders $ myAnts $ ants gs) initst
  elapsedTime <- timeRemaining gp gs
  hPutStrLn stderr $ show elapsedTime
  -- wrap list of orders back into a monad
  return orders

data MyState = MyState {
         stPars   :: GameParams,
         stState  :: GameState,
         stBusy   :: Busy,
         stOrders :: [Order]
     }

type MyGame = StateT MyState IO

-- Array of point wher we cannot move
type Busy = Array Point Bool

msReserve = 300 -- reserve time for answer back

makeOrders :: [Ant] -> MyGame [Order]
makeOrders [] = gets stOrders
makeOrders ants = do
  st <- get
  let gp = stPars  st
      gs = stState st
  tr <- lift $ timeRemaining gp gs
  if tr <= msReserve
    then gets stOrders
    else do
      perAnt $ head ants
      makeOrders $ tail ants

perAnt :: Ant -> MyGame ()
perAnt a = do
  st <- get
  let neigh = neighbours w $ point a
      avail = food . stState $ st
      w = world . stState $ st
  -- If we found food, take it (i.e. make a pause)
  if nearFood w neigh
     then return ()
     else do
       -- otherwise take one random from the acceptable ones
       let acc = filter ((acceptable w (stBusy st)) a) allDirs
       case acc of
         []  -> return ()
         [d] -> orderMove a d
         _   -> do
           r <- lift $ randomRIO (0, length acc - 1)
           let d = acc !! r
           orderMove a d

orderMove :: Ant -> Direction -> MyGame ()
orderMove a d = do
  w <- gets $ world . stState
  let mvo = Order { ant = a, direction = d }
  modify $ \s -> s { stBusy = actBusy w (stBusy s) a d, stOrders = mvo : stOrders s }

initBusy :: World -> Busy
initBusy w = array (bounds w) $ map f $ assocs w
  -- where f (i, mt) = (i, not $ tile mt `elem` [Dead, Water, Unknown])
  where f (i, mt) = (i, not $ isLand mt)

actBusy :: World -> Busy -> Ant -> Direction -> Busy
actBusy w b a d = b // [(i, True)]
  where i = move w (point a) d

acceptable :: World -> Busy -> Ant -> Direction -> Bool
acceptable w busy a d = not $ busy ! i
  where i = move w (point a) d
