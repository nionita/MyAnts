{-# LANGUAGE RankNTypes #-}

module Brain (doTurn) where

import Control.Monad (filterM, when)
import Data.Array.Unboxed
import Data.Array.IO
import Data.List
-- import qualified Data.Map as M
import Data.Maybe (fromJust)
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

msReserve = 300 -- reserve time for answer back

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
perAnt pt = pickFood pt <|> gotoFood pt <|> moveRandom pt

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
             (to, x) = head $ sortByDist u pt fo
             gp = stPars st
         -- if it's not visible don't care
         if x > viewradius2 gp
            then return False
            else do
              -- am I the nearest ant to it?
              let (fr, _) = head $ sortByDist u to (ours gs)
              if fr /= pt
                 then return False
                 else do
                   let nx = nextTo u pt to
                   lift $ hPutStrLn stderr
                        $ "Ant " ++ show pt ++ " to food " ++ show to ++ " thru " ++ show nx
                   b <- isBusy nx
                   when b $ lift $ hPutStrLn stderr $ "...but " ++ show nx ++ " is busy!"
                   if b then return False
                        else orderMove pt (fromJust $ dirTo u pt nx)

-- Take a random (but not bad) direction
moveRandom :: Point -> MyGame Bool
moveRandom pt = do
  acc <- filterM (acceptableDirs pt) allDirs
  case acc of
    []  -> return False
    [d] -> orderMove pt d
    _   -> do
      r <- liftIO $ randomRIO (0, length acc - 1)
      let d = acc !! r
      orderMove pt d

orderMove :: Point -> Direction -> MyGame Bool
orderMove p d = do
    st <- get
    let busy = stBusy st
        u = stUpper st
        mvo = Order { source = p, direction = d }
        i = move u p d
    liftIO $ writeArray busy i True
    put st { stOrders = mvo : stOrders st }
    return True

-- Init bad/busy squares: just a copy of water
initBusy :: GameState -> IO Busy
initBusy gs = mapArray id (water gs)

isBusy :: Point -> MyGame Bool
isBusy p = do
    st <- get
    let busy = stBusy st
    lift $ readArray busy p

acceptableDirs :: Point -> Direction -> MyGame Bool
acceptableDirs p d = do
    st <- get
    let u = stUpper st
        i = move u p d
    b <- isBusy i
    return $! not b
