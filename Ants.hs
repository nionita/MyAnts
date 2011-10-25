module Ants
  (
    -- Data structures
    Direction (..)
  , GameParams (..)
  , GameState (..)
  , Order (..)
  , Water
  , Point

    -- Utility functions
  , distance
  , timeRemaining
  , move
  , sortByDist

    -- main function
  , game

  -- TODO implement the following functions according to the starter pack guide
  --, direction

  , nearFood
  , allDirs
  , nextTo
  , dirTo

  ) where

import Control.Applicative
import Control.Monad (forM_)
import Data.Array.IO
import Data.Char (digitToInt, toUpper)
import Data.List (isPrefixOf, delete, sortBy, lookup)
import Data.Maybe (fromJust, fromMaybe)
import Data.Ord (comparing)
import qualified Data.Set as S
import Data.Time.Clock
import System.IO
import System.Mem (performGC)

-- type synonyms
type Row = Int
type Col = Int
type Point = (Row, Col)
type Hill  = (Point, Int)
type Water = IOUArray Point Bool
type Food  = S.Set Point

-- Wrap the coordinates
(%!%) :: Point -> Point -> Point
(%!%) u p = 
  let modCol = 1 + col u
      modRow = 1 + row u
      ixCol  = col p `mod` modCol
      ixRow  = row p `mod` modRow
  in (ixRow, ixCol)

row :: Point -> Row
row = fst

col :: Point -> Col
col = snd

data Direction = North | East | South | West deriving (Bounded, Eq, Enum)

allDirs = [North .. West]

instance Show Direction where
  show North = "N"
  show East  = "E"
  show South = "S"
  show West  = "W"

-- Representation of an order
data Order = Order
  { source :: Point
  , direction :: Direction
  } deriving (Show)

data GameState = GameState
  { water  :: Water
  , waterP :: [Point]
  , ants   :: [Point]
  , ours   :: [Point]
  , foodP  :: [Point]
  , food   :: Food
  , hills  :: [Hill]
  , startTime :: UTCTime
  }

data GameParams = GameParams
  { loadtime :: Int
  , turntime :: Int
  , rows :: Int
  , cols :: Int
  , turns :: Int
  , viewradius2 :: Int
  , attackradius2 :: Int
  , spawnradius2 :: Int
  , viewPoints :: [Point]
  } deriving (Show)

modDistance :: Int -> Int -> Int -> Int
modDistance n x y = min ((x - y) `mod` n) ((y - x) `mod` n)

manhattan :: Point -- bound
          -> Point -> Point -> Int
manhattan bound p1 p2 = 
  let rowd = modDistance (row bound + 1) (row p1) (row p2)
      cold = modDistance (col bound + 1) (col p1) (col p2)
  in rowd + cold

oneNorm :: Point -> Int
oneNorm p = row p + col p

twoNormSquared :: Point -> Int
twoNormSquared p = row p ^ 2 + col p ^ 2

euclidSquare :: Point  -- bound
             -> Point -> Point -> Int
euclidSquare bound p1 p2 = 
  let rowd = modDistance (row bound + 1) (row p1) (row p2)
      cold = modDistance (col bound + 1) (col p1) (col p2)
  in (rowd ^ 2) + (cold ^ 2)

distance :: Point -> Point -> Point -> Int
distance bound l1 l2 =
  let maxRow = row bound
      maxCol = col bound
      rowDist = modDistance maxRow (row l1) (row l2)
      colDist = modDistance maxCol (col l1) (col l2)
  in rowDist + colDist

move :: Point -> Point -> Direction -> Point
move u p dir
  | dir == North = u %!% (row p - 1, col p)
  | dir == South = u %!% (row p + 1, col p)
  | dir == West  = u %!% (row p, col p - 1)
  | otherwise    = u %!% (row p, col p + 1)

issueOrder :: Order -> IO ()
issueOrder order = do
  let p = source order
      srow = show . row $ p
      scol = show . col $ p
      sdir = show . direction $ order
  putStrLn $ "o " ++ srow ++ " " ++ scol ++ " " ++ sdir

finishTurn :: IO ()
finishTurn = do
  putStrLn "go"
  hFlush stdout
  performGC

tuplify2 :: [a] -> (a, a)
tuplify2 (x:y:_) = (x, y)

tuplify3 :: [Int] -> ((Int, Int), Int)
tuplify3 (x:y:z:_) = ((x, y), z)

addWater :: GameState -> Point -> GameState
addWater gs p = gs { waterP = p : waterP gs }

addFood :: GameState -> Point -> GameState
addFood gs p = gs { foodP = p : foodP gs }

addHill :: GameState -> (Point, Int) -> GameState
addHill gs h = gs { hills = nhills }
    where nhills = h : delete h (hills gs)

addAnt :: GameState -> (Point, Int) -> GameState
addAnt gs (p, i) = gs { ants = p : ants gs, ours = os }
    where os = if i == 0 then p : ours gs else ours gs

-- Currently we ignore the dead ants
addDead :: GameState -> Point -> GameState
addDead gs _ = gs

initialGameState :: GameParams -> IO GameState
initialGameState gp = do
  time <- getCurrentTime
  w <- newArray ((0, 0), (rows gp - 1, cols gp - 1)) False
  let gs = GameState { water = w, waterP = [], ants = [], ours = [],
                       food = S.empty, foodP = [], hills = [], startTime = time }
  return gs

updateGameState :: GameParams -> GameState -> String -> GameState
updateGameState _  gs [] = gs
updateGameState gp gs s
  | c == "w" = addWater gs $ toPoint ps
  | c == "f" = addFood  gs $ toPoint ps
  | c == "h" = addHill  gs $ toPoiPl ps
  | c == "a" = addAnt   gs $ toPoiPl ps
  | c == "d" = addDead  gs $ toPoint ps
  | otherwise = gs -- ignore line
  where
    (c : ps) = words s
    toPoint :: [String] -> Point
    toPoint = tuplify2 . map read
    toPoiPl :: [String] -> (Point, Int)
    toPoiPl = tuplify3 . map read

-- Reads input from the engine and stores in game state
updateGame :: GameParams -> GameState -> IO GameState
updateGame gp gs = do
  line <- getLine
  process line
  where 
    process line
      -- | "turn" `isPrefixOf` line = do
      --     -- hPutStrLn stderr line
      --     updateGame gp gs 
      | "go" `isPrefixOf` line = prepState gs
      | otherwise              = updateGame gp $ updateGameState gp gs line

-- Prepares the game state after collecting the new input
prepState :: GameState -> IO GameState
prepState gs = do
  forM_ (waterP gs) $ \i -> writeArray (water gs) i True
  let fo = S.fromList (foodP gs)
  time <- getCurrentTime
  return gs { waterP = [], food = fo, startTime = time }

-- timeRemaining :: GameParams -> GameState -> IO NominalDiffTime
timeRemaining :: GameParams -> GameState -> IO Int
timeRemaining gp gs = do
  timeNow <- getCurrentTime
  let ms = turntime gp - round (1000 * (timeNow `diffUTCTime` startTime gs))
  return ms

gatherParamInput :: IO [String]
gatherParamInput = gatherInput' []
  where
    gatherInput' :: [String] -> IO [String]
    gatherInput' xs = do
      line <- getLine
      if "ready" /= line
        then gatherInput' (line:xs)
        else return xs
  
createParams :: [(String, String)] -> GameParams
createParams s =
  -- let lookup' key = read $ fromJust $ lookup key s
  let lookup' key = read $ fromMaybe "0" $ lookup key s
      lt  = lookup' "loadtime"
      tt  = lookup' "turntime"
      rs  = lookup' "rows"
      cs  = lookup' "cols"
      ts  = lookup' "turns"
      vr2 = lookup' "viewradius2"
      ar2 = lookup' "attackradius2"
      sr2 = lookup' "spawnradius2"
      mx  = truncate $ sqrt $ fromIntegral vr2
      vp' = (,) <$> [-mx..mx] <*> [-mx..mx]
      vp  = filter (\p -> twoNormSquared p <= vr2) vp'
  in GameParams { loadtime      = lt
                , turntime      = tt
                , rows          = rs
                , cols          = cs
                , turns         = ts
                , viewradius2   = vr2
                , attackradius2 = ar2
                , spawnradius2  = sr2
                , viewPoints    = vp
                }

endGame :: IO ()
endGame = do
  players <- getLine
  hPutStrLn stderr $ "Number of players: " ++ (words players !! 1)
  scores <- getLine
  hPutStrLn stderr $ "Final scores: " ++ unwords (tail $ words scores)
  -- TODO print 

gameLoop :: GameParams -> GameState
         -> (GameParams -> GameState -> IO ([Order], GameState))
         -> IO ()
gameLoop gp gs doTurn = do
  line <- getLine
  gameLoop' line
  where
    gameLoop' line
      | "turn" `isPrefixOf` line = do 
          hPutStrLn stderr line
          gs1 <- updateGame gp gs
          (orders, gs2) <- doTurn gp gs1
          -- hPutStrLn stderr $ show orders
          mapM_ issueOrder orders
          finishTurn
          gameLoop gp gs2 doTurn
      | "end" `isPrefixOf` line = endGame
      | otherwise = gameLoop gp gs doTurn -- ignore line

game :: (GameParams -> GameState -> IO ([Order], GameState)) -> IO ()
game doTurn = do
  paramInput <- gatherParamInput
  let gp = createParams $ map (tuplify2 . words) paramInput
  hPutStrLn stderr $ "Params:\n" ++ show gp
  gs <- initialGameState gp
  finishTurn -- signal done with setup
  gameLoop gp gs doTurn

nearFood :: Point -> Food -> Point -> Bool
nearFood bound food p = any (flip S.member food . move bound p) allDirs

nextTo :: Point -> Point -> Point -> Point
nextTo bound from to = fst . head $ sortByDist bound to $ map (move bound from) allDirs

-- Give a point and one of its neighbour points, get the direction to take to it
-- (if possible)
dirTo :: Point -> Point -> Point -> Maybe Direction
dirTo bound from to = lookup to $ map (\d -> (move bound from d, d)) allDirs

sortByDist :: Point -> Point -> [Point] -> [(Point, Int)]
sortByDist bound from tos = sortBy (comparing snd)
                                $ map (\to -> (to, distance bound from to)) tos

-- vim: set expandtab:
