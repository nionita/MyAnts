module Ants
  (
    -- Data structures
    Dir (..)
  , GameParams (..)
  , GameState (..)
  , Order (..)
  , BitMap
  , Food
  , Point

    -- Utility functions
  , timeRemaining
  , move
  , distance
  , sortByDist
  , inRadius2

    -- main function
  , game

  -- other

  , getFoods
  , allDirs
  , nextTo
  , nextAw
  , straightTo

  ) where

import Control.Applicative
import Control.Monad (forM_)
import Data.Array.IO
import qualified Data.ByteString.Char8 as B
import Data.Char (digitToInt, toUpper)
import Data.List (delete, sortBy, lookup)
import Data.Maybe (fromMaybe)
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
type BitMap = IOUArray Point Bool
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

data Dir = North | East | South | West deriving (Bounded, Eq, Enum)

allDirs = [North .. West]

instance Show Dir where
  show North = "N"
  show East  = "E"
  show South = "S"
  show West  = "W"

-- Representation of an order
data Order = Order
  { source :: Point
  , direction :: Dir
  } deriving (Show)

data GameState a = GameState
  { water  :: BitMap
  , waterP :: [Point]
  , ours   :: [Point]   -- our ants
  , ants   :: [Point]   -- other ants
  , foodP  :: [Point]
  , food   :: Food
  , hills  :: [Hill]
  , startTime :: UTCTime
  , userState :: Maybe a -- to keep user state
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

move :: Point -> Point -> Dir -> Point
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

addWater :: GameState a -> Point -> GameState a
addWater gs p = gs { waterP = p : waterP gs }

addFood :: GameState a -> Point -> GameState a
addFood gs p = gs { foodP = p : foodP gs }

addHill :: GameState a -> (Point, Int) -> GameState a
addHill gs h = gs { hills = nhills }
    where nhills = h : delete h (hills gs)

addAnt :: GameState a -> (Point, Int) -> GameState a
addAnt gs (p, i) = if i == 0
                      then gs { ours = p : ours gs }
                      else gs { ants = p : ants gs }

-- Currently we ignore the dead ants
addDead :: GameState a -> Point -> GameState a
addDead gs _ = gs

initialGameState :: GameParams -> IO (GameState a)
initialGameState gp = do
  time <- getCurrentTime
  w <- newArray ((0, 0), (rows gp - 1, cols gp - 1)) False
  let gs = GameState { water = w, waterP = [], ants = [], ours = [], food = S.empty,
                       foodP = [], hills = [], startTime = time, userState = Nothing }
  return gs

updateGameState :: GameParams -> GameState a -> B.ByteString -> Either B.ByteString (GameState a)
updateGameState _  gs s | B.null s = Right gs
updateGameState gp gs s
  | c == B.pack "w" = Right $ addWater gs $ toPoint ps
  | c == B.pack "f" = Right $ addFood  gs $ toPoint ps
  | c == B.pack "h" = Right $ addHill  gs $ toPoiPl ps
  | c == B.pack "a" = Right $ addAnt   gs $ toPoiPl ps
  | c == B.pack "d" = Right $ addDead  gs $ toPoint ps
  | otherwise = Left s -- wrong line
  where
    (c : ps) = B.words s
    toPoint :: [B.ByteString] -> Point
    toPoint = tuplify2 . map (read . B.unpack)
    toPoiPl :: [B.ByteString] -> (Point, Int)
    toPoiPl = tuplify3 . map (read . B.unpack)

-- Reads input from the engine and stores in game state
updateGame :: GameParams -> GameState a -> IO (GameState a)
updateGame gp gs = do
  line <- B.getLine
  process line
  where 
    process line
      -- | "turn" `isPrefixOf` line = do
      --     -- hPutStrLn stderr line
      --     updateGame gp gs 
      | B.pack "go" `B.isPrefixOf` line = prepState gs
      | otherwise              = case updateGameState gp gs line of
                                    Right gs' -> updateGame gp gs'
                                    Left  s   -> do
                                        B.hPutStrLn stderr $ B.pack "Ignore: " `B.append` line
                                        updateGame gp gs

-- Prepares the game state after collecting the new input
prepState :: GameState a -> IO (GameState a)
prepState gs = do
  forM_ (waterP gs) $ \i -> writeArray (water gs) i True
  let fo = S.fromList (foodP gs)
  time <- getCurrentTime
  return gs { waterP = [], food = fo, startTime = time }

-- timeRemaining :: GameParams -> GameState -> IO NominalDiffTime
timeRemaining :: GameParams -> GameState a -> IO Int
timeRemaining gp gs = do
  timeNow <- getCurrentTime
  let ms = turntime gp - round (1000 * (timeNow `diffUTCTime` startTime gs))
  return ms

gatherParamInput :: IO [B.ByteString]
gatherParamInput = gatherInput' []
  where
    gatherInput' :: [B.ByteString] -> IO [B.ByteString]
    gatherInput' xs = do
      line <- B.getLine
      if B.pack "ready" /= line
        then gatherInput' (line:xs)
        else return xs
  
createParams :: [(B.ByteString, B.ByteString)] -> GameParams
createParams s =
  let lookup' key = read $ B.unpack $ fromMaybe (B.pack "0") $ lookup key s
      lt  = lookup' $ B.pack "loadtime"
      tt  = lookup' $ B.pack "turntime"
      rs  = lookup' $ B.pack "rows"
      cs  = lookup' $ B.pack "cols"
      ts  = lookup' $ B.pack "turns"
      vr2 = lookup' $ B.pack "viewradius2"
      ar2 = lookup' $ B.pack "attackradius2"
      sr2 = lookup' $ B.pack "spawnradius2"
  in GameParams { loadtime      = lt
                , turntime      = tt
                , rows          = rs
                , cols          = cs
                , turns         = ts
                , viewradius2   = vr2
                , attackradius2 = ar2
                , spawnradius2  = sr2
                }

endGame :: IO ()
endGame = do
  hPutStrLn stderr "End of game reached"
  -- players <- getLine
  -- hPutStrLn stderr $ "Number of players: " ++ (words players !! 1)
  -- scores <- getLine
  -- hPutStrLn stderr $ "Final scores: " ++ unwords (tail $ words scores)
  -- TODO print 

gameLoop :: GameParams -> GameState a
         -> (GameParams -> GameState a -> IO ([Order], GameState a))
         -> IO ()
gameLoop gp gs doTurn = do
  line <- B.getLine
  gameLoop' line
  where
    gameLoop' line
      | B.pack "turn" `B.isPrefixOf` line = do 
          B.hPutStrLn stderr line
          gs1 <- updateGame gp gs
          (orders, gs2) <- doTurn gp gs1
          -- hPutStrLn stderr $ show orders
          mapM_ issueOrder orders
          finishTurn
          gameLoop gp gs2 doTurn
      | B.pack "end" `B.isPrefixOf` line = endGame
      | otherwise = do
          B.hPutStrLn stderr $ B.pack "Input: " `B.append` line
          gameLoop gp gs doTurn -- ignore line

game :: (GameParams -> GameState a -> IO ([Order], GameState a)) -> IO ()
game doTurn = do
  paramInput <- gatherParamInput
  let gp = createParams $ map (tuplify2 . B.words) paramInput
  hPutStrLn stderr $ "Params:\n" ++ show gp
  gs <- initialGameState gp
  finishTurn -- signal done with setup
  gameLoop gp gs doTurn

getFoods :: Food -> [Point] -> [Point]
getFoods food = filter (`S.member` food)

-- Which direction to take to a given point? And which neighbour is on the way?
nextTo :: Point -> Point -> Point -> (Dir, Point)
nextTo bound from to = fst . head $ sortByDist snd bound to
                                  $ map (\d -> (d, move bound from d)) allDirs

-- Which direction to take away from given point? And which neighbour is on the way?
nextAw :: Point -> Point -> Point -> (Dir, Point)
nextAw bound from to = fst . head $ sortRevByDist snd bound to
                                  $ map (\d -> (d, move bound from d)) allDirs

-- Find a straight way from one point to another
straightTo :: Point -> Point -> Point -> [(Dir, Point)]
straightTo bound from to
  | from == to = []
  | otherwise  = let dp = nextTo bound from to
                 in dp : straightTo bound (snd dp) to

-- Sort a list of <point+info> by distance to another point
sortByDist :: (a -> Point) -> Point -> Point -> [a] -> [(a, Int)]
sortByDist f bound from as = sortBy (comparing snd)
                                $ map (\a -> (a, distance bound from (f a))) as

-- Sort a list of <point+info> descending by distance to another point
sortRevByDist :: (a -> Point) -> Point -> Point -> [a] -> [(a, Int)]
sortRevByDist f bound from as = sortBy (comparing (negate . snd))
                                $ map (\a -> (a, distance bound from (f a))) as

-- Find <point+info> in a given radius (squared)
inRadius2 :: (a -> Point) -> Int -> Point -> Point -> [a] -> [a]
inRadius2 f r bound from as = filter ((<=r) . distance bound from . f) as

-- vim: set expandtab:
