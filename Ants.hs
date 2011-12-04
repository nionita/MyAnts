{-# LANGUAGE BangPatterns #-}

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
  , sumPoint
  , distance
  , euclidSquare
  , sortByDist
  , inRadius2
  , gravCenter
  , gravVar

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
import Control.Monad (forM_, when)
import Data.Array.IO
import qualified Data.ByteString.Char8 as B
import Data.Char (digitToInt, toUpper)
import Data.List (delete, sortBy, lookup, foldl')
import Data.Maybe (fromMaybe, fromJust)
import qualified Data.Map as M
import Data.Ord (comparing)
import qualified Data.Set as S
import Data.Time.Clock
import System.IO
import System.Random (mkStdGen, setStdGen)
import System.Environment (getArgs)
import System.Mem (performGC)

-- type synonyms
type Point = (Int, Int)         -- (row, col)
type Hill  = (Point, Int)
type BitMap = IOUArray Point Bool
type Food  = S.Set Point

-- Wrap the coordinates
(%!%) :: Point -> Point -> Point
(%!%) (!pr, !pc) (!ur, !uc) = 
  let !modCol = 1 + uc
      !modRow = 1 + ur
      !ixCol  = pc `mod` modCol
      !ixRow  = pr `mod` modRow
  in (ixRow, ixCol)

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
  , logic :: String
  } deriving (Show)

data GameState a = GameState
  { water  :: BitMap
  , waterP :: [Point]
  , ours   :: [Point]   -- our ants
  , ants   :: [(Int, Point)]   -- other ants
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
  , seed :: Int
  } deriving (Show)

modDistance :: Int -> Int -> Int -> Int
modDistance n x y = min ((x - y) `mod` n) ((y - x) `mod` n)

euclidSquare :: Point  -- bound
             -> Point -> Point -> Int
euclidSquare (br, bc) (p1r, p1c) (p2r, p2c) =
  let rowd = modDistance (br + 1) p1r p2r
      cold = modDistance (bc + 1) p1c p2c
  in (rowd * rowd) + (cold * cold)

distance :: Point -> Point -> Point -> Int
distance (br, bc) (p1r, p1c) (p2r, p2c) =
  let rowDist = modDistance (br + 1) p1r p2r
      colDist = modDistance (bc + 1) p1c p2c
  in rowDist + colDist

move :: Point -> Point -> Dir -> Point
move u (rp, cp) dir
  | dir == North = let !rp1 = rp - 1 in (rp1, cp) %!% u
  | dir == South = let !rp1 = rp + 1 in (rp1, cp) %!% u
  | dir == West  = let !cp1 = cp - 1 in (rp, cp1) %!% u
  | otherwise    = let !cp1 = cp + 1 in (rp, cp1) %!% u

sumPoint :: Point -> Point -> Point -> Point
sumPoint bound (p1r, p1c) (p2r, p2c) = (p1r + p2r, p1c + p2c) %!% bound

issueOrder :: Order -> IO ()
issueOrder order = do
  let (pr, pc) = source order
      srow = show pr
      scol = show pc
      sdir = show . direction $ order
  putStrLn $ "o " ++ srow ++ " " ++ scol ++ " " ++ sdir

finishTurn :: GameParams -> [Order] -> IO ()
finishTurn gp ords = do
  putStrLn "go"
  hFlush stdout
  -- let dubs = collisions gp ords
  -- when (not $ null dubs) $ do
  --     hPutStrLn stderr "Dubs:"
  --     mapM_ (hPutStrLn stderr . show) dubs
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
addAnt gs a@(p, i) = if i == 0
                      then gs { ours = p : ours gs }
                      else gs { ants = (i, p) : ants gs }

-- Currently we ignore the dead ants
addDead :: GameState a -> Point -> GameState a
addDead gs _ = gs

initialGameState :: GameParams -> IO (GameState a)
initialGameState gp = do
  when (seed gp /= 0) $ do
    let gen = mkStdGen (seed gp)
    setStdGen gen
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
  line <- getLineOrEof
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
      line <- getLineOrEof
      if B.pack "ready" `B.isPrefixOf` line
        then return xs
        else gatherInput' (line:xs)
  
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
      see = lookup' $ B.pack "player_seed"
  in GameParams { loadtime      = lt
                , turntime      = tt
                , rows          = rs
                , cols          = cs
                , turns         = ts
                , viewradius2   = vr2
                , attackradius2 = ar2
                , spawnradius2  = sr2
                , seed          = see
                }

endGame :: IO ()
endGame = do
  hPutStrLn stderr "End of game reached"
  -- players <- getLine
  -- hPutStrLn stderr $ "Number of players: " ++ (words players !! 1)
  -- scores <- getLine
  -- hPutStrLn stderr $ "Final scores: " ++ unwords (tail $ words scores)
  -- TODO print 

gameLoop :: Maybe Int -> GameParams -> GameState a
         -> (GameParams -> GameState a -> IO ([Order], GameState a))
         -> IO ()
gameLoop mendt gp gs doTurn = do 
  line <- getLineOrEof
  gameLoop' line
  where
    gameLoop' line
      | B.pack "turn" `B.isPrefixOf` line = do 
          B.hPutStrLn stderr line
          let ws = B.words line
              tn = fst . fromJust $ B.readInt $ head $ tail ws
              run = do
                  gs1 <- updateGame gp gs
                  (orders, gs2) <- doTurn gp gs1
                  mapM_ issueOrder orders
                  finishTurn gp orders
                  gameLoop mendt gp gs2 doTurn
          case mendt of
            Just et -> if tn >= et then endGame else run
            Nothing -> run
      | B.pack "end" `B.isPrefixOf` line = endGame
      | otherwise = do
          B.hPutStrLn stderr $ B.pack "Input: " `B.append` line
          gameLoop mendt gp gs doTurn -- ignore line

getLineOrEof = do
  eof <- isEOF
  if eof then return (B.pack "end") else B.getLine
    -- do
    --   lin <- B.getLine
    --   B.hPutStrLn stderr lin
    --   return lin

game :: (GameParams -> GameState a -> IO ([Order], GameState a)) -> IO ()
game doTurn = do
  endt <- getEndTurn
  paramInput <- gatherParamInput
  let gp = createParams $ map (tuplify2 . B.words) paramInput
  hPutStrLn stderr $ "Params:\n" ++ show gp
  gs <- initialGameState gp
  finishTurn gp [] -- signal done with setup
  gameLoop endt gp gs doTurn

getEndTurn = do
  args <- getArgs
  case args of
    (a:_) -> return $ Just $ read a
    _     -> return Nothing

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
-- inRadius2 f r bound from as = filter ((<=r) . distance bound from . f) as
inRadius2 f r bound from as = filter ((<=r) . euclidSquare bound from . f) as

-- Gravity center
-- It must have at least one point!
gravCenter :: [Point] -> Point
gravCenter ps = (x `div` c, y `div` c)
    where ((x, y), c) = foldl' f ((0, 0), 0) ps
          f ((x, y), c) (xc, yc) = ((x + xc, y + yc), c + 1)

-- Variance
gravVar :: Point -> [Point] -> (Point, Point)
gravVar u ps = (gc, (dx `div` l, dy `div` l))
    where gc = gravCenter ps
          l  = length ps
          dx = sum $ map (modDistance (fst u) (fst gc) . fst) ps
          dy = sum $ map (modDistance (snd u) (snd gc) . snd) ps

collisions gp ords = filter fi $ M.assocs mp
    where u = (rows gp - 1, cols gp - 1)
          mp = foldr fo M.empty $ map (\ord -> (move u (source ord) (direction ord), [ord])) ords
          fo = uncurry (M.insertWith (++))
          fi (_, a:b:_) = True
          fi _          = False

-- vim: set expandtab:
