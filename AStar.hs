{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}

module AStar (
    PathInfo(..), JPInfo(..),
    aStar
    ) where

import Data.Functor ((<$>))
import Data.List (delete, foldl')
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromJust)
import Ants

-- This class is the interface for the open collection
-- and has to be implemented by some real collection (map, list, whatever)
class OpenClass op where
    opIsEmpty   :: op -> Bool			-- is the collection empty?
    opSingleton :: Point -> OpInfo -> op	-- create a singleton collection
    opRemoveMin :: op -> ((Point, OpInfo), op)	-- retrieve & remove one with the smallest f value
    opRetrieve  :: Point -> op -> Maybe OpInfo	-- retrieve by key (point)
    opInsert    :: Point -> OpInfo -> op -> op	-- insert (or replace) point

data JPInfo = JPInfo {
                  jpDir   :: !Dir,			-- direction from parent to this point
                  jpCost  :: {-# UNPACK #-} !Int	-- the cost (steps) from parent to this point
              }
data OpInfo = OpInfo {
                  oiG     :: {-# UNPACK #-} !Int,	-- the current cost
                  oiF     :: {-# UNPACK #-} !Int,	-- the total cost (estimated)
                  oiPath  :: ![PathInfo],	-- the path so far (reverse)
                  oiJPInfo:: Maybe JPInfo	-- the info for jump poits
             }
data PathInfo = PathInfo {
                    piPoint :: {-# UNPACK #-} !Point,	-- the next point
                    piDir   :: !Dir,	-- next direction to take
                    piTimes :: {-# UNPACK #-} !Int	-- how many times
                } deriving Show
type Closed = S.Set Point

aStar :: (Monad m, Functor m)
      => ((Point, Maybe JPInfo) -> m [(Point, JPInfo)])	-- action to get the valid neighbours
      -> (Point -> Int)			-- heuristic funtion (target point is in closure)
      -> Point				-- from point
      -> (Point -> Bool)		-- function to check that we are there
      -> Maybe Int			-- maximum path length
      -> m (Maybe [PathInfo])		-- returns: possibly a path
aStar fions heur from fulfilled mmax = go iopen S.empty
    where oii = OpInfo { oiG = 0, oiF = heur from, oiPath = [], oiJPInfo = Nothing }
          iopen = opSingleton from oii :: BiMap
          go !open closed
             | opIsEmpty open = return Nothing	-- no path
             | fulfilled op   = return rez
             | Just mx <- mmax, oiG oi + heur op >= mx	-- we reached maximum length
                              = return Nothing
             | otherwise = do
                 let closed' = S.insert op closed
                 open' <- expandNode fions heur o os closed'
                 go open' closed'
             where (o@(op, oi), os) = opRemoveMin open
                   rez = Just $ oiPath oi

expandNode :: (OpenClass op, Monad m, Functor m)
      => ((Point, Maybe JPInfo) -> m [(Point, JPInfo)])	-- action to get the valid neighbours
      -> (Point -> Int)		-- heuristic function (target point is in closure)
      -> (Point, OpInfo)	-- current open node to expand (+ info)
      -> op			-- the open "list"
      -> Closed			-- the closed "list"
      -> m op			-- returns the new open list
expandNode fions heur (!ex, !oi) open !closed = foldl' go open <$> fions (ex, oiJPInfo oi)
    where go op (p, _) | p `S.member` closed = op
          go op dp@(p, jpi)
              = let !tent_g = oiG oi + jpCost jpi	-- proposed new cost
                in case opRetrieve p op of
                    Just oi' -> if tent_g >= oiG oi' then op else newsucc op dp tent_g
                    Nothing  -> newsucc op dp tent_g
          newsucc op dp@(p, jpi) tg
              = let opi = OpInfo { oiG = tg, oiF = tg + heur p,	-- new function values
                                   oiPath = pinfo : oiPath oi,	-- new path info
                                   oiJPInfo = Just jpi }	-- new jump point info
                    pinfo = PathInfo { piPoint = p, piDir = jpDir jpi, piTimes = jpCost jpi }
                in opInsert p opi op
                -- in opInsert p ((tg, tg + heur p), dp : sson) op
          -- sson = snd oi

-- Implement the open collection through 2 maps
data BiMap = BiMap {
                 perPoint :: M.Map Point OpInfo,
                 perValue :: M.Map Int [Point]	-- here we could use Set
             }

instance OpenClass BiMap where
    opIsEmpty   = biMapIsEmpty
    opSingleton = biMapSingleton
    opRemoveMin = biMapRemoveMin
    opRetrieve  = biMapRetrieve
    opInsert    = biMapInsert

biMapIsEmpty :: BiMap -> Bool
biMapIsEmpty = M.null . perPoint

biMapSingleton :: Point -> OpInfo -> BiMap
biMapSingleton p oi = BiMap { perPoint = pp, perValue = pv }
    where pp = M.singleton p oi
          pv = M.singleton v [p]
          v  = oiF oi

biMapRemoveMin :: BiMap -> ((Point, OpInfo), BiMap)
biMapRemoveMin bi = ((p, oi), bi')
    where pv = perValue bi
          v  = head $ M.keys pv			-- take smallest value
          ps = fromJust $ M.lookup v pv		-- and the corresponding list
          !p  = head ps				-- one of the points
          pp = perPoint bi
          !oi = fromJust $ M.lookup p pp	-- now we have the info
          !pp' = M.delete p pp			-- remove from per point map
          !pv' = if null (tail ps) then M.delete v pv else M.insert v (tail ps) pv
          bi' = BiMap { perPoint = pp', perValue = pv' }

biMapRetrieve :: Point -> BiMap -> Maybe OpInfo
biMapRetrieve p bi = M.lookup p (perPoint bi)

biMapInsert :: Point -> OpInfo -> BiMap -> BiMap
biMapInsert p oi bi = pp' `seq` pv'' `seq` BiMap { perPoint = pp', perValue = pv'' }
    where pp = perPoint bi
          pv = perValue bi
          v  = oiF oi
          !pp' = M.insert p oi pp
          -- now insert into value map, but remove a possibly existing old entry (from old value list)
          !pv' = case M.lookup p pp of
                    Nothing  -> pv
                    Just oi' -> let v' = oiF oi'
                                    ps = fromJust $ M.lookup v' pv
                                    ps' = delete p ps
                                in if null ps' then M.delete v' pv else M.insert v' ps' pv
          !pv'' = M.insertWith (++) v [p] pv'
