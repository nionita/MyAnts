{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}

module AStar (
    PathInfo,
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
    opIsEmpty   :: op -> Bool				-- is the collection empty?
    opSingleton :: Point -> OpenInfo -> op		-- create a singleton collection
    opRemoveMin :: op -> ((Point, OpenInfo), op)	-- retrieve & remove one with the smallest f value
    opRetrieve  :: Point -> op -> Maybe OpenInfo	-- retrieve by key (point)
    opInsert    :: Point -> OpenInfo -> op -> op	-- insert (or replace) point

type PathInfo = (Dir, Point)			-- direction (to move) and the neightbour in this direction
type OpenInfo = ((Int, Int), [PathInfo])	-- info for open vertices: costs (g, f) and path
type Closed = S.Set Point

-- Some helper functions for brevity
f, g :: OpenInfo -> Int
f = snd . fst
g = fst . fst

aStar :: (Monad m, Functor m)
      => (Point -> m [PathInfo])	-- action to get the valid neighbours of a point
      -> (Point -> Int)			-- heuristic funtion (target point is in closure)
      -> Point				-- from point
      -> (Point -> Bool)		-- function to check that we are there
      -> Maybe Int			-- maximum path length
      -> m (Maybe [PathInfo])		-- returns: possibly a path
aStar fions heur from fulfilled mmax = go iopen S.empty
    where iopen = opSingleton from ((0, heur from), []) :: BiMap
          go open closed
             | opIsEmpty open = return Nothing	-- no path
             | fulfilled op   = return rez
             | Just mx <- mmax, g oi + heur op >= mx	-- we reached maximum length
                              = return Nothing
             | otherwise = do
                 let !closed' = S.insert op closed
                 !open' <- expandNode fions heur o os closed'
                 go open' closed'
             where (o@(op, oi), os) = opRemoveMin open
                   rez = Just . snd $ oi

expandNode :: (OpenClass op, Monad m, Functor m)
           => (Point -> m [PathInfo])	-- action to get the valid neighbours of a point
           -> (Point -> Int)		-- heuristic function (target point is in closure)
           -> (Point, OpenInfo)		-- current open node to expand (+ info)
           -> op			-- the open "list"
           -> Closed			-- the closed "list"
           -> m op			-- returns the new open list
expandNode fions heur (!ex, oi) open closed = foldl' go open <$> fions ex
    where go op (_, p) | p `S.member` closed = op
          go op dp@(_, p)
              = case opRetrieve p op of
                    Just oi -> if tent_g >= g oi then op else newsucc op dp
                    Nothing -> newsucc op dp
          newsucc op dp@(_, p) = opInsert p ((tent_g, tent_g + heur p), dp : sson) op
          !tent_g = g oi + 1	-- in our case the edge cost is always 1
          sson = snd oi

-- Implement the open collection through 2 maps
data BiMap = BiMap {
                 perPoint :: M.Map Point OpenInfo,
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

biMapSingleton :: Point -> OpenInfo -> BiMap
biMapSingleton p oi = BiMap { perPoint = pp, perValue = pv }
    where pp = M.singleton p oi
          pv = M.singleton v [p]
          v  = f oi

biMapRemoveMin :: BiMap -> ((Point, OpenInfo), BiMap)
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

biMapRetrieve :: Point -> BiMap -> Maybe OpenInfo
biMapRetrieve p bi = M.lookup p (perPoint bi)

biMapInsert :: Point -> OpenInfo -> BiMap -> BiMap
biMapInsert p oi bi = BiMap { perPoint = pp', perValue = pv'' }
    where pp = perPoint bi
          pv = perValue bi
          v  = f oi
          !pp' = M.insert p oi pp
          -- now insert into value map, but remove a possibly existing old entry (from old value list)
          !pv' = case M.lookup p pp of
                    Nothing  -> pv
                    Just oi' -> let v' = f oi'
                                    ps = fromJust $ M.lookup v' pv
                                    ps' = delete p ps
                                in if null ps' then M.delete v' pv else M.insert v' ps' pv
          !pv'' = M.insertWith (++) v [p] pv'
