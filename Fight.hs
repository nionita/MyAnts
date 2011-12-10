{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Fight
      (
      EDir(..),
      EvalPars(..),
      fightZones,
      nextTurn
      )
where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Ord (comparing)
import Data.Function (on)

import Ants

data EDir = Any [EDir] | Stay | Go Dir deriving (Eq, Show)	-- extended direction, as we can also choose to wait
type Action = (Point, EDir)		-- start point and direction to move
type GenFun = Point -> [(Dir, Point)]	-- to generate legal neighbours
type DstFun = Point -> Point -> Bool	-- to tell if 2 points are "near"
type ToMove = M.Map Int [Point]		-- yet to move players/ants
type PoiMap = M.Map Point Int		-- which players ant is in that point
type Config = ([Action], PoiMap)	-- actions and resulting distribution
type FPoint = (Float, Float)

data EvalPars = EvalPars {
                    pes :: Float,	-- weight of the worst case
                    opt :: Float,	-- weight of the best case (100-pes-opt=weight of avg)
                    reg :: Int,		-- weight of enemy ants (100-reg=weight of ours)
                    agr :: Bool,	-- agressiv moves preferred
                    tgt :: Maybe Point,	-- target: we will move to this point
                    tgs :: (Int, Int)	-- scores for target point (us, them), unit ants
                } deriving Show

-- This function calculates the best final configurations (and the moves
-- needed to reach them) per fight area
nextTurn :: Point -> Int -> Int -> GenFun -> EvalPars -> [Point] -> ToMove -> (FPoint, Config)
nextTurn bound dist dist1 gfun epar us toMove = getMaxs cf cfs
    where getMaxs !acc [] = acc
          getMaxs !acc@(!mx, cs) ((i, c) : cis)
              | i >  mx   = getMaxs (i, c) cis
              -- | i == mx   = getMaxs (i, c) cis
              | otherwise = getMaxs acc cis
          (cf:cfs) = ourMoves bound dist dist1 gfun epar us toMove

-- Evaluate every of our moves with the average of the possible answers
ourMoves :: Point -> Int -> Int -> GenFun -> EvalPars -> [Point] -> ToMove
         -> [(FPoint, Config)]
ourMoves bound dist dist1 gfun epar us toMove = do
    let amvs = sortBy (comparing (fst . snd)) $ map (interMove near' near1 gfun 0 toMove M.empty) us
    myc <- nextAnt True near' near1 gfun 0 amvs toMove ([], M.empty)
    let ocfs = nextPlayer near' near1 gfun toMove myc
        avg  = average (pes epar) (opt epar) $ map (evalOutcome near' epar . snd) ocfs
        sec  = if agr epar then inv else 0
        ens  = enemiesOfPlayer 0 toMove
        -- (gc, va) = gravVar ens
        gcu = gravCenter us
        gce = gravCenter ens
        inv = if gce == gcu then 1 else 1 / fromIntegral (distance bound gce gcu)
    return ((avg, sec), myc)
    where near' = near dist  bound
          near1 = near dist1 bound

-- Choose next player to move
nextPlayer :: DstFun -> DstFun -> GenFun -> ToMove -> Config -> [Config]
nextPlayer near near1 gfun toMove conf
    | M.null toMove = return conf
    | otherwise     = do
        let (pla, pants) = M.findMin toMove
            toMove' = M.delete pla toMove
            amvs = sortBy (comparing (fst . snd))
                      $ map (interMove near near1 gfun pla toMove (snd conf)) pants
        nextAnt False near near1 gfun pla amvs toMove' conf

-- Choose next ant to move, make all valid (and interesting) moves
-- Functions near and near1 are used to prune uninteresting moves
-- near ist the fight distance, near1 ist fight distance "+ 1" (i.e. one move
-- from the fight distance)
nextAnt :: Bool -> DstFun -> DstFun -> GenFun -> Int -> [(Point, (Int, [(EDir, Point)]))]
        -> ToMove -> Config -> [Config]
nextAnt stop near near1 gfun _   []                 toMove conf
    = if stop then return conf else nextPlayer near near1 gfun toMove conf
nextAnt stop near near1 gfun pla ((a, (_, mvs)):as) toMove (acs, mp) = do
    (d, p) <- freeMove mp mvs
    let acts = (a, d) : acs
        final = case d of
                  Any ds -> mp
                  _      -> M.insert p pla mp
    nextAnt stop near near1 gfun pla as toMove (acts, final)

extend :: (Point -> [(Dir, Point)]) -> Point -> [(EDir, Point)]
extend f p = (Stay, p) : map (\(d, p') -> (Go d, p')) (f p)

-- Filter all possible moves: must not go to a busy point and must be interesting
interMove :: DstFun -> DstFun -> GenFun -> Int -> ToMove -> PoiMap
          -> Point -> (Point, (Int, [(EDir, Point)]))
interMove near near1 gfun pla toMove pm a = go [] [] $ extend gfun a
    where go dcc acc [] = if null acc
                             then (a, (length dcc, dcc))
                             else (a, (1 + length dcc, (Any acc, a) : dcc))
          go dcc acc (m@(d, p):ms) = case M.lookup p pm of
             Just _  -> go dcc acc ms
             Nothing -> if any (near1 p) tml || any (near p) cfl
                           then go (m:dcc) acc ms
                           else go dcc (d:acc) ms
          -- tml = concatMap snd $ filter ((/= pla) . fst) $ M.assocs toMove
          tml = enemiesOfPlayer pla toMove
          cfl = map fst $ filter ((/= pla) . snd) $ M.assocs pm

freeMove :: PoiMap -> [(EDir, Point)] -> [(EDir, Point)]
freeMove pm = filter (\(_, p) -> M.lookup p pm == Nothing)

-- Having a final configuration we want to evaluate the outcome
-- For now we just make the difference: enemy loss - our loss
-- Bigger is better
evalOutcome :: DstFun -> EvalPars -> PoiMap -> Int
evalOutcome near epar final = tgp * 100 + our * (w - 100) + (the - our) * w
    where dds = getLosses near final
          (our, the) = M.fold count (0, 0) dds
          w   = reg epar
          tgp = maybe 0 target (tgt epar)
          (w1, w2) = tgs epar
          count p (a, b) = if p == 0 then (a+1, b) else (a, b+1)
          target p = let alive = M.difference final dds
                     in case M.lookup p alive of
                         Nothing -> 0
                         Just pl -> if pl == 0 then w1 else w2

-- We return the dead ants per (involved) player (a map)
-- and a map of dead ants (value: player)
-- Than we can weight the looses with some factors (in the caller)
-- for example to kill more from some player, or (if we have enough ants)
-- to accept even negative ballance, in order to eliminate a player or
-- raze a hill
-- also we can see if a hill was razed during the fight, by comparing
-- the alive ants with the hill position (this is done in caller)
getLosses :: DstFun -> PoiMap -> PoiMap
getLosses near final = foldl' accDeads M.empty $ map fst $ filter df eneml
    where -- pairs = M.assocs final
          -- eneml = map (nearEnemies near pairs) pairs
          eneml = combats near $ M.assocs final
          df (_, (ecnt, es)) = any (deadly ecnt) es
          -- enemy is at least as strong (i.e. has smaller or equal count!):
          deadly cnt e = maybe False ((<= cnt) . fst) (lookup e eneml)
          accDeads d p = maybe d (\pl -> M.insert p pl d) (M.lookup p final)

-- For an ant, find the enemies in fight distance
nearEnemies :: DstFun -> [(Point, Int)] -> (Point, Int) -> (Point, (Int, [Point]))
nearEnemies near pis pi = (fst pi, (length en, en))
    where f (a1, p1) (a2, p2) = (a2, p1 /= p2 && near a1 a2)
          en = map fst . filter snd . zipWith f (repeat pi) $ pis

combats :: DstFun -> [(Point, Int)] -> [(Point, (Int, [Point]))]
combats near = map simpl . groupBy ((==) `on` fst) . sort . go []
    where go acc []       = acc
          go acc (pi:pis) = go (rez [] pi pis ++ acc) pis
          rez acc _ [] = acc
          rez acc pi@(p, i) ((q, j):pis)
              | i == j    = rez acc pi pis
              | near p q  = rez ((p, q) : (q, p) : acc) pi pis
              | otherwise = rez acc pi pis
          simpl li@((p, _):_) = (p, (length li, map snd li))

type PlPoint = (Int, Point)
type PPSet = S.Set PlPoint

data FZoneInt = FZI { unk, ope, clo :: PPSet }

extendCol :: DstFun -> FZoneInt -> FZoneInt
extendCol near fzi
    | Just (ex, ope') <- S.minView (ope fzi) = extendOne near ex fzi { ope = ope' }
    | otherwise                              = fzi

extendOne :: DstFun -> PlPoint -> FZoneInt -> FZoneInt
extendOne near ex@(p, a) fzi = extendCol near fzi { unk = unk', ope = ope', clo = clo' }
    where oped = S.filter f (unk fzi)
          ope' = ope fzi `S.union` oped
          unk' = unk fzi `S.difference` oped
          clo' = S.insert ex $ clo fzi
          f (p2, a2) = p /= p2 && near a a2

findRoot :: DstFun -> [Point] -> [PlPoint] -> [Point] -> Maybe (Point, ([Point], [Point]))
findRoot _    []     _   _    = Nothing
findRoot near (o:os) ens seen
    | any f ens = Just (o, (os, seen))
    | otherwise       = findRoot near os ens (o:seen)
    where f (_, a2) = near o a2

-- This function divides all ants in fight zones
-- In a fight zone only ants are included, which have contact
-- with enemy ants from that zone - recursively
fightZones :: Point -> Int -> [Point] -> [PlPoint] -> [([Point], ToMove)] -> [([Point], ToMove)]
fightZones bound dist us them acc
    | Just (root, (rest, seen)) <- findRoot (near dist bound) us them []
        = goFightZones bound dist root rest them acc
    | otherwise = acc

goFightZones :: Point -> Int -> Point -> [Point] -> [PlPoint] -> [([Point], ToMove)]
             -> [([Point], ToMove)]
goFightZones bound dist root rest them acc = fightZones bound dist rus rthem (zon:acc)
    where fzi = FZI { unk = S.fromList (zip (repeat 0) rest) `S.union` S.fromList them,
                  ope = S.singleton (0, root), clo = S.empty }
          fzf = extendCol (near dist bound) fzi
          zon = makeZone $ clo fzf
          (rus, rthem) = restOursAnts $ unk fzf

makeZone :: PPSet -> ([Point], ToMove)
makeZone pps = (us, amap)
    where us = map snd $ filter ((==0) . fst) $ S.toList pps
          amap = M.fromListWith (++) $ map (\(p, x) -> (p, [x])) $ filter ((/=0) . fst) $ S.toList pps

restOursAnts :: PPSet -> ([Point], [PlPoint])
restOursAnts pps = (us, them)
    where us = map snd $ filter ((==0) . fst) $ S.toList pps
          them = filter ((/=0) . fst) $ S.toList pps

average :: Float -> Float -> [Int] -> Float
average pes opt xs = go (0, 0, 1000000, -1000000) xs
    where go (!s, !c, !mi, !ma) []     = (mi * pes + (s * av / c) + ma * opt) / 100
          go (!s, !c, !mi, !ma) (x:xs) = let y = fromIntegral x
                                         in  go (s+y, c+1, min mi y, max ma y) xs
          av = 100 - pes - opt

near r u a b = euclidSquare u a b <= r

enemiesOfPlayer pla toMove = concatMap snd $ filter ((/= pla) . fst) $ M.assocs toMove
