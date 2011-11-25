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
                    tgt :: Maybe Point	-- target: we will move to this point
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
    myc <- nextAnt True near' near1 gfun 0 us toMove ([], M.empty)
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
        nextAnt False near near1 gfun pla pants toMove' conf

-- Choose next ant to move, make all valid (and interesting) moves
-- Functions near and near1 are used to prune uninteresting moves
-- near ist the fight distance, near1 ist fight distance "+ 1" (i.e. one move
-- from the fight distance)
nextAnt :: Bool -> DstFun -> DstFun -> GenFun -> Int -> [Point] -> ToMove -> Config -> [Config]
nextAnt stop near near1 gfun _   []     toMove conf
    = if stop then return conf else nextPlayer near near1 gfun toMove conf
nextAnt stop near near1 gfun pla (a:as) toMove (acs, mp) = do
    (d, p) <- interMove near near1 gfun a pla toMove mp
    let acts = (a, d) : acs
        final = case d of
                  Any ds    -> mp
                  otherwise -> M.insert p pla mp
    nextAnt stop near near1 gfun pla as toMove (acts, final)

extend :: (Point -> [(Dir, Point)]) -> Point -> [(EDir, Point)]
extend f p = (Stay, p) : map (\(d, p') -> (Go d, p')) (f p)

-- Filter all possible moves: must not go to a busy point and must be interesting
interMove :: DstFun -> DstFun -> GenFun -> Point -> Int -> ToMove -> PoiMap -> [(EDir, Point)]
interMove near near1 gfun a pla toMove pm = go [] [] $ extend gfun a
    where go dcc acc [] = if null acc then dcc else (Any acc, a) : dcc
          go dcc acc (m@(d, p):ms) = case M.lookup p pm of
             Just _  -> go dcc acc ms
             Nothing -> if any (near1 p) tml || any (near p) cfl
                           then go (m:dcc) acc ms
                           else go dcc (d:acc) ms
          -- tml = concatMap snd $ filter ((/= pla) . fst) $ M.assocs toMove
          tml = enemiesOfPlayer pla toMove
          cfl = map fst $ filter ((/= pla) . snd) $ M.assocs pm

-- Having a final configuration we want to evaluate the outcome
-- For now we just make the difference: enemy loss - our loss
-- Bigger is better
evalOutcome :: DstFun -> EvalPars -> PoiMap -> Int
evalOutcome near epar final = our * (w - 100) + (the - our) * w
    where lom = getLosses near final
          all = M.fold (+) 0 lom
          our = maybe 0 id $ M.lookup 0 lom
          the = all - our
          w   = reg epar

-- We return the dead ants per (involved) player (a map)
-- Than we can weight the looses with some factors (in the caller)
-- for example to kill more from some player, or (if we have enough ants)
-- to accept even negative ballance, in order to eliminate a player or
-- raze a hill
getLosses :: DstFun -> PoiMap -> M.Map Int Int
getLosses near final = foldl' accDeads M.empty $ map fst deads
    where pairs = M.assocs final
          eneml = map (nearEnemies near pairs) pairs
          enemm = M.fromList eneml
          deads = filter df eneml
          df (_, (ecnt, es)) = any (deadly ecnt) es
          -- enemy is at least as strong (i.e. has smaller or equal count!):
          deadly cnt e = maybe False ((<= cnt) . fst) (M.lookup e enemm)
          accDeads m p = case M.lookup p final of	-- count the deads per player
                             Nothing -> m
                             Just pl -> M.insertWith (+) pl 1 m

-- For an ant, find the enemies in fight distance
nearEnemies :: DstFun -> [(Point, Int)] -> (Point, Int) -> (Point, (Int, [Point]))
nearEnemies near pis pi = (fst pi, (length en, en))
    where f (a1, p1) (a2, p2) = (a2, p1 /= p2 && near a1 a2)
          en = map fst . filter snd . zipWith f (repeat pi) $ pis

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
