{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Fight
      (
      EDir(..),
      EvalPars(..),
      fightZones,
      nextTurn,
      zoneMax, zoneMaxMax, zoneMaxUs
      )
where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Ord (comparing)
import Data.Function (on)
import Debug.Trace

import Ants

-- mytrace = trace
mytrace _ x = x

-- Some constants
zoneMax      = 8  :: Int	-- max ants in a zone fight for full calculation
zoneMaxMax   = 10 :: Int	-- max ants in a zone fight
zoneMaxUs    = 3  :: Int	-- max of our ants in a bigger zone fight
zoneMaxUsClc = 5  :: Int	-- max of our ants for which we do full calculation

data EDir = Any [EDir] | Stay | Go Dir deriving (Eq, Show)	-- extended direction, as we can also choose to wait
type Action = (Point, EDir)		-- start point and direction to move
type GenFun = Point -> [(Dir, Point)]	-- to generate legal neighbours
type DstFun = Point -> Point -> Bool	-- to tell if 2 points are "near"
type ToMove = M.Map Int [Point]		-- yet to move players/ants
type PoiMap = M.Map Point Int		-- which players ant is in that point
type Config = ([Action], PoiMap)	-- actions and resulting distribution
type FPoint = (Float, Float)

data EvalPars = EvalPars {
                    bnd :: Point,	-- we need again and again this bound
                    pes :: Float,	-- weight of the worst case
                    opt :: Float,	-- weight of the best case (100-pes-opt=weight of avg)
                    reg :: Int,		-- weight of enemy ants (100-reg=weight of ours)
                    agr :: Bool,	-- agressiv moves preferred
                    tgt :: Maybe Point,	-- target: we will move to this point
                    tgs :: (Int, Int)	-- scores for target point (us, them), unit ants
                } deriving Show

-- This function calculates the best final configurations (and the moves
-- needed to reach them) per fight area
nextTurn :: Int -> Int -> GenFun -> EvalPars -> [Point] -> ToMove -> (FPoint, Config)
nextTurn dist dist1 gfun epar us toMove = mytrace ("our moves: " ++ show (cf:cfs)) $ getMaxs cf cfs
    where getMaxs !acc [] = acc
          getMaxs !acc@(!mx, cs) ((i, c) : cis)
              | i >  mx   = getMaxs (i, c) cis
              -- | i == mx   = getMaxs (i, c) cis
              | otherwise = getMaxs acc cis
          (cf:cfs) = ourMoves dist dist1 gfun epar us toMove

-- Evaluate every of our moves with the average of the possible answers
ourMoves :: Int -> Int -> GenFun -> EvalPars -> [Point] -> ToMove -> [(FPoint, Config)]
ourMoves dist dist1 gfun epar us toMove = do
    let amvs = sortBy (comparing (fst . snd)) $ map (interMove near' near1 gfun epar 0 toMove M.empty) us
        ourlen = length us
        reduce = if ourlen > zoneMaxUsClc then 2 ^ (ourlen - zoneMaxUsClc) else 1
        mycfs = nextAnt True near' near1 gfun epar 0 amvs toMove ([], M.empty)
        consider = length mycfs `div` reduce
    myc <- take consider $ sortConfigs mycfs
    let ocfs = nextPlayer near' near1 gfun epar toMove myc
        ooc  = gravCenter us
        oec  = gravCenter $ enemiesOfPlayer 0 toMove
        od   = euclidSquare (bnd epar) oec ooc
        avg  = average (pes epar) (opt epar) $ map (evalOutcome near' epar (oec, od) . snd) ocfs
    return (avg, myc)
    where near' = near dist  (bnd epar)
          near1 = near dist1 (bnd epar)

-- Choose next player to move
nextPlayer :: DstFun -> DstFun -> GenFun -> EvalPars -> ToMove -> Config -> [Config]
nextPlayer near near1 gfun epar toMove conf
    | M.null toMove = return conf
    | otherwise     = do
        let (pla, pants) = M.findMin toMove
            toMove' = M.delete pla toMove
            amvs = sortBy (comparing (fst . snd))
                      $ map (interMove near near1 gfun epar pla toMove (snd conf)) pants
        nextAnt False near near1 gfun epar pla amvs toMove' conf

-- Choose next ant to move, make all valid (and interesting) moves
-- Functions near and near1 are used to prune uninteresting moves
-- near ist the fight distance, near1 ist fight distance "+ 1" (i.e. one move
-- from the fight distance)
nextAnt :: Bool -> DstFun -> DstFun -> GenFun -> EvalPars -> Int -> [(Point, (Int, [(EDir, Point)]))]
        -> ToMove -> Config -> [Config]
nextAnt stop near near1 gfun epar _   []                 toMove conf
    = if stop then return conf else nextPlayer near near1 gfun epar toMove conf
nextAnt stop near near1 gfun epar pla ((a, (_, mvs)):as) toMove (acs, mp) = do
    (d, p) <- freeMove mp mvs
    let acts = (a, d) : acs
        final = case d of
                  Any ds -> mp
                  _      -> M.insert p pla mp
    nextAnt stop near near1 gfun epar pla as toMove (acts, final)

extend :: (Point -> [(Dir, Point)]) -> Point -> [(EDir, Point)]
extend f p = (Stay, p) : map (\(d, p') -> (Go d, p')) (f p)

-- Filter all possible moves: must not go to a busy point and must be interesting
interMove :: DstFun -> DstFun -> GenFun -> EvalPars -> Int -> ToMove -> PoiMap
          -> Point -> (Point, (Int, [(EDir, Point)]))
interMove near near1 gfun epar pla toMove pm a = go [] [] $ extend gfun a
    where go dcc acc [] = case acc of
                              []  -> (a, (length dcc, dcc))
                              [m] -> (a, (1 + length dcc, m : dcc))
                              _   -> (a, (1 + length dcc, (Any $ map fst acc, a) : dcc))
          go dcc acc (m@(d, p):ms) = case M.lookup p pm of
             Just _  -> go dcc acc ms
             Nothing -> case tgt epar of
                 Nothing -> if any (near1 p) tml || any (near p) cfl
                               then go (m:dcc) acc ms
                               else go dcc (m:acc) ms
                 Just h  -> if h == p || any (near1 p) tml || any (near p) cfl
                               then go (m:dcc) acc ms
                               else go dcc (m:acc) ms
          -- tml = concatMap snd $ filter ((/= pla) . fst) $ M.assocs toMove
          tml = enemiesOfPlayer pla toMove
          cfl = map fst $ filter ((/= pla) . snd) $ M.assocs pm

freeMove :: PoiMap -> [(EDir, Point)] -> [(EDir, Point)]
freeMove pm = filter (\(_, p) -> M.lookup p pm == Nothing)

-- Having a final configuration we want to evaluate the outcome
-- We evaluate the difference: enemy loss - our loss
-- but with variable weight for our and enemy losses
-- and add perhaps a bonus for occupying the target (if given)
-- When playing aggresive we also give in a second component
-- a better score for moves that win space (i.e. go near to the enemy)
evalOutcome :: DstFun -> EvalPars -> (Point, Int) -> PoiMap -> (Int, Int)
evalOutcome near epar (oec, od) final = mytrace tr $ sc `seq` adv `seq` (sc, adv)
    where dds = getLosses near final
          (our, the) = M.fold count (0, 0) dds
          w   = reg epar
          tgp = maybe 0 target (tgt epar)
          (w1, w2) = tgs epar
          alive = M.difference final dds
          ealive = filter ((==0) . snd) $ M.assocs alive
          ngc = gravCenter $ map fst ealive
          dif = od - euclidSquare (bnd epar) oec ngc
          adv = if agr epar && not (null ealive) then dif else 0
          sc = tgp * 100 + our * (w - 100) + (the - our) * w
          count p (a, b) = if p == 0 then (a+1, b) else (a, b+1)
          target p = case M.lookup p alive of
                         Nothing -> 0
                         Just pl -> if pl == 0 then w1 else w2
          tr = show final ++ ":\n" ++ show (sc, adv) ++ ", deads = " ++ show dds
                 ++ ", alive = " ++ show alive ++ ", tgp = " ++ show tgp

-- We return the dead ants per (involved) player (a map)
-- and a map of dead ants (value: player)
-- Than we can weight the looses with some factors (in the caller)
-- for example to kill more from some player, or (if we have enough ants)
-- to accept even negative ballance, in order to eliminate a player or
-- raze a hill
-- also we can see if a hill was razed during the fight, by comparing
-- the alive ants with the hill position (this is done in caller)
getLosses :: DstFun -> PoiMap -> PoiMap
getLosses near final = deads near $ combats near $ M.assocs final

combats :: DstFun -> [(Point, Int)] -> [((Point, Int), Int)]
combats near = map simpl . group . sort . go []
    where go acc []       = acc
          go acc (pi@(p, i):pis) = go rez pis
              where rez = foldr bat acc pis
                    bat qj@(q, j) acc
                        | i == j    = acc
                        | near p q  = pi : qj : acc
                        | otherwise = acc
          simpl li@(pi:_) = (pi, length li)

deads :: DstFun -> [((Point, Int), Int)] -> PoiMap
deads near = go M.empty
    where go acc []    = acc
          go acc (pi@((p, _), _):pis)
              | M.member p acc = go acc pis
              | otherwise      = check acc pi pis
          check acc _              []            = acc
          check acc pi@((p, i), m) (qj@((q, j), n):pis)
              | i == j    = check acc pi pis
              | near p q  = case compare m n of
                               LT -> check (M.insert q j acc) pi pis
                               EQ -> M.insert q j $ M.insert p i acc
                               GT -> M.insert p i acc
              | otherwise = check acc pi pis

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

-- Calculate an mean, minimum and maximum of achievable scores and combine all
-- into a final score (with parameter for pessimistic and optimistic behaviour)
-- Also calculate a mean of space win (second component)
average :: Float -> Float -> [(Int, Int)] -> (Float, Float)
average pes opt xs = go (0, 0, maxmax, -maxmax, 0) xs
    where go (!s, !c, !mi, !ma, !di) [] = ((mi * pes + (s * av / c) + ma * opt) / 100, di / c)
          go (!s, !c, !mi, !ma, !di) ((x, d):xs)
              = let y = fromIntegral x
                    z = fromIntegral d
                in  go (s+y, c+1, min mi y, max ma y, di+z) xs
          av = 100 - pes - opt
          maxmax = 10000000

near r u a b = euclidSquare u a b <= r

enemiesOfPlayer pla toMove = concatMap snd $ filter ((/= pla) . fst) $ M.assocs toMove

-- Some configurations are more resilient than other
sigma :: [Point] -> (Double, Double)
sigma ps = (sigx, sigy)
    where sumx = sum $ map (fromIntegral . fst) ps
          sumy = sum $ map (fromIntegral . snd) ps
          sigx = sum $ map (f sumx . fst) ps
          sigy = sum $ map (f sumy . snd) ps
          f c x = let d = c - fromIntegral x in d * d

-- (0, sy), (sx, 0) and (s, s) are best -- these are horizontal, vertical or diagonal lines
-- So one configuration is better if it's near of of those
-- Smaller note is better
note :: (Double, Double) -> Double
note (x, y) = min (abs (x - y)) $ min x y

-- Sort configs as described above
sortConfigs :: [Config] -> [Config]
sortConfigs = undecorate . sortBy (comparing snd) . decorate (note . sigma . M.keys . snd)

decorate :: (a -> b) -> [a] -> [(a, b)]
decorate f = map (\a -> (a, f a))

undecorate = map fst
