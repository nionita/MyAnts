module Fight
--    (
--    EDir(..),
--    fightZones,
--    nextTurn
--    )
where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Ants

data EDir = Stay | Go Dir deriving Show	-- extended direction, as we can also choose to wait
type Action = (Point, EDir)		-- start point and direction to move
type GenFun = Point -> [(Dir, Point)]	-- to generate legal neighbours
type DstFun = Point -> Point -> Bool	-- to tell if 2 points are "near"
type ToMove = M.Map Int [Point]		-- yet to move players/ants
type PoiMap = M.Map Point Int		-- which players ant is in that point
type Config = ([Action], PoiMap)	-- actions and resulting distribution

-- This function calculates the best final configurations (and the moves
-- needed to reach them) per fight area
nextTurn :: DstFun -> GenFun -> (Int, Int) -> [Point] -> ToMove -> (Int, [Config])
nextTurn near gfun peso us toMove = getMaxs (minBound, []) $ ourMoves near gfun peso us toMove
    where getMaxs acc [] = acc
          getMaxs acc@(mx, cs) ((c, i) : cis)
              | i >  mx = getMaxs (i, [c]) cis
              | i == mx = getMaxs (mx, c:cs) cis
              | i <  mx = getMaxs acc cis

-- Evaluate every of our moves with the average of the possible answers
ourMoves :: DstFun -> GenFun -> (Int, Int) -> [Point] -> ToMove -> [(Config, Int)]
ourMoves near gfun (pes, opt) us toMove = do
    myc <- nextAnt True gfun 0 us toMove ([], M.empty)
    let ocfs = nextPlayer gfun toMove myc
        avg  = average pes opt $ map (evalOutcome near . snd) ocfs
    return (myc, avg)

-- Choose next player to move
nextPlayer :: GenFun -> ToMove -> Config -> [Config]
nextPlayer gfun toMove conf
    | M.null toMove = return conf
    | otherwise     = do
        let (pla, pants) = M.findMin toMove
            toMove' = M.delete pla toMove
        nextAnt False gfun pla pants toMove' conf

-- Choose next ant to move, make all valid moves
nextAnt :: Bool -> GenFun -> Int -> [Point] -> ToMove -> Config -> [Config]
nextAnt stop gfun _   []     toMove conf = if stop then return conf else nextPlayer gfun toMove conf
nextAnt stop gfun pla (a:as) toMove conf = do
    (d, p) <- extend gfun a	-- here we could prune "uninteresting" moves (at least for the last player)
    case M.lookup p (snd conf) of
        Just _  -> fail	"busy" -- that neighbour is busy
        Nothing -> do
            let acts = (a, d) : fst conf
                final = M.insert p pla (snd conf)
            nextAnt stop gfun pla as toMove (acts, final)

extend :: (Point -> [(Dir, Point)]) -> Point -> [(EDir, Point)]
extend f p = (Stay, p) : map (\(d, p') -> (Go d, p')) (f p)

-- Having a final configuration we want to evaluate the outcome
-- For now we just make the difference: enemy loss - our loss
-- Bigger is better
evalOutcome :: DstFun -> PoiMap -> Int
evalOutcome near final = all - 2 * our	-- because we counted them twice
    where lom = getLosses near final
          all = M.fold (+) 0 lom
          our = maybe 0 id $ M.lookup 0 lom

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
fightZones :: DstFun -> [Point] -> [PlPoint] -> [([Point], ToMove)] -> [([Point], ToMove)]
fightZones near us them acc
    | Just (root, (rest, seen)) <- findRoot near us them []
        = goFightZones near root rest them acc
    | otherwise = acc

goFightZones :: DstFun -> Point -> [Point] -> [PlPoint] -> [([Point], ToMove)] -> [([Point], ToMove)]
goFightZones near root rest them acc = fightZones near rus rthem (zon:acc)
    where fzi = FZI { unk = S.fromList (zip (repeat 0) rest) `S.union` S.fromList them,
                  ope = S.singleton (0, root), clo = S.empty }
          fzf = extendCol near fzi
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

average :: Int -> Int -> [Int] -> Int
average pes opt xs = go (0, 0, maxBound, minBound) xs
    where go (s, c, mi, ma) []     = (mi * pes + (s * av `div` c) + ma * opt) `div` 100
          go (s, c, mi, ma) (x:xs) = go (s+x, c+1, min mi x, max ma x) xs
          av = 100 - pes - opt
