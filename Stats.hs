module Stats (
    Stats,
    newStats, addParVal, estimateTime,
    showStats
    ) where

import qualified Data.Map as M
import Data.Maybe (fromMaybe, fromJust)

data ParStat = ParStat {
                 avg, sigma :: !Double,
                 vals :: [Double]
               }

data Stats = Stats {
                 scale, hist :: Int,
                 psmap :: M.Map Int ParStat
             }

stat0 = ParStat { avg = 0, sigma = 0, vals = [] }

newStats :: Int -> Int -> Stats
newStats sc hi = Stats { scale = sc, hist = hi, psmap = M.empty }

addParVal :: Stats -> Int -> Int -> Stats
addParVal sts par tim = sts { psmap = M.insert para new $ psmap sts }
    where timd = fromIntegral tim
          para = par `div` scale sts
          old = fromMaybe stat0 $ M.lookup para $ psmap sts
          va = take (hist sts) $ timd : vals old
          (cn, su) = go 0 0 va
          av = su / cn
          si = sqrt $ (/cn) $ sum $ map (\v -> (v - av)*(v - av)) va
          new = ParStat { avg = av, sigma = si, vals = va }
          go c s []     = (c, s)
          go c s (v:vs) = go (c+1) (s+v) vs

estimateTime :: Stats -> Int -> Int
estimateTime sts par
    | Just ps <- M.lookup para (psmap sts)
                = ceiling $ avg ps + 3 * sigma ps
    | otherwise = extrapolate sts para
    where para = par `div` scale sts

extrapolate :: Stats -> Int -> Int
extrapolate sts par
    | null sm   = extraBi sts par bi
    | null bi   = extraSm sts par sm
    | otherwise = interp sts par (last sm) (head bi)
    where pars = M.keys $ psmap sts
          (sm, bi) = break (> par) pars

interp :: Stats -> Int -> Int -> Int -> Int
interp sts par sm bi = ceiling $ (bia + sma) / 2
    where smt = fromJust $ M.lookup sm $ psmap sts
          bit = fromJust $ M.lookup bi $ psmap sts
          sma = est smt
          bia = est bit

extraSm :: Stats -> Int -> [Int] -> Int
extraSm sts par [sm] = 2 * estimateTime sts (sm * scale sts)
extraSm sts par (sm1:sm2:_) = ceiling $ v1 + 2 * v2
    where st1 = fromJust $ M.lookup sm1 $ psmap sts
          st2 = fromJust $ M.lookup sm2 $ psmap sts
          v1  = est st1
          v2  = est st2

extraBi :: Stats -> Int -> [Int] -> Int
extraBi _   _ []     = 0	-- we cannot approximate, this is the first measurement
extraBi sts _ (bi:_) = estimateTime sts (bi * scale sts)

est :: ParStat -> Double
est ps = avg ps + 3 * sigma ps

showStats :: Stats -> String
showStats sts = unlines $ map line as
    where as = M.assocs $ psmap sts
          line1 (v, ps) = "Val " ++ show v
                                ++ ": tim = " ++ show (est ps)
                                ++ ", avg = " ++ show (avg ps)
                                ++ ", sigma = " ++ show (sigma ps)
                                ++ " (" ++ show (length $ vals ps) ++ " values)"
          linen (v, ps) = "Val " ++ show (v * sc) ++ " - " ++ show (v * sc + sc - 1)
                                ++ ": tim = " ++ show (est ps)
                                ++ ", avg = " ++ show (avg ps)
                                ++ ", sigma = " ++ show (sigma ps)
                                ++ " (" ++ show (length $ vals ps) ++ " values)"
          sc = scale sts
          line = if sc == 1 then line1 else linen
