module Main where

import Control.Applicative ((<$>))
import Control.Concurrent (threadDelay)
import Control.Monad (filterM, liftM, liftM2)
import Data.List
import Data.Maybe (mapMaybe, fromJust)
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Directory
import System.FilePath
import System.Cmd
import System.Random

import Config

data ConfigRecord = CF {
        cfRoot   :: String,
        cfPlay   :: String,
        cfLogDir :: String,
        cfTurns  :: Int,
        cfMaps   :: String,
        cfPars   :: String,
        cfEngine :: String,
        cfEngines :: M.Map String String
    }

main = do
    args <- getArgs
    let (cfile, opts) = if null args then ("Games.txt", []) else (head args, tail args)
    mconf <- getConfig cfile
    case mconf of
        Nothing   -> return ()
        Just conf -> do
           let kmiss = checkConfig conf
           if null kmiss
               then do
                   let cf = configRecord $ resolveConfig conf
                   runWith cf opts
               else putStrLn $ "Keys are missing in " ++ cfile ++ ": "
                               ++ concat (intersperse ", " kmiss)

checkConfig :: Config -> [String]
checkConfig conf = mapMaybe checkV ["Root", "Play", "LogDir", "Maps", "Engine"]
                ++ mapMaybe checkD ["Engines"]
    where checkV k = if keyVal conf k == Nothing then Just k else Nothing
          checkD k = if keyMap conf k == Nothing then Just k else Nothing

configRecord :: Config -> ConfigRecord
configRecord conf = CF {
    cfRoot = fromJust $ keyVal conf "Root",
    cfPlay = fromJust $ keyVal conf "Play",
    cfLogDir = fromJust $ keyVal conf "LogDir",
    cfTurns = read $ fromJust $ keyVal conf "Turns",
    cfMaps = fromJust $ keyVal conf "Maps",
    cfPars = fromJust $ keyVal conf "Pars",
    cfEngine = fromJust $ keyVal conf "Engine",
    cfEngines = fromJust $ keyMap conf "Engines"
    }

runWith cf opts = do
    maps  <- getMaps cf
    mymap <- pickRandom maps
    let pl = fromJust $ playerNum mymap
    engs <- randomEngines (pl-1) (M.elems $ cfEngines cf)
    putStrLn $ "Map " ++ mymap ++ " (" ++ show pl ++ " players)"
    let logs = "--log_dir " ++ (cfRoot cf </> cfLogDir cf)
        trns = "--turns " ++ show (cfTurns cf)
        mapf = "--map_file " ++ mymap
        me = cfEngine cf
        qengs = map quote engs
    putStrLn "Engines:"
    putStrLn me
    mapM_ putStrLn engs
    let cmd = unwords $ [ cfPlay cf, logs, trns, cfPars cf, mapf, me] ++ qengs
    threadDelay 1000000 -- sleep 1 second before start
    system cmd
    putStrLn $ "This was: map " ++ mymap ++ " (" ++ show pl ++ " players)"
    putStrLn "Engines:"
    putStrLn me
    mapM_ putStrLn engs

getMaps :: ConfigRecord -> IO [String]
getMaps cf = do
    let mdir = cfRoot cf </> cfMaps cf
    msdirs <- map (mdir </>) <$> filter ((/= '.') . head) <$> onlyDirs mdir
    maps   <- concat <$> mapM getMapFiles msdirs
    return maps

onlyDirs path = getDirectoryContents path >>= filterM (\f -> doesDirectoryExist $ path </> f)

getMapFiles dir
    = map (dir </>) <$> filter ((/= Nothing) . playerNum) <$> filter (".map" `isSuffixOf`)
         <$> getDirectoryContents dir >>= filterM (\f -> doesFileExist $ dir </> f)

playerNum :: String -> Maybe Int
playerNum s = go $ infix0 ++ infix1
    where infix1 = [ ("_p0" ++ show i ++ "_", i)    | i <- [2..9]]
                ++ [ ("_p1" ++ show i ++ "_", i+10) | i <- [0..2]]
          infix0 = [ ("_0" ++ show i ++ "p_", i)    | i <- [2..9]]
                ++ [ ("_1" ++ show i ++ "p_", i+10) | i <- [0..2]]
          go [] = Nothing
          go ((ifi, k):is) = if ifi `isInfixOf` s then Just k else go is

randomEngines :: Int -> [String] -> IO [String]
randomEngines n es
    | l >= n = liftM (take n) $ randomPerm es
    | l <  n = liftM2 (++) (randomPerm es) (go [] (n-l))
    where go acc 0 = return acc
          go acc k = do
             r <- pickRandom es
             go (r : acc) (k-1)
          l = length es

-- Pick a random element from a non empty list
pickRandom :: [a] -> IO a
pickRandom as = do
    r <- randomRIO (0, length as - 1)
    return (as!!r)

-- Make a random permutation of a list
randomPerm :: Eq a => [a] -> IO [a]
randomPerm [] = return []
randomPerm as = do
    r  <- pickRandom as
    rs <- randomPerm $ delete r as
    return (r : rs)

quote :: String -> String
quote x = '"' : x ++ ['"']

-- vim: set expandtab:
