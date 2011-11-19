module Main where

import Data.List
import Data.Maybe (mapMaybe, fromJust)
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Directory

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
                   let cf = configRecord conf
                   runWith cf opts
               else putStrLn $ "Keys are missing in " ++ cfile ++ ": "
                               ++ concat (intersperse ", " kmiss)

checkConfig :: Config -> [String]
checkConfig conf = mapMaybe check ["Root", "Play", "LogDir", "Maps", "Engine" ]
    where check k = if keyVal conf k == Nothing then Just k else Nothing

configRecord :: Config -> ConfigRecord
configRecord conf = CF {
    cfRoot = fromJust $ keyVal conf "Root",
    cfPlay = fromJust $ keyVal conf "Play",
    cfLogDir = fromJust $ keyVal conf "LogDir",
    cfTurns = read $ fromJust $ keyVal conf "Turns",
    cfMaps = fromJust $ keyVal conf "Maps",
    cfPars = fromJust $ keyVal conf "Pars",
    cfEngine = fromJust $ keyVal conf "Engine",
    cfEngines = case keyMap conf "Engines" of
                    Just m -> m
                    _      -> M.empty
    }

runWith cf opts = do
    maps <- getMaps cf
    mapM_ putStrLn maps
    -- putStrLn "CmdLine:"
    -- let cmd = 

getMaps :: ConfigRecord -> IO [String]
getMaps cf = do
    -- case keyVal conf 
    cwd <- getCurrentDirectory
    -- setCurrentDirectory mdir
    setCurrentDirectory cwd
    return []

-- vim: set expandtab:
