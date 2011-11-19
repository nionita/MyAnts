module Config (
    Config,
    getConfig,
    resolveConfig,
    keyVal, keyDict, keyMap
    ) where

import Control.Monad (liftM)
import qualified Data.Map as M
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec ((<|>))

type Config = M.Map String ConVal

data ConVal = Val String
            | Map Config
    deriving Show

getConfig :: String -> IO (Maybe Config)
getConfig file = do
    fc <- readFile file
    case parseConfig fc of
        Left err -> do
            putStrLn $ "Parse: " ++ show err
            return Nothing
        Right c  -> return (Just c)

resolveConfig :: Config -> Config
resolveConfig c = resolveConfig' c c

keyVal :: Config -> String -> Maybe String
keyVal c k = case M.lookup k c of
                 Just (Val s) -> Just s
                 _            -> Nothing

keyDict :: Config -> String -> Maybe Config
keyDict c k = case M.lookup k c of
                 Just (Map m) -> Just m
                 _            -> Nothing

keyMap :: Config -> String -> Maybe (M.Map String String)
keyMap c k = case M.lookup k c of
                 Just (Map m) -> Just $ M.map (\(Val s) -> s) $ M.filter vals m
                 _            -> Nothing
    where vals (Val _) = True
          vals _       = False

resolveConfig' :: Config -> Config -> Config
resolveConfig' c m = M.map (resolveConVal c) m

resolveConVal :: Config -> ConVal -> ConVal
resolveConVal c (Val s) = Val $ replaceVars c "" s
resolveConVal c (Map m) = Map $ resolveConfig' c m

replaceVars :: Config -> String -> String -> String
replaceVars c s0 s = case findVar s0 s of
    Left s'                  -> s'
    Right (var, (pre, post)) -> case M.lookup var c of
        Nothing       -> error $ "Key " ++ var ++ " is not defined, but found in: " ++ s0 ++ s
        Just (Val vv) -> replaceVars c (pre ++ vv) post
        _             -> error $ "Key " ++ var ++ " is not an assignment, found in: " ++ s0 ++ s

findVar :: String -> String -> Either String (String, (String, String))
findVar s0 s
    | null post          = Left (s0 ++ s)
    | _:'(':rest <- post = endVar (s0 ++ pre) rest
    | otherwise          = findVar (s0 ++ pre ++ "$") (tail post)
    where (pre, post) = break (== '$') s

endVar :: String -> String -> Either String (String, (String, String))
endVar s0 s
    | null post = Left (s0 ++ "$(" ++ s)
    | otherwise = Right (pre, (s0, tail post))
    where (pre, post) = break (== ')') s

parseConfig :: String -> Either P.ParseError Config
parseConfig = P.parse config ""

config = do
    as <- P.many assoc
    let m = M.fromList as
    return m

assoc = do
    P.spaces
    k <- key
    P.spaces
    P.char '='
    P.spaces
    v <- P.try lconfig <|> val
    P.spaces
    return (k, v)

lconfig = do
    P.char '['
    P.spaces
    c <- config
    P.char ']'
    P.spaces
    return $ Map c

val = liftM Val $ P.manyTill P.anyChar (P.char '\n')

key = do
    l <- P.letter
    r <- P.many $ P.letter <|> P.digit <|> P.oneOf "_-"
    return (l : r)

-- vim: set expandtab:
