module Main where

import Data.List
import Data.Maybe (mapMaybe)
import System.IO

import Ants
import Brain (doTurn)

-- | This runs the game
main :: IO ()
main = game doTurn

-- vim: set expandtab:
