module Main where

import Data.List
import Data.Maybe (mapMaybe)
import System.IO

import Ants
import Brain (doTurn)

-- | Picks the first "passable" order in a list
-- returns Nothing if no such order exists
tryOrder :: World -> [Order] -> Maybe Order
tryOrder w = find (passable w)

-- | Generates orders for an Ant in all directions
generateOrders :: Ant -> [Order]
generateOrders a = map (Order a) [North .. West]

-- | This runs the game
main :: IO ()
main = game doTurn

-- vim: set expandtab:
