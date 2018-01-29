module Main where

import Renaming.B3
import Renaming.C3
import Renaming.D3

maim :: Tree Int ->Bool
maim t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B3.myFringe t)+sumSquares (Renaming.C3.myFringe t))

main = putStrLn "hello"
