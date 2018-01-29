module Main where

import Renaming.B5
import Renaming.C5
import Renaming.D5

maim :: Tree Int ->Bool
maim t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B5.myFringe t)+sumSquares (Renaming.C5.myFringe t))

main = putStrLn "hello"
