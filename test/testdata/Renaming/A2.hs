module Main where

import Renaming.B2
import Renaming.C2
import Renaming.D2

maim :: Tree Int ->Bool
maim t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B2.myFringe t)+sumSquares (Renaming.C2.myFringe t))

main = putStrLn "hello"
