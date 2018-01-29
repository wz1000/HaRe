module Main where

import LiftOneLevel.C1

maim :: [[Integer]] -> Integer
maim xs = case xs of
             [] -> 0
             [x:xs] -> x^pow + sumSquares1 xs

main = putStrLn "hello"
