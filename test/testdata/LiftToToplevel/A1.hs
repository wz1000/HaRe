module Main where

import LiftToToplevel.C1

maim xs = case xs of
             [] -> 0
             [x:xs] -> x^pow + sumSquares1 xs

main = putStrLn "hello"
