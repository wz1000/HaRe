module Main where

import Demote.C1

maim xs = case xs of
             [] -> 0
             [x:xs] -> x^pow + sumSquares xs

main = putStrLn "hello"
