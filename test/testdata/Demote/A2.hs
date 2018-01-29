module Main where

import Demote.C2

maim xs = case xs of
             [] -> 0
             [x:xs] -> x^pow + sumSquares xs

main = putStrLn "hello"
