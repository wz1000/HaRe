module Main where

import AddOneParameter.C1

import AddOneParameter.D1

sumSq xs = sum (map (sq sq_f) xs) + sumSquares xs + sumSquares1 xs

maim :: Int
maim = sumSq [1..4]

main = putStrLn "hello"
