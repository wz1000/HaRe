module Main where

import RmOneParameter.D2

sumSq xs ys= sum (map sq xs) + sumSquares xs

maim = sumSq [1..4]

main = putStrLn "hello"

