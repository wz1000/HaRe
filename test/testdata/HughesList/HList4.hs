module Main where

exponents :: Int -> [Int]
exponents base = base : (exponents (2*base))

main = putStrLn "hello"
