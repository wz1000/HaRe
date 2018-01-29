module Main where

interleave :: a -> [a] -> [a]
interleave e lst = (head lst) : e : interleave e (tail lst)

main = putStrLn "hello"
