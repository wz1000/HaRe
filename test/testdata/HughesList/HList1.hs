module Main where

data Tree a = Leaf
            | Node (Tree a) a (Tree a)

enumerate :: Tree a -> [a]
enumerate Leaf = []
enumerate (Node left x right) = (enumerate left) ++ [x] ++ (enumerate right)

main = putStrLn "hello"
