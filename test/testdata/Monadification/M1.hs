module M1 where

f :: [a] -> b -> b
f [] y = y
f x y = f (g x) (h y)

g :: [a] -> [a]
g x = tail x

h :: a -> a
h x = id x 
