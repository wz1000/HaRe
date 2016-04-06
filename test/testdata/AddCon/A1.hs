module A1 where

data T a = C1 a

data T' a c = C1' a | C2' c

over :: (T b) -> b
over (C1 x) = x

