module HList4 where

exponents :: Int -> [Int]
exponents base = base : (exponents (2*base))
