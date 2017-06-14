module FHList1 where

interleave :: a -> [a] -> [a]
interleave e lst = (head lst) : e : interleave e (tail lst)
