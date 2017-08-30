module HList1 where
import Data.DList

data Tree a = Leaf
            | Node (Tree a) a (Tree a)

enumerate :: Tree a -> DList a
enumerate Leaf = empty
enumerate (Node left x right) = (fromList [x]) `append` (enumerate left) `append` (enumerate right)
