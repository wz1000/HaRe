-- Adapted from https://gist.github.com/23Skidoo/4487926
module HughesList.DList
       where

import Data.Char (isSpace)
import Prelude hiding (reverse)

newtype DList a = DList ([a] -> [a])

fromList :: [a] -> DList a
fromList l = DList (l ++)

toList :: DList a -> [a]
toList (DList f) = f []

singleton :: a -> DList a
singleton a = DList (a:)

append :: DList a -> DList a -> DList a
append (DList f) (DList g) = DList (f . g)

reverse :: [a] -> [a]
reverse l = rev l []
  where
    rev :: [a] -> [a] -> [a]
    rev [] y     = y
    rev (x:xs) y = rev xs (x:y)

reverseH :: DList a -> DList a
reverseH (DList f) = DList (reverse . f)

fields :: String -> [String]
fields [] = []
fields (c:l) | isSpace c = fields l
             | otherwise = word (c:) l

word :: (String -> String) -> String -> [String]
word w (c:l) | not (isSpace c) = word (w . (c:)) l
word w l                       = w [] : fields l
