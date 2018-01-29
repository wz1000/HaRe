module Main where

import LiftOneLevel.C3 (anotherFun)
import LiftOneLevel.D3 (sumSquares)

maim = sumSquares [1..4] + anotherFun [1..4]

main = putStrLn "hello"
