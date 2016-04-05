module AddConSpec (main, spec) where

import           Test.Hspec

import Language.Haskell.Refact.Refactoring.AddCon

import TestUtils

import System.Directory

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do

  describe "Adding" $ do
    it "addConstructor in A1" $ do
      r <- ct $ addConstructor defaultTestSettings testOptions "./AddCon/A1.hs" ["C2","c"] (3,12)
      -- r <- ct $ addConstructor logTestSettings testOptions "./AddCon/A1.hs" ["C2","c"] (3,12)

      r' <- ct $ mapM makeRelativeToCurrentDirectory r

      r' `shouldBe` [ "AddCon/A1.hs"
                    ]

      diffA <- ct $ compareFiles "./AddCon/A1.expected.hs"
                                 "./AddCon/A1.refactored.hs"
      diffA `shouldBe` []

    -- -------------------

{-

TestCases{refactorCmd="refacAddCon",
positive=[(["A1.hs"], ["C2","c","3","12"]),
          (["A2.hs"], ["C2","Int","3","12"]),
          (["A3.hs"], ["C2","Int","n","3","12"]),
          (["A4.hs"], ["C2","b","3","12"]),
          (["A5.hs"], ["T2","Int","3","12"]),
          (["A6.hs"], ["T3","a","3","12"]),
          (["B1.hs"], ["C4","Float","3","16"]),
          (["B2.hs"], ["C4","Float","3","16"]),
          (["Case1.hs"], ["C3","Int","3","12"]),
          (["Case2.hs"], ["C3","Int","3","12"]),
          (["Tuple1.hs"], ["T3","b","4","12"]),
          (["Tuple2.hs"], ["T3","b","4","12"])
          ],
negative=[
]


}
-}
