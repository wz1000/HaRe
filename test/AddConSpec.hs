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
      r <- ct $ addConstructor defaultTestSettings testOptions "./AddCon/A1.hs" ["C2","c"] (3,1)
      -- r <- ct $ addConstructor logTestSettings testOptions "./AddCon/A1.hs" ["C2,"c"] (3,1)

      r' <- ct $ mapM makeRelativeToCurrentDirectory r

      r' `shouldBe` [ "AddCon/A1.hs"
                    ]

      diffA <- ct $ compareFiles "./AddCon/A1.expected.hs"
                                 "./AddCon/A1.refactored.hs"
      diffA `shouldBe` []

    -- -------------------
