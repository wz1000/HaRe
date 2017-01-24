module HughesListSpec (main, spec) where

import Test.Hspec
import System.Directory
import TestUtils
import Language.Haskell.Refact.Refactoring.HughesList

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do
  describe "doHughesList" $ do
    it "Simplest example that rewrites a single function to use Hughes lists instead of standard ones." $ do
      res <- ct $ hughesList defaultTestSettings testOptions "./HughesList/HList1.hs" "enumerate" (7,1)
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/HList1.hs"]
      diff <- ct $ compareFiles "./HughesList/HList1.refactored.hs"
                                "./HughesList/HList1.hs.expected"
      diff `shouldBe` []
    it "Another simple example but there is a client function that DList values need to be converted back to lists" $ do
      res <- ct $ hughesList logTestSettings testOptions "./HughesList/HList2.hs" "enumerate" (7,1)
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/HList2.hs"]
      diff <- ct $ compareFiles "./HughesList/HList2.refactored.hs"
                                "./HughesList/HList2.hs.expected"     
      diff `shouldBe` []
