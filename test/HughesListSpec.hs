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
      pendingWith "need to get this to work"
      {-
      res <- ct $ hughesList defaultTestSettings testOptions "./HughesList/HList1.hs" "enumerate" (7,1) 2
      -- res <- ct $ hughesList logTestSettings testOptions "./HughesList/HList1.hs" "enumerate" (7,1) 2
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/HList1.hs"]
      diff <- ct $ compareFiles "./HughesList/HList1.refactored.hs"
                                "./HughesList/HList1.hs.expected"
      diff `shouldBe` []
      -}

    it "Another simple example but there is a client function that DList values need to be converted back to lists" $ do
      pendingWith "need to get this to work"
      {-
      res <- ct $ hughesList defaultTestSettings testOptions "./HughesList/HList2.hs" "enumerate" (7,1) 2
      -- res <- ct $ hughesList logTestSettings testOptions "./HughesList/HList2.hs" "enumerate" (7,1) 2
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/HList2.hs"]
      diff <- ct $ compareFiles "./HughesList/HList2.refactored.hs"
                                "./HughesList/HList2.hs.expected"
      diff `shouldBe` []
      -}

    it "A really contrived example where the result type of a function is refactored to a DList" $ do
      pendingWith "need to get this to work"
      {-
      -- res <- ct $ hughesList logTestSettings testOptions "./HughesList/HList3.hs" "explode" (6,1) 3
      res <- ct $ hughesList defaultTestSettings testOptions "./HughesList/HList3.hs" "explode" (6,1) 3
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/HList3.hs"]
      diff <- ct $ compareFiles "./HughesList/HList3.refactored.hs"
                                "./HughesList/HList3.hs.expected2"
      diff `shouldBe` []
      -}

    it "Refactoring a recursive definition" $ do
      pendingWith "need to get this to work"
      {-
      res <- ct $ hughesList defaultTestSettings testOptions "./HughesList/HList4.hs" "exponents" (4,1) 2
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/HList4.hs"]
      diff <- ct $ compareFiles "./HughesList/HList4.refactored.hs"
                                "./HughesList/HList4.hs.expected"
      diff `shouldBe` []
      -}

    it "Simple refactoring using the fast subset of DList functions" $ do
      pendingWith "need to get this to work"
      {-
      res <- ct $ fastHughesList defaultTestSettings testOptions "./HughesList/FHList1.hs" "interleave" (3,1) 3
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/FHList1.hs"]
      diff <- ct $ compareFiles "./HughesList/FHList1.refactored.hs"
                                "./HughesList/FHList1.hs.expected"
      diff `shouldBe` []
      -}

    it "Explode example again this time using the fast functions only" $ do
      pendingWith "need to get this to work"
      {-
      res <- ct $ fastHughesList defaultTestSettings testOptions "./HughesList/FHList2.hs" "interleave" (6,1) 3
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["HughesList/FHList2.hs"]
      diff <- ct $ compareFiles "./HughesList/FHList2.refactored.hs"
                                "./HughesList/FHList2.hs.expected"
      diff `shouldBe` []
      -}
