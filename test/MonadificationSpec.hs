module MonadificationSpec (main, spec) where

import Test.Hspec
import System.Directory
import TestUtils
import Language.Haskell.Refact.Refactoring.Monadification

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do
  describe "doMonadification" $ do
    it "Monadify simple functions" $ do
      res <- ct $ monadification defaultTestSettings testOptions "./Monadification/M1.hs" [(4,1),(11,1)]
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["Monadification/M1.hs"]
      diff <- ct $ compareFiles "./Monadification/M1.refactored.hs"
                                "./Monadification/M1.hs.expected"     
      diff `shouldBe` []
    it "Monadify simple evaluator" $ do
      res <- ct $ monadification logTestSettings testOptions "./Monadification/M2.hs" [(15,1)]
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["Monadification/M2.hs"]
      diff <- ct $ compareFiles "./Monadification/M2.refactored.hs"
                                "./Monadification/M2.hs.expected"     
      diff `shouldBe` []
