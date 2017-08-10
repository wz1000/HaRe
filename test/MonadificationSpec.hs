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
    it "Monadify simple evaluator" $ do
      res <- ct $ monadification logTestSettings testOptions "./Monadification/M1.hs"
      res' <- ct $ mapM makeRelativeToCurrentDirectory res
      res' `shouldBe` ["Monadification/M1.hs"]
      diff <- ct $ compareFiles "./Monadification/M1.refactored.hs"
                                "./Monadification/M1.hs.expected"     
      diff `shouldBe` []
