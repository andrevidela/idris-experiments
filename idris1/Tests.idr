module Tests

import Specdris.Spec
import Karatsuba


test : IO ()
test = spec $ do
  describe "conversion tests" $ do
    it "should convert to LSB" $
      the (List Bit) 3 `shouldBe` [I,I]
    it "should convert back from LSB" $
      lsbToInt' [I,O,O,I] `shouldBe` 9

  describe "addition tests" $ do
    it "should add with zero" $
      lsbToInt' ((the (List Bit) 3) + (the (List Bit) 0)) `shouldBe` (3 + 0)
    it "should add with one" $
      lsbToInt' ((the (List Bit) 3) + (the (List Bit) 1)) `shouldBe` (3 + 1)
    it "should be symetric" $
      lsbToInt' ((the (List Bit) 0) + (the (List Bit) 3)) `shouldBe` (0 + 3)

  describe "multiplication tests" $ do
    it "should multiply with zero" $ do
      lsbToInt' ((the (List Bit) 3) * (the (List Bit) 0))
        `shouldBe` 0
    it "should multiply with One" $ do
      lsbToInt' ((the (List Bit) 3) * (the (List Bit) 1))
        `shouldBe` 3
    it "should multiply with zero" $ do
      lsbToInt' ((the (List Bit) 3) * (the (List Bit) 0))
        `shouldBe` 0
    it "should multiply with self" $ do
      lsbToInt' ((the (List Bit) 3) * (the (List Bit) 3))
        `shouldBe` 9
    it "should multiply with other" $ do
      lsbToInt' ((the (List Bit) 3) * (the (List Bit) 4))
        `shouldBe` 12
  describe "substraction tests" $ do
    it "should negate numbers" $ do
      (signedToInt $ the SignedBit (-3)) `shouldBe` (-3)
    it "should add 0 to negative numbers" $ do
      (signedToInt $ the SignedBit (-3) + (the SignedBit 0)) `shouldBe` (-3)
    it "should subtract 0 to negative numbers" $ do
      (signedToInt $ the SignedBit (-3) - (the SignedBit 0)) `shouldBe` (-3)
    it "should return zero when substracting with itself" $ do
      (signedToInt $ the SignedBit 3 - the SignedBit 3) `shouldBe` 0
    it "should substract with one" $ do
      (signedToInt $ the SignedBit 3 - the SignedBit 1) `shouldBe` 2
    it "should add with one" $ do
      (signedToInt $ the SignedBit (-3) + the SignedBit 1) `shouldBe` (-2)
