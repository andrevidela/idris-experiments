module Karatsuba

import Data.Vect


data Bit = O | I

Show Bit where
  show O = "0"
  show I = "1"

Eq Bit where
  O == O = True
  I == I = True
  _ == _ = False

BitVect : Nat -> Type
BitVect n = Vect n Bit

multiply : Bit -> Bit -> Bit
multiply I I = I
multiply _ _ = O

bitSign : Bit -> Bit -> Bit
bitSign I O = I
bitSign O I = I
bitSign O O = O
bitSign I I = O

flip : Bit -> Bit
flip I = O
flip O = I

||| Add two bits together and return carry (Sum, Carry)
addBit2 : Bit -> Bit -> (Bit, Bit)
addBit2 O O = (O, O)
addBit2 O I = (I, O)
addBit2 I O = (I, O)
addBit2 I I = (O, I)

||| Add three bits together and return (Sum, Carry)
addBits3 : Bit -> Bit -> Bit -> (Bit, Bit)
addBits3 O O O = (O, O)
addBits3 O O I = (I, O)
addBits3 O I O = (I, O)
addBits3 I O O = (I, O)
addBits3 O I I = (O, I)
addBits3 I O I = (O, I)
addBits3 I I O = (O, I)
addBits3 I I I = (I, I)

powNat : Int -> Nat -> Int
powNat v Z = 1
powNat v (S n) = v * (v `powNat` n)

lsbToInt : BitVect n -> Int
lsbToInt = snd . (foldl combine (Z, the Int 0))
  where
    combine : (Nat, Int) -> Bit -> (Nat, Int)
    combine (count, acc) O = (S count, acc)
    combine (count, acc) I = (S count, acc + (2 `powNat` count))

total
intToLsb : Int -> (k ** BitVect k)
intToLsb n = assert_total $ intToLsb' (abs n)
  where
    intToLsb' : Int -> DPair Nat (\n => BitVect n)
    intToLsb' i = let d = i `div` 2
                      m = i `mod` 2
                      b = if m == 0 then O else I
                   in if d == 0
                         then (S Z ** [b])
                         else let (r ** rs) = intToLsb' d
                               in (S r ** b :: rs)

||| This addition returns the last bit separated from the others
additionLSBCarry : {0 n : Nat} -> BitVect n -> BitVect n -> (Bit, BitVect n)
additionLSBCarry lhs rhs = addWithCarry lhs rhs O
  where
    addWithCarry : {0 n : Nat} -> Vect n Bit -> Vect n Bit -> Bit -> (Bit, Vect n Bit)
    addWithCarry [] [] z = (z, [])
    addWithCarry (x :: xs) (y :: ys) z =
      let (s, c) = addBits3 x y z
          (carry, rest) = addWithCarry xs ys c
       in (carry, s :: rest)

||| This addition always has a carry at the end
additionLSB : {0 n : Nat} -> BitVect n -> BitVect n -> BitVect (S n)
additionLSB x y = addWithCarry x y O
  where
    addWithCarry : {0 n : Nat} -> Vect n Bit -> Vect n Bit -> Bit -> Vect (S n) Bit
    addWithCarry [] [] z = [z]
    addWithCarry (x :: xs) (y :: ys) z = let (s, c) = addBits3 x y z in s :: addWithCarry xs ys c

||| This addition assumes the Most Significant Bit first layout
additionMSB : BitVect n -> BitVect n -> BitVect (S n)
additionMSB x y = reverse $ additionLSB (reverse x) (reverse y)


||| Given an non-empty vector, return the last element of the vector
last : Vect (S n) a -> a
last (x :: []) = x
last (x :: (y :: ys)) = Karatsuba.last (y :: ys)

||| Given a non-empty vector, return all but the last element of the vector
dropLast : Vect (S n) a -> Vect n a
dropLast (x :: []) = []
dropLast (x :: (y :: xs)) = x :: dropLast (y :: xs)

||| Given a non-empty vector, split the vector at the last element
splitLast : Vect (S n) a -> (a, Vect n a)
splitLast (x :: []) = (x, [])
splitLast (x :: (y :: xs)) = let (last, ys) = splitLast (y :: xs) in
                                 (last, x :: ys)

||| Two's complement only works on vector f size at least one
twosComplement : {n : Nat} -> BitVect (S n) -> BitVect (S (S n))
twosComplement (x :: xs) {n = S (S n)} = map flip (x :: xs) `additionLSB` (I :: replicate (S (S n)) O)

||| Two's completemebnt but returns the last extra bit separately
twoComplementWithCarry : {n : Nat} -> BitVect (S n) -> (Bit, BitVect (S n))
twoComplementWithCarry x {n} = map flip x `additionLSBCarry` (I :: replicate n O)

sign : Integer -> Bit
sign i = if i < 0 then I else O

main : IO ()
main = do putStrLn "addition bit vectors"
          let (3 ** seven) = intToLsb 7
          let (3 ** six) = intToLsb 6
          let n = lsbToInt $ additionLSB seven six
          putStrLn $ "7 + 6 = "  ++ (show n)

