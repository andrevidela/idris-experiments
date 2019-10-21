module Karatsuba

import Lists
import Data.Vect

%access public export

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


record SignedBitVect (n : Nat) where
  constructor MkSignedVect
  ||| O means positive I means negative
  sign : Bit
  vect : BitVect n

record SignedBit where
  constructor MkSigned
  ||| O means positive I means negative
  sign : Bit
  list : List Bit

bitMult : Bit -> Bit -> Bit
bitMult I I = I
bitMult _ _ = O

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

lsbToInt : BitVect n -> Int
lsbToInt = snd . (foldl combine (0, 0))
  where
    combine : (Nat, Int) -> Bit -> (Nat, Int)
    combine (count, acc) O = (S count, acc)
    combine (count, acc) I = (S count, acc + (2 `pow` count))

lsbToInt' : List Bit -> Int
lsbToInt' xs = lsbToInt (fromList xs)

squareRoot : Nat -> Nat
squareRoot n = sqrtAcc n 0
  where
    sqrtAcc : Nat -> Nat -> Nat
    sqrtAcc n acc = if acc * acc > n then acc else sqrtAcc n (S acc)

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


additionLSBCarry : BitVect n -> BitVect n -> (Bit, BitVect n)
additionLSBCarry lhs rhs = addWithCarry lhs rhs O
  where
    addWithCarry : Vect n Bit -> Vect n Bit -> Bit -> (Bit, Vect n Bit)
    addWithCarry [] [] z = (z, [])
    addWithCarry (x :: xs) (y :: ys) z =
      let (s, c) = addBits3 x y z
          (carry, rest) = addWithCarry xs ys c
       in (carry, s :: rest)

additionLSB : BitVect n -> BitVect n -> BitVect (S n)
additionLSB x y = addWithCarry x y O
  where
    addWithCarry : Vect n Bit -> Vect n Bit -> Bit -> Vect (S n) Bit
    addWithCarry [] [] z = [z]
    addWithCarry (x :: xs) (y :: ys) z = let (s, c) = addBits3 x y z in s :: addWithCarry xs ys c

additionMSB : BitVect n -> BitVect n -> BitVect (S n)
additionMSB x y = reverse $ additionLSB (reverse x) (reverse y)

generateMutlVectors : BitVect n -> BitVect m -> Vect m (BitVect n)
generateMutlVectors origin = map (select origin)
  where
    select : BitVect n -> Bit -> BitVect n
    select vs O {n} = replicate n O
    select vs I = vs

proofNatSucc : n + 1 = S n
proofNatSucc {n = Z} = Refl
proofNatSucc {n = (S k)} = cong proofNatSucc

proofNat2Succ : n + 2 = S (S n)
proofNat2Succ {n = Z} = Refl
proofNat2Succ {n = (S Z)} = Refl
proofNat2Succ {n = (S (S k))} = cong {f=S} (cong {f=S} proofNat2Succ)

total
sumarize : {n : Nat} -> Vect (S m) (BitVect n) -> BitVect (n + (S m))
sumarize (x :: []) {n} = x ++ [O]
sumarize (x :: (y :: [])) {n} =
  let y' = O :: x
      x' = y ++ [O]
      v =  additionLSB y' (rewrite sym $ proofNatSucc {n} in x')
   in rewrite proofNat2Succ {n} in v
sumarize (x :: xs) {n} {m=S (S m)} =
  let v = sumarize (xs)
      r = leftPad x {len=m}
   in rewrite sym $ plusSuccRightSucc n (S (S m))
   in v `additionLSB` r
  where
    ||| Like leftpad but better
    leftPad : Vect k Bit -> Vect (k + (S (S len))) Bit
    leftPad vs {k} {len} =
      rewrite sym $ proofNat2Succ {n=len} in
      replace {P=flip Vect Bit} (sym $ plusCommutative k (len + 2)) $
      replicate (len + 2) O ++ vs


multiplicationLSB : BitVect n -> BitVect (S m) -> BitVect (n + (S m))
multiplicationLSB x y = sumarize $ generateMutlVectors (reverse x) y

maxLength : List a -> List a -> Nat
maxLength xs ys = max (length xs) (length ys)

MaxLengthVect : List a -> List a -> Type
MaxLengthVect ls rs = let m = maxLength ls rs in (Vect m a, Vect m a)


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

additionLSBList : List Bit -> List Bit -> List Bit
additionLSBList xs ys = let (l ** (lx, ly)) = extendListsToVect xs ys O
                            sum = additionLSB lx ly
                         in case Karatsuba.last (sum) of
                                 O => take (length sum `minus` 1) (toList sum)
                                 I => toList $ sum

total
additionLSBListCarry : List Bit -> List Bit -> (Bit, List Bit)
additionLSBListCarry xs ys = let (_ ** (lx, ly)) = extendListsToVect xs ys O
                                 (carry, sum) = assert_total $ additionLSBCarry lx ly
                              in (carry, toList sum)


multiplicationLSBList : List Bit -> List Bit -> List Bit
multiplicationLSBList xs ys = case extendListsToVect xs ys O of
                                (Z ** ([], [])) => []
                                (S n ** (lx, ly)) => toList $ multiplicationLSB lx ly
twosComplement : BitVect (S n) -> BitVect (S (S n))
twosComplement (x :: xs) {n = S (S n)} = map flip (x :: xs) `additionLSB` (I :: replicate (S (S n)) O)

twoComplementWithCarry : BitVect (S n) -> (Bit, BitVect (S n))
twoComplementWithCarry x {n} = map flip x `additionLSBCarry` (I :: replicate n O)

twosComplementCarry : List Bit -> (Bit, List Bit)
twosComplementCarry [] = (I, [])
twosComplementCarry (x :: xs) = map toList $ twoComplementWithCarry $ fromList (x :: xs)

vectToSigned : Vect (S n) Bit -> SignedBit
vectToSigned (x :: []) = MkSigned x []
vectToSigned (x :: xs) = MkSigned (Karatsuba.last (x :: xs)) (toList $ dropLast (x :: xs))

listToSigned : List Bit -> SignedBit
listToSigned [] = MkSigned O []
listToSigned (x :: xs) = vectToSigned (fromList (x :: xs))

flip' : SignedBit -> SignedBit
flip' (MkSigned sign list) = MkSigned (flip sign) (map flip list)


additionSigned : SignedBit -> SignedBit -> SignedBit
additionSigned (MkSigned sl ls) (MkSigned sr rs) =
  let (c1, sum) = ls `additionLSBListCarry` rs
      (s, overflow) = addBits3 sl sr c1
   in MkSigned s sum

multiplicationSigned : SignedBit -> SignedBit -> SignedBit
multiplicationSigned (MkSigned s1 ls) (MkSigned s2 rs) = MkSigned (bitSign s1 s2) (multiplicationLSBList ls rs)

sign : Integer -> Bit
sign i = if i < 0 then I else O

multiply : Bit -> Bit -> Bit
multiply I I = I
multiply _ _ = O

Num SignedBit where
  (+) = additionSigned
  (*) = multiplicationSigned
  fromInteger x = let asInt = fromInteger x
                      (_ ** bits) = intToLsb asInt
                   in MkSigned (sign x) (toList bits)


Neg SignedBit where
  negate (MkSigned sign val) = let (c, bits) = twosComplementCarry val
                                   (v, _) = c `addBit2` (flip sign)
                                in MkSigned v bits
  (-) l r = l + (negate r)

signedToInt : SignedBit -> Int
signedToInt (MkSigned O list) = lsbToInt' list
signedToInt m@(MkSigned I list) = negate $ signedToInt $ negate m

total
intToSignedListBit : Integer -> List Bit
intToSignedListBit x =
  if x < 0
     then Basics.snd $ twosComplementCarry $ positiveIntToListBit (abs x) [O]
     else positiveIntToListBit x [O]
  where
    total
    positiveIntToListBit : Integer -> List Bit -> List Bit
    positiveIntToListBit i xs = let (_ ** bits) = intToLsb (fromInteger i) in toList bits ++ xs

mutual
  total
  karatsuba : List Bit -> List Bit -> List Bit
  karatsuba [] _ = []
  karatsuba (x :: xs) [] = []
  karatsuba (x :: []) (y :: []) = [x `multiply`  y]
  karatsuba left right =
    let longest = the Nat $ max (List.length left) (List.length right)
        half = assert_total $ longest `divNat` 2 -- divNat is safe since its right argument is > 0
        x_h = take half left
        x_l = drop half left
        y_h = take half right
        y_l = drop half right
        a = assert_total $ karatsuba x_h y_h
        d = assert_total $ karatsuba x_l y_l
        e = assert_total $ karatsuba (x_h + x_l) (y_h + y_l) - a - d
    in (a ++ replicate longest O) + (e ++ replicate half O) + d

  Num (List Bit) where
    (+) x y = snd $ additionLSBListCarry x y
    (*) x y = karatsuba x y
    fromInteger x = intToSignedListBit x


  Neg (List Bit) where
    negate ls = snd $ twosComplementCarry ls
    (-) l r = l + (negate r)

