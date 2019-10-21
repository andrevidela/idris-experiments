module Lists

import Data.Vect

%access public export

%default total

data ListLength : Nat -> List a -> Type where
  Empty : ListLength Z []
  Cons : (e : a) -> ListLength n l -> ListLength (S n) (e :: l)

getLength : (l : List a) -> ListLength (length l) l
getLength [] = Empty
getLength (x :: xs) = Cons x $ getLength xs

listLengthToVect : {ls : List a} -> ListLength l ls -> Vect l a
listLengthToVect Empty = []
listLengthToVect (Cons e x) = e :: listLengthToVect x

equalizeLengths : {a : Type} -> {l1, l2 : List a}
               -> ListLength n1 l1 -> ListLength n2 l2
               -> (element : a)
               -> {auto prf : n1 `LTE` n2}
               -> (Vect n2 a, Vect n2 a)
equalizeLengths Empty y e {prf = LTEZero} {n2}= (replicate n2 e, listLengthToVect y)
equalizeLengths (Cons l x) (Cons r y) e {prf = (LTESucc z)} =
  let (ls, rs) = equalizeLengths x y e in (l :: ls, r :: rs)

equaliseLists : (l : List a) -> (r : List a) -> {prf : length l `LTE` length r}
             -> a -> (Vect (length r) a, Vect (length r) a)
equaliseLists l r x = equalizeLengths (getLength l) (getLength r) x

mkLengthProof : (l : List a) -> (r : List a) -> Either (length l `LTE` length r)
                                                       (length r `LTE` length l)
mkLengthProof [] [] = Left LTEZero
mkLengthProof [] (x :: xs) = Left LTEZero
mkLengthProof (x :: xs) [] = Right LTEZero
-- isn't this just bimap?
mkLengthProof (x :: xs) (y :: ys) with (mkLengthProof xs ys)
  mkLengthProof (x :: xs) (y :: ys) | (Left l) = Left (LTESucc l)
  mkLengthProof (x :: xs) (y :: ys) | (Right r) = Right (LTESucc r)

vectLengthProof : (l : Vect n a) -> (r : Vect m a) -> Either (n `LTE`m) (m `LTE` n)
vectLengthProof [] [] = Left LTEZero
vectLengthProof [] (x :: xs) = Left LTEZero
vectLengthProof (x :: xs) [] = Right LTEZero
vectLengthProof (x :: xs) (y :: ys) with (vectLengthProof xs ys)
  vectLengthProof (x :: xs) (y :: ys) | (Left l) = Left (LTESucc l)
  vectLengthProof (x :: xs) (y :: ys) | (Right r) = Right (LTESucc r)

extendVect : Vect (S n) a -> {prf : S n `LTE` m} -> Vect m a
extendVect (x :: []) {m} = replicate m x
extendVect (x :: (y :: xs)) {prf=LTESucc k} = x :: extendVect (y :: xs) {prf=k}

maxLength : Vect n a -> Vect m a -> Nat
maxLength _ _ {n} {m} = max n m

VectPair : Nat -> Type -> Type
VectPair n a = (Vect n a, Vect n a)

mkMaxProof : (l, r : Nat) -> Either (l `LTE` r) (r `LTE` l)
mkMaxProof Z r = Left LTEZero
mkMaxProof (S k) Z = Right LTEZero
mkMaxProof (S k) (S j) with (mkMaxProof k j)
  mkMaxProof (S k) (S j) | (Left l) = Left (LTESucc l)
  mkMaxProof (S k) (S j) | (Right r) = Right (LTESucc r)


extendBoth : (l : Vect (S n) a) -> (r : Vect (S m) a)
          -> Either (VectPair (S n) a) (VectPair (S m) a)
extendBoth l r {n} {m} with (mkMaxProof (S n) (S m))
  extendBoth l r {n} {m} | (Left x) = Right (extendVect l {prf = x}, r)
  extendBoth l r {n} {m} | (Right x) = Left (l, extendVect r {prf = x})

extendListsToVect : (l, r : List a) -> a -> (m ** (VectPair m a))
extendListsToVect [] [] x = (Z ** ([], []))
extendListsToVect [] xs x = (length xs ** (replicate (length xs) x, fromList xs))
extendListsToVect xs [] x = (length xs ** (fromList xs, replicate (length xs) x))
extendListsToVect (y :: xs) (z :: ys) x = case extendBoth (fromList (x :: xs)) (fromList (y :: ys)) of
                                               Left (ls, rs) => (S (length xs) ** (ls, rs))
                                               Right (ls, rs) => (S (length ys) ** (ls, rs))

extendBothLists : (l, r : List a) -> a -> (List a, List a)
extendBothLists [] [] e = ([], [])
extendBothLists [] ys@(x :: xs) e = (replicate (length ys) e, ys)
extendBothLists ys@(x :: xs) [] e = (ys, replicate (length ys) e)
extendBothLists (x :: xs) (y :: ys) e = case extendBoth (fromList (x :: xs)) (fromList (y :: ys)) of
                                             Left (ls, rs) => (toList ls, toList rs)
                                             Right (ls, rs) => (toList ls, toList rs)
