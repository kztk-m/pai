{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, FlexibleInstances #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module MyData where

import InvUtil

data Nat = Z | S Nat deriving (Eq,Ord,Show)

instance Default Nat where
    something = Z

instance Num Nat where
  Z   + m = m
  S n + m = S (n + m)

  Z   * m = Z
  S n * m = m + (n * m)

  abs n   = n
  
  signum Z = Z
  signum _ = S Z

  fromInteger 0 = Z
  fromInteger n = S (fromInteger (n-1))

  m - Z = m
  S m - S n = m - n 
  Z - n = Z

-- int2nat 0     
--     = Z
-- int2nat (n+1) | n >= 0 
--     = S (int2nat n)

int2nat :: (Eq n, Num n) => n -> Nat 
int2nat n = f n Z 
    where f n x | seq x True = if n == 0 then x else f (n-1) (S x)
          

{-# INLINABLE[1] nat2int #-}
nat2int :: Num n => Nat -> n 
nat2int n = f n 0
    where f n x | seq x True = case n of 
                                 Z   -> x
                                 S m -> f m (1+x)


data List x 
    = Nil
    | Cons x (List x) 
      deriving (Eq,Ord,Show)

instance Default (List a) where
    something = Nil


data B = B0 | B1 deriving (Eq,Ord,Show)

int2lsb :: Int -> List B 
int2lsb 0 = Cons B0 Nil
int2lsb 1 = Cons B1 Nil
int2lsb n = 
    if n `mod` 2 == 0 then
        Cons B0 (int2lsb (n `div` 2))
    else
        Cons B1 (int2lsb (n `div` 2))

{-# INLINABLE[1] lsb2int #-}
lsb2int :: List B -> Int 
lsb2int (Cons B0 Nil) = 0
lsb2int (Cons B1 Nil) = 1
lsb2int (Cons B0 x) = 2 * lsb2int x 
lsb2int (Cons B1 x) = 1 + (2 * lsb2int x)



instance Default B where
    something = B0

fromHsList x = foldr Cons Nil x

toHsList Nil        = []
toHsList (Cons a x) = a:toHsList x

data MParen = L MParen | R MParen | EOS

data SExp = Symbol String | SNil | SCons SExp SExp deriving (Ord,Eq,Show)
-- data STok = LPar | RPar | Dot | Str String deriving (Ord,Eq,Show)

data MSTok = LPar MSTok | RPar MSTok | Dot MSTok 
           | Str  String MSTok 
           | MSTokEOS

data BS = BN BS BS | BL deriving (Show,Eq)

data Bin x
    = BNode x (Bin x) (Bin x)
    | BLeaf 
  deriving (Eq, Show)

data LBin x 
    = LFork (LBin x) (LBin x)
    | LTip  x
  deriving (Eq, Show)

data Pair x y = Pair x y
                deriving (Eq,Ord,Show)
data Pair3 x y z = Pair3 x y z
                 deriving (Eq,Ord,Show)

fromHsPair (x,y)      = Pair x y
toHsPair   (Pair x y) = (x,y)


data Diffs a = Del | Ins a | Keep

{-# RULES
"IntNatInt"  forall x. nat2int (int2nat x) = x
"IntLSBInt"  forall x. lsb2int (int2lsb x) = x 
  #-}
