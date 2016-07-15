module HandWritten where

import MyData
import InvUtil

invsnoc (Cons a Nil) = (Nil,a)
invsnoc (Cons a v) =
    let (x,b) = invsnoc v
    in (Cons a x,b)

-- data Q a b c d e 
--     = Q1 a
--     | Q2 b 
--     | Q3 c
--     | Q4 d
--     | Q5 e

invsnocO (Cons a x) = h a x
    where h a Nil = (Nil,a)
          h a v   = 
              let (x,b) = invsnocO v
              in (Cons a x,b)
         

invsnoc2 x = case trav1 x of
               Q1 (v,b) -> (v,b)
    where
      trav1 (Cons t1 t2) =
          case (trav2 t1,trav3 t2) of
            (Q2 (_,b), Q3 ())    -> Q1 (Nil,b)
            (Q2 (a,_), Q4 (x,b)) -> Q1 (Cons a x,b)
      trav2 x = Q2 (x,x)
      trav3 Nil = Q3 ()
      trav3 (Cons t1 t2) =
          case (trav2 t1,trav3 t2) of
            (Q2 (_,b), Q3 ())    -> Q4 (Nil,b)
            (Q2 (a,_), Q4 (x,b)) -> Q4 (Cons a x,b)


dl Nil         = Nil
dl (Cons x xs) = Cons x (Cons x (dl xs))

invdl :: Eq a => List a -> List a 
invdl Nil = Nil
invdl (Cons x (Cons y xs)) =
    if x == y then 
        Cons x (invdl xs)
    else
        error "Inconsistent"

data Q a b c d e f g 
    = Q1 a
    | Q2 b 
    | Q3 c
    | Q4 d
    | Q5 e
    | Q6 f
    | Q7 g
    | QDead

instance Show (Q a b c d e f g) where
    show (Q1 _) = "Q1"
    show (Q2 _) = "Q2"
    show (Q3 _) = "Q3"
    show (Q4 _) = "Q4"
    show (Q5 _) = "Q5"
    show (Q6 _) = "Q6"
    show (Q7 _) = "Q7"
    show (QDead) = "QDead"

invdoublelist x = case trav1 x of
                    Q1 x -> x 
    where
      trav1 (Nil) = Q1 Nil
      trav1 (Cons t1 t2) =
          case (trav2 t1, trav3 t2) of
            (Q2 x, Q3 (y,xs)) -> Q1 (Cons (if x == y then x else error "") xs)
      trav2 x = Q2 x
      trav3 (Cons t1 t2) =
          case (trav2 t1, trav4 t2) of
            (Q2 x, Q4 xs) -> Q3 (x,xs)
      trav4 (Nil) = Q4 Nil
      trav4 (Cons t1 t2) =
          case (trav2 t1, trav5 t2) of
            (Q2 x, Q5 (y,xs)) -> Q4 (Cons (if x == y then x else error "") xs)
      trav5 (Cons t1 t2) =
          case (trav2 t1, trav4 t2) of
            (Q2 x, Q4 xs) -> Q5 (x,xs)



invtreelist x = case trav1 x of
                  Q1 x -> x 
    where
      trav1 (Cons x y) =
          case (trav2 x, trav3 y) of
            (Q2  n, Q3 ()) -> Q1 BL
            (Q2  n, Q5 (r,rs)) ->
                let (x,y) = invapp(Pair n (Cons r rs))
                    l'    = invtreelist x
                    r'    = invtreelist y
                in Q1 (BN l' r')
            (Q4  n, Q5 (r,rs)) ->
                let (x,y) = invapp(Pair n (Cons r rs))
                    l'    = invtreelist x
                    r'    = invtreelist y
                in Q1 (BN l' r')
      trav2 (Nil)       = Q2 Nil
      trav2 x           = Q4 x 
      trav3 Nil         = Q3 ()
      trav3 (Cons r rs) = 
          case (trav4 r, trav5 rs) of
            (Q6 r, Q7 rs) -> Q5 (r,rs)
      trav4 x = Q6 x
      trav5 x = Q7 x 
invapp :: Pair (List B) (List x) -> (List x,List x)
invapp x = case trav1 x of
             Q1 x -> x 
    where
      trav1 (Pair x y) =
          case (trav2 x, trav3 y) of
            (Q1 (),Q1 (ys)) -> Q1 (Nil,ys)
            (Q1 (),Q2 (ys,_)) -> Q1 (Nil,ys)
            (Q2  n,Q2 (_,(x,zs))) ->
                let (xs,ys) = invapp (Pair n zs)
                in Q1 (Cons x xs,ys)
      trav2 Nil = Q1 ()
      trav2 (Cons x y) = 
          case (trav4 x, trav5 y) of
            (Q1 (), Q1  _)   -> Q2 (Nil)
            (Q2 (), Q1  x)   -> Q2 (Cons B0 x)
            (Q2 (), Q2  x)   -> Q2 (Cons B0 x)
            (Q1 (), Q3(_,x)) -> Q2 (Cons B1 x)
            (Q2 (), Q3(x,_)) -> Q2 (Cons B0 x)
      trav3 (t@(Cons t1 t2)) =
          case (trav6 t1, trav7 t2) of
            (Q1 x, Q1 zs) -> Q2(t,(x,zs))
      trav3 t = Q1 t
      trav6 t = Q1 t
      trav7 t = Q1 t 
      trav4 (B0) = Q1 ()
      trav4 (B1) = Q2 ()
      trav5 (Nil) = Q1 Nil
      trav5 (t@(Cons x y)) =
          case (trav4 x, trav5 y) of
            (Q1 (), Q1 _)    -> Q3 (t,Nil)
            (Q2 (), Q1  x)   -> Q3 (t,Cons B0 x)
            (Q2 (), Q2  x)   -> Q3 (t,Cons B0 x)
            (Q1 (), Q3(_,x)) -> Q3 (t,Cons B1 x)
            (Q2 (), Q3(x,_)) -> Q3 (t,Cons B0 x)
            x                -> error $ show t
      trav5 t     = Q2 t
            

runlength_expand Nil = Nil
runlength_expand (Cons (Pair symb rec) xs) =
    multiply symb (incB(rec)) (runlength_expand xs)
    where
      incB Nil          = Cons B1 Nil
      incB (Cons B0 xs) = (Cons B1 xs)
      incB (Cons B1 xs) = Cons B0 (incB xs)
      multiply s Nil x = x
      multiply s (Cons B0 xs) x = 
          let f = multiply s xs 
          in f (f x)
      multiply s (Cons B1 xs) x =
          let f = multiply s xs
          in f (f (Cons s x))


parseSExp x = let (r,MSTokEOS) =  parseCar x in r 
parseCar (Str x t)       = (Symbol x, t)
parseCar (LPar (RPar t)) = (SNil,     t)
parseCar (LPar t)        = 
    let (p1,r1) = parseCar t 
        (p2,r2) = parseCdr r1
    in (SCons p1 p2, r2)
parseCdr (Dot (Str x (RPar t))) = (Symbol x, t)
parseCdr (RPar t)               = (SNil,t)
parseCdr x = 
    let (p1,r1) = parseCar x 
        (p2,r2) = parseCdr r1 
    in (SCons p1 p2, r2)

parseBin t = let (r,EOS) = f t in r 
    where
      f (L (R z)) = (BL,z)
      f (L z) =
          let (l,s1) = f z 
              (r,R s2) = f s1
          in (BN l r,s2)

my_unzip Nil = (Nil,Nil)
my_unzip (Cons (Pair a b) x) =
  let (s,t) = my_unzip x 
  in (Cons a s, Cons b t)

