module Main (main) where

import System.CPUTime
import MyData
import InvUtil
import System.Mem

import Text.Printf 

import System.Environment (getArgs)


-- import TestRunLength
import RUNLENGTH
import SNOC
import DOUBLELIST
import TREE2LIST
import TABA_REVERSE
import BIN2PEANO
import PEANO2BIN
import PRINT_SEXP
import SERIALIZE_BINTREE
import DOUBLE
import ZIPI


import Debug.Trace

class NFData a where
    rnf :: a -> ()
    rnf x = x `seq` ()

instance NFData Int 
instance NFData Integer
instance NFData Float
instance NFData Double

instance NFData Char
instance NFData Bool
instance NFData ()

instance (NFData a, NFData b) => NFData (a,b) where
  rnf (x,y) = rnf x `seq` rnf y


instance NFData a => NFData [a] where
  rnf [] = ()
  rnf (x:xs) = rnf x `seq` rnf xs


instance (NFData a, NFData b) => NFData (Pair a b) where
  rnf (Pair x y) = rnf x `seq` rnf y
    
instance NFData a => NFData (List a) where
    rnf Nil = ()
    rnf (Cons x xs) = rnf x `seq` rnf xs 

instance NFData B where
    rnf B0 = ()
    rnf B1 = ()

instance NFData Nat where
    rnf Z     = ()
    rnf (S x) = rnf x


instance NFData BS where
    rnf BL = ()
    rnf (BN l r) = rnf l `seq` rnf r

instance NFData MSTok where
    rnf (LPar t)  = rnf t 
    rnf (RPar t)  = rnf t 
    rnf (Dot t)   = rnf t 
    rnf (Str x t) = rnf x `seq` rnf t
    rnf (MSTokEOS) = ()
instance NFData SExp where
    rnf (Symbol x)  = rnf x 
    rnf (SNil)      = ()
    rnf (SCons x y) = rnf x `seq` rnf y 

instance NFData MParen where
    rnf (L x) = rnf x
    rnf (R x) = rnf x
    rnf EOS   = ()



countTime :: NFData a => IO a -> IO Double
countTime f = 
    do start <- getCPUTime
       r     <- f
       print (rnf r)
       end   <- getCPUTime
--       putStr $ show $ (fromIntegral(end - start))/(10**12)
--       putStrLn " seconds are elapsed."
       return ((fromIntegral(end - start))/(10**12))

performTest desc input f g = do 
  performGC 
  putStrLn $ "=== " ++ desc ++ " =============" 
  print $ rnf input
  print (size input) 
  performGC 
  putStrLn "-- HandWritten Code --------------"
  hwtime <- countTime (return $ f input)
  rest input g hwtime
    where
      rest input g hwtime = do 
        putStrLn $ (printf "%.2f" hwtime) ++ " seconds are elappsed."
        performGC 
        putStrLn "-- Automatically-Derived Code ----"
        drtime <- countTime (return $ g input)
        putStrLn $ (printf "%.2f" drtime) ++ " seconds are elappsed."
        putStrLn "-- Overhead (Ratio of AD/HW) --"
        putStrLn $ (printf "%.2f" (drtime/hwtime))
        putStrLn ""



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
-- 4000000
-- inv_Fsnoc   -- 2.4s
-- handwritten -- 1.4s
-- invsnoc2    -- 1.7s
smain = do
    let ls  = fromHsList $ (take (4000000) (cycle [1]) ++ [2] :: [Int])
    performTest "Snoc" ls invsnocO inv_Fsnoc 
--    print (rnf ls)
--    countTime (return $ invsnocO ls)

snoc_exp = testRun ("Snoc", ls, invsnoc, inv_Fsnoc)
    where ls  = fromHsList $ (take (4000000) (cycle [1]) ++ [2] :: [Int])

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


--  invdoublelist   -- 0.44s
--  inv_Fdoublelist -- 3.0s
--  handwritten     -- 0.18s
dlmain = do 
  let ls = dl (fromHsList $ (take 3000000 (cycle [1]) :: [Int])) 
  performTest "Double List" ls invdl inv_FdoubleList
--  print (rnf ls)
--  countTime (return $ invdoublelist ls) 
 
dl_exp = testRun ("Double List", ls, invdl, inv_FdoubleList)
    where ls = dl (fromHsList $ (take 3000000 (cycle [1]) :: [Int])) 

-- incL(Nil)       = Cons B0 Nil
-- incL(Cons B0 x) = Cons B1 x
-- incL(Cons B1 x) = Cons B0 (incL(x))

-- appn(Nil,ys)            = Pair Nil ys
-- appn(Cons x xs,ys)      = letappend(appn(xs,ys),x)
-- letappend(Pair n zs ,x) = Pair (incL(n)) (Cons x zs)

-- treelist(BL)     = Cons Nil Nil
-- treelist(BN l r) = lettreelist(appn(treelist(l),treelist(r)))
-- lettreelist(Pair n (Cons r rs)) = Cons n (Cons r rs)

{-
q_tl -> Cons q_nil1 q_nil2
q_tl -> Cons q_any  q_1
q_1  -> Cons q_any  q_any

q_ap -> Pair q_nil3 q_any
q_ap -> Pair q_incl q_2
q_2  -> Cons q_any  q_any

q_inc -> Cons q_b01 q_nil4
q_inc -> Cons q_b11 q_any
q_inc -> Cons q_b02 q_inc 
-}



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
            
class Sizable a where
    {-# SPECIALIZE size :: Int -> Int #-}
    {-# SPECIALIZE size :: Char -> Int #-}
    size :: a -> Int

instance Sizable B where
    size B0 = 1
    size B1 = 1

instance Sizable a => Sizable (List a) where
    size xs = f xs 0
        where f xs s | seq s True 
                        = case xs of 
                            Nil       -> 1 + s 
                            Cons x ys -> f ys (size x + 1 + s)
    -- size Nil = 1
    -- size (Cons x xs) = size x + 1 + size xs

instance (Sizable a,Sizable b) => Sizable (a,b) where
    size (x,y) = size x + size y + 1 

instance (Sizable a,Sizable b) => Sizable (Pair a b) where
    size (Pair x y) = size x + size y + 1 

instance Sizable Int where
    size _ = 1

instance (Sizable a) => Sizable [a] where
    size [] = 1
    size (x:xs) = size x + 1 + size xs 

instance Sizable Nat where
    size = (+1).nat2int 

instance Sizable MSTok where
    size (Str x t) = 1 + size x + size t 
    size (LPar t)  = 1 + size t
    size (RPar t)  = 1 + size t 
    size (Dot  t)  = 1 + size t 
    size _         = 1 

instance Sizable Char where
    size _ = 1 

instance Sizable MParen where
    size (L x) = 1 + size x
    size (R x) = 1 + size x
    size EOS   = 1

inv_tl :: List (List B) -> BS
inv_tl(Cons Nil Nil) = BL
inv_tl(Cons n (Cons r rs)) = 
    let (x,y) = inva(n,Cons r rs)
        l     = inv_tl (x :: List (List B))
        r'    = inv_tl (y :: List (List B)) 
    in BN l r'
inva:: (List B, List x) -> (List x, List x)
inva(Nil,ys) = (Nil,ys)
inva(m,Cons x zs) = 
    let n = invi m 
        (xs,ys) = inva(n,zs)
    in (Cons x xs,ys)
invi :: List B -> List B
invi(Cons B0 Nil) = Nil
invi(Cons B1 x)   = Cons B0 x
invi(Cons B0 y)   = Cons B1 (invi(y))
    

mkB n | n == 1 = BL
      | n == 2 = BN BL BL
      | n >= 3 =
--          BN (mkB 1) (mkB (n-1))
            BN (mkB (n`div`2)) (mkB $(n+1)`div`2)

-- 2937815
-- handwritten   -- 1.4s
-- invtreelist   -- 1.4s
-- inv_Ftreelist -- 4.5s
tlmain = do
  let ls = treelist (mkB 400000)
  performTest "TreeList" ls (invtreelist) (inv_Ftreelist)
  -- print (size ls)
  -- print (rnf ls)
  -- countTime (return $ invtreelist ls)

tl_exp =  
    let ls = treelist (mkB 400000)
    in testRun ("TreeList", ls, (invtreelist),  (inv_Ftreelist))
              

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


rlmain = do
  let xs = cycle [B0,B1]
  let ys = cycle [three, four, five]
          where three = Cons B1 (Cons B1 Nil)
                four  = Cons B0 (Cons B0 (Cons B1 Nil))
                five  = Cons B1 (Cons B0 (Cons B1 Nil))
  let ls = foldr Cons Nil $ map (\(x,y) -> Pair x y) 
                             $ take 1000000 $ zip xs ys                 
  performTest "RunLength" ls runlength_expand inv_Frunlength 


rl_exp =
  let xs = cycle [B0,B1]
      ys = cycle [three, four, five]
          where three = Cons B1 (Cons B1 Nil)
                four  = Cons B0 (Cons B0 (Cons B1 Nil))
                five  = Cons B1 (Cons B0 (Cons B1 Nil))
      ls = foldr Cons Nil $ map (\(x,y) -> Pair x y) 
                             $ take 1000000 $ zip xs ys                 
  in testRun ("RunLength", ls, runlength_expand, inv_Frunlength)


trmain = do 
  let ls = (fromHsList $ (take 4000000 (cycle [1,2]) :: [Int])) 
  performTest "TABA Reverse" ls f inv_Ftaba_reverse
      where f x = g x Nil
            g Nil y = y
            g (Cons a x) y = g x (Cons a y)
tr_exp = 
  let ls = (fromHsList $ (take 4000000 (cycle [1,2]) :: [Int])) 
  in testRun ("TABA Reverse",ls, f, inv_Ftaba_reverse)
      where f x = g x Nil
            g Nil y = y
            g (Cons a x) y = g x (Cons a y)


trmain2 = do 
  let ls = (fromHsList $ (take 3500000 (cycle [1,2]) :: [Int])) 
  performTest "TABA Reverse (HW Code is also TABA)" ls f inv_Ftaba_reverse
      where f x = let (Nil,r) = h (length x) x in r 
            length Nil = 0
            length (Cons _ x) = 1 + length x
            h 0 y = (y,Nil)
            h (n+1) y = 
                let (Cons a z,r) = h n y
                in  (z, Cons a r)

tr_exp2 = 
  let ls = (fromHsList $ (take 3500000 (cycle [1,2]) :: [Int])) 
  in testRun ("TABA Reverse (HW Code is also TABA)", ls, f, inv_Ftaba_reverse)
      where f x = let (Nil,r) = h (length x) x in r 
            length Nil = 0
            length (Cons _ x) = 1 + length x
            h 0 y = (y,Nil)
            h (n+1) y = 
                let (Cons a z,r) = h n y
                in  (z, Cons a r)
  

b2pmain = do 
  let s = int2nat 7000000
  -- print $ f s
  -- print $ inv_Fbin2peano s
  performTest "Bin2Peano" s peano2bin inv_Fbin2peano

b2p_exp = 
  let s = int2nat 7000000
  in testRun ("Bin2Peano", s, peano2bin, inv_Fbin2peano)


p2b_exp = 
    let s = int2lsb 7000000
    in testRun ("Peano2Bin", s, bin2peano, inv_Fpeano2bin)

-- printSExp(x) = printCar x Nil

-- printCar (Symbol x)  t = Cons (Str x) t 
-- printCar (SNil)      t = Cons LPar (Cons RPar t)
-- printCar (SCons x y) t = Cons LPar (printCar x (printCdr y (Cons RPar t)))

-- printCdr (Symbol x)  t = Cons Dot (Cons (Str x) t)
-- printCdr (SNil)      t = t
-- printCdr (SCons x y) t = printCar x (printCdr y t)

-- printSExpHW(x) = printCar(Nil,x)


-- printCarHW(t,Symbol x)  = Cons (Str x) t
-- printCarHW(t,SNil)      = Cons LPar (Cons RPar t)
-- printCarHW(t,SCons x y) = Cons LPar (printCarHW(printCdrHW(t,y),x))

-- printCdrHW(t,Symbol x)  = Cons Dot (Cons (Str x) (Cons RPar t))
-- printCdrHW(t,SNil)      = Cons RPar t
-- printCdrHW(t,SCons x y) = printCarHW(printCdrHW(t,y),x)		       	
                        


makeSExp n 
    | n == 2 = Symbol "w"
    | n == 1 = Symbol "h"
    | n == 0 = SNil
    | True   = SCons (makeSExp (n-2)) (makeSExp (n-1))
        

ps_exp = 
  let s = printSExp $ makeSExp 32
  in testRun ("Print SExp", s, parseSExp, inv_FprintSExp)
      where
        pprint x = pp (printSExp x) []
        pp (Str x t) = \v -> x ++ " " ++ (pp t v)
        pp (LPar  t) = \v -> '(':' ':pp t v 
        pp (RPar  t) = \v -> ')':' ':pp t v 
        pp (Dot   t) = \v -> '.':' ':pp t v 
        pp MSTokEOS  = \v -> v

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
          

{-
sb(BL,r)      = Cons(B0,Cons(B1,r))
sb(BN(x,y),r) = Cons(B0,sb(x,sb(y,Cons(B1,r))))

Is left-2-right DFS automata required, 
for ll case?
-}

-- pb x = let (t,Nil) = isb x in t
--     where
--       isb x = trace (show $ size x) $ let Q1 (t,r) = trav1 x in (t,r)
--       trav1 (Cons x y) =
--           case (trav2 x, trav3 y) of 
--             (Q1 (),  Q2 (r,_)) -> Q1 (BL,r)
--             (Q1 (),  Q1 ((t,r),_)) -> 
--                 let (y,r') = isb r
--                     Cons B1 r'' = r'
--                 in  Q1 (BN t y ,r'')
--       trav2 B0 = Q1 ()
--       trav4 B0 = Q1 ()
--       trav4 B1 = Q2 ()
--       trav3 (v@(Cons x y)) =
--           case (trav4 x, trav3 y) of 
--             (Q2 (),  Q2 (_,r)) -> Q2 (r,v)
--             (Q2 (),  Q1 (_,r)) -> Q2 (r,v)
--             (Q2 (),  Q3 r    ) -> Q2 (r,v)
--             (Q1 (),  Q2 (r,_)) -> Q1 ((BL,r),v)
--             (Q1 (),  Q1 ((t,r),_)) -> 
--                 let (y,r') = isb r
--                     Cons B1 r'' = r'
--                 in  Q1 ((BN t y ,r''),v)
--       trav3 v = Q3 v

                
-- Encoding to "List" inead of Monadic tree requires
-- l2r dfs parsing.
               
sbmain = do 
  let s = sb $ (mkB 3000000)
  performTest "Print BIN" s parseBin inv_Fserialize_bintree 
    where
      sb x = f x EOS
      f BL y       = L (R y)
      f (BN l r) y = L (f l (f r (R y)))

sb_exp = 
    let s = sb $ (mkB 3000000)
    in testRun ("Print BIN", s, parseBin, inv_Fserialize_bintree)
    where
      sb x = f x EOS
      f BL y       = L (R y)
      f (BN l r) y = L (f l (f r (R y)))


dbl_exp =
    let s = int2nat (16 * 10^6) 
    in testRun ("double of integer", s, half, inv_Fdouble)
        where
          half Z = Z
          half (S (S x)) = S (half x)

zipI_exp =
    let s = fromHsList $ (take (2000000) (cycle [Pair 1 2] :: [Pair Int Int]))
    in testRun ("zipI", s, my_unzip, inv_Fmyzip)
        where
          my_unzip Nil = (Nil,Nil)
          my_unzip (Cons (Pair a b) x) =
              let (s,t) = my_unzip x 
              in (Cons a s, Cons b t)

testRun :: (NFData b, NFData a, Sizable a) =>
           (String, a, a -> b, a -> b) -> Bool -> IO ()
testRun (desc, input, fst, snd) isHW =  do
          putStrLn $ "=== " ++ desc ++ " =============" 
--          print $ rnf input
          putStrLn $ printf "size: %d"  (rnf input `seq` size input) 
          performGC 
          performGC 
          performGC 
          ( if isHW then 
                do putStrLn "-- HandWritten Code --------------"
                   hwtime <- countTime (return $ fst input)
                   putStrLn $ (printf "%.2f" hwtime) 
                                ++ " seconds are elappsed."
            else 
                do putStrLn "-- Generated Code ----------------"
                   hwtime <- countTime (return $ snd input)
                   putStrLn $ (printf "%.2f" hwtime) 
                                ++ " seconds are elappsed.")


main = do
    let trials = [
         ("snoc", snoc_exp),
         ("dl", dl_exp),
         ("tl"  , tl_exp),
         ("rl",   rl_exp),
         ("rev",   tr_exp), 
         ("rev2",  tr_exp2),
         ("b2p",   b2p_exp),
         ("p2b",   p2b_exp),
         ("sb",    sb_exp), 
         ("dbl",   dbl_exp),
         ("zip",   zipI_exp),
         ("print_sexp", ps_exp) ]
    (exp:hw:_) <- getArgs
    let isHW = case hw of
                 "0"  -> False
                 ""   -> False 
                 "00" -> False
                 _    -> True 
    let tr = lookup exp trials
    case tr of 
      Just f -> f isHW
      _ -> putStr "Error!"
          
            
--    sbmain
--    psmain
   -- smain >> dlmain >> tlmain >> rlmain >> trmain 
   --       >> trmain2 >> b2pmain >> sbmain

{-# RULES
"SizeNatInt" forall x. size (int2nat x) = x+1
  #-}