{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
module Main (main) where

import System.CPUTime
import MyData
import InvUtil
import System.Mem

import Text.Printf 

import System.Environment (getArgs)
import HandWritten 

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


class Sizable a where
    size :: a -> Int

{-# SPECIALIZE [1] size :: Int -> Int #-}
{-# SPECIALIZE [1] size :: Char -> Int #-}

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
            h n y = 
                let (Cons a z,r) = h (n-1) y
                in  (z, Cons a r)

tr_exp2 = 
  let ls = (fromHsList $ (take 3500000 (cycle [1,2]) :: [Int])) 
  in testRun ("TABA Reverse (HW Code is also TABA)", ls, f, inv_Ftaba_reverse)
      where f x = let (Nil,r) = h (length x) x in r 
            length Nil = 0
            length (Cons _ x) = 1 + length x
            h 0 y = (y,Nil)
            h n y = 
                let (Cons a z,r) = h (n-1) y
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
