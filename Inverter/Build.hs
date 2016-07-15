{-# LANGUAGE FlexibleContexts #-}

module Inverter.Build (
    -- fromProgramToGTA,  -- ^ this should be made obsolette
    fromProgramToTA,
    fromTAtoDGTA, 
    -- ambiguityInfo,     -- ^ also obsolette
    testGTA, testGTA'
    ) where

import Syntax.Abstract
import TreeAutomata.Automata as TA
import TreeAutomata.Guided as GTA
import Inverter.Action
import Util 

import Control.Monad.State

import Data.Maybe 
import Data.Map (Map)
import qualified Data.Map as Map

-- | This function calculates deterministic GTA from an input program.
fromProgramToGTA :: Prog -> (Map AState (GTA Int Int Name Act), AState, Bool)
fromProgramToGTA prog =
    let (ta, entryPoint, otherEntries) = fromProgramToTA prog 
    in (Map.map (renumberStates . determinize . renumberGuides) $ fromTA2GTAs ta (entryPoint:otherEntries),
        entryPoint,
        isJust $ checkAmbiguity ta entryPoint)

fromTAtoDGTA ::
  (Ord state, Ord name, Action action) =>
  TA state name action
  -> [state]
  -> Map state (GTA Int Int name action)
fromTAtoDGTA ta states =
   Map.map (renumberStates . determinize . renumberGuides) 
        (fromTA2GTAs ta states)

-- | This function calculates TA from an input program.

fromProgramToTA :: Prog -> (TA AState Name Act, --  constructed TA
                            AState,             --  entry point
                            [AState])           --  other states 
fromProgramToTA prog =
    let (tMap,ePs) = execState (mapM makeR $ decls prog) (Map.empty,[])
    in (TA tMap, FromF entrypoint, ePs)
    where
      st e       = FromE $ expId e
      int2name i = IName $ show i 
      entrypoint = findEntryPoint prog
      p2a recVar (ConP _ c ps) = ConA c (map (p2a recVar) ps)
      p2a recVar (VarP _ v)    = FieldA (recVar) v
      addR s src dst act = 
          do { (m,e) <- get
             ; put (Map.insertWith (++) s [Tr src dst act] m,e) }
      addEp state = 
          do { (m,e) <- get 
             ; put (m,state:e) }             
      makeR (Decl _ f ps e) =
          let varName = (Name "v", collectVarsE e)
              act = LamA [varName] $ RecordA $ 
                      [ (int2name i, p2a varName p)
                            | (p,i) <- zip ps [1..] ]
          in addR EpsS [st e] (FromF f) act >> makeE e
      -- { v: _ }
      makeE (VarE i v) =
          let act = LamA [] $ RecordA $ [(v,MarkA)]
          in addR TopS [] (FromE i) act 
      -- \v1 v2 ... vn -> merge v1 v2 ... vn
      makeE (ConE i c es) =
          let rvs = [ (Name ("v"++show i), collectVarsE e) 
                          | (e,i) <- zip es [1..] ]
              act = LamA rvs $ MergeA rvs
          in addR (ConS c) (map st es) (FromE i) act >> mapM_ makeE es
      -- \x -> let r1 = I#e1(x.1), ..., rn = I#en(x.n) in merge r1 r2 ... rn
      makeE (FunE i f es) =
          let varName = (Name "x", [int2name i | i <- [1..(length es)]] )
              bind =[ case e of 
                        (VarE j v) -> 
                            ((Name ("v"++show i),[v]),FieldA varName (int2name i))
                        _ -> 
                            ((Name ("v"++show i), collectVarsE e),
                                     RunA (st e) (FieldA varName (int2name i)))
                      | (e,i) <- zip es [1..] ]
              act = LamA [varName] $ LetA bind $ MergeA (map fst bind)
          in addR EpsS [FromF f] (FromE i) act 
             >> mapM_ (addEp.st) es >> mapM_ makeE es

-- | This function calculates why the system cannot derive the inverse of input program.
--   NB: It returns some of the causes but may not all.
ambiguityInfo :: Prog -> [(AState, AState)]
ambiguityInfo prog = 
    case let (ta,ep,_) = fromProgramToTA prog in checkAmbiguity ta ep of 
      Just    x -> [ (s1,s2)| ((EpsS,[s1]), (EpsS,[s2])) <- x ]
      Nothing   -> []

--
-- * Debugging
--

-- | For debugging, 
--   given an input program, this function returns GTA without determinization 
testGTA prog =
    let (ta, entryPoint, otherEntries) = fromProgramToTA prog 
    in (Map.map determinize $ fromTA2GTAs ta (entryPoint:otherEntries),
        entryPoint)

-- | For debugging, 
--   given an input program, this function returns GTA without state-simplication and determinization.
testGTA' prog =
    let (ta, entryPoint, otherEntries) = fromProgramToTA prog 
    in (fromTA2GTAs ta (entryPoint:otherEntries),
        entryPoint)

-- Notes

{-
Conversion of Act for code generation
[[act]] = A[[ act ]]  -- t is fresh

A[[\v1 v2 -> a]] = 
  \R2T[[v1]] R2T[[v2]] -> A[[a]]

A[[c(a1,a2)]] =
 do { v1 <- A[[a1]],; v2 <- A[[a2]]; return  c(v1,v1) }

A[[v.f]] = return \R2Ti[[v.f]]
A[[v]]   = return \R2T[[v]]
A[[{f1: a1, f2: a2}]] = 
  do { v1 <- A[[a1]]; v2 <- A[[a2]]; return (v1,v2) }
A[[v{x} U v'{x'} U v''{x''}] = Merge[[ v{x},v'{x'}, v''{x''} ]]
A[[ [_] ]] = tree -- tree is bound outside
A[[ <a1,a2,a3> ]] 
  = \x -> do { t1 <- a1 x; t2 <- a2 x; t3 <- a3 x; return (t1,t2,t3) }
A[[ let { v1 = a1; v2 = a2 } in a ]]
  = do { R2T[[v1]] <- A[[a1]]; R2T[[v2]] <- A[[a2]] ; A[[a]] }
A[[ @E1(a) ]]
  = (A[[a]] >>= \x -> S2F[[E1]](x))
A[[ a . TakeA [(0,3), (2,4)] ]]
  = \(x1,x2,x3) (y1,y2,y3,y4) ->  A[[a]] x1 y3 
A[[ a1 . a2 ]]  
  = A[[a2]] >=> A[[a1]] 

A[[ a1 | a2 ]]
  = A[[ a1 ]] ++ A[[ a2 ]]
A[[ fixA a ]] 
  = fix (\f x -> x ++ f (A[[a]] >=> x) ) return
  = fixApp (A[[a]])

R2T[[ v{x} ]]    = (v1,v2,..., vn) where n = |x|
R2Ti[[ v{x}.f ]] = vi where elemIndex f x = Just i
S2N[[ E1 ]] = func_E1 

Merge [[ v{x}, v'{x'}, v''{x''} ]]
 = ( wi ,wj `merge` wk )
  where
     wi = v s.t. exists v{x}. elemIndex f x = Just i 
                          and elemIndex f {x U x' U x''} = Just 0
     merege is introduced if there are many such "v".

conversion of code

* for transition 

G: 
   A <-- c(A1,A2) { act }
 
==>

semEGc( t,EA1(t1),EA2(t2) ) 
 = EA ( [[act]] t t1 t2 )

* for guide function

G --> c(G1,G2)

==>

travEG(c(t1,t2))
 = semEGc( c(t1,t2), travEG1(t1),  travEG2(t2) ) }

* for entryPoint

S2N[[E]](t) = travEG1(t)

* for states
data StateE x1 x2 ... xn 
  = EA1 x1
  | EA2 x2
  ...
  | EAn xn 

* for aux function

checkEq x y =
  if x == y then x
  else           error "Inconsistency Detected"

* for entry point
inv = S2N[[E]]
-}
