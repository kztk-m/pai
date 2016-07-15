-- | Auxiliary functions for constructing Haskell expressions. 
module Inverter.HSSyntax where

import Syntax.Abstract (Name(..))
import qualified Language.Haskell.TH as TH

import Data.List (sort, elemIndex)
import Debug.Trace

-- * names

n2n :: Name -> TH.Name
n2n (Name n)  = TH.mkName n 
n2n (IName i) = TH.mkName $ "i_" ++ show i 

deadStateName :: TH.Name
deadStateName = TH.mkName "e_DEAD"

deadStateConName :: Show entry => entry -> TH.Name
deadStateConName e = TH.mkName $ "S" ++ "_" ++ show e ++ "_DEAD"

s2n :: Show state => state -> TH.Name
s2n x = TH.mkName $ "e_" ++ show x

s2c :: (Show state,Show entry) => entry -> state -> TH.Name
s2c e s 
    = TH.mkName $ "S" ++ "_"++ show e ++ "_"++show s

treeVarName = TH.mkName $ "tree" 

returnE e = TH.AppE (TH.VarE (TH.mkName "return")) e 

mkSimpleClause ps e = TH.Clause ps (TH.NormalB e) []
mkSimpleMatch  p  e = TH.Match  p  (TH.NormalB e) []
mkApp f args = foldl TH.AppE f args 

tuple :: Int -> TH.Name 
tuple 0 = TH.mkName $ "()"
tuple n = TH.mkName $ "(" ++ replicate (n-1) ',' ++ ")"

travName :: (Show a, Show b) => a -> b -> TH.Name
travName e g 
 = TH.mkName $ "trav_" ++ shows e ("_" ++ show g)

semName :: (Show state, Show entry, Show symbol) =>
           entry -> state -> symbol -> TH.Name
semName e g c
 = TH.mkName $ "sem_" ++ shows e ("_" ++ shows g ("_" ++ show c))

-- * expressions

appendE :: TH.Exp -> TH.Exp -> TH.Exp
appendE e1 e2 = 
    TH.InfixE (Just e1)
              (TH.VarE $ TH.mkName "++")
              (Just e2)

mplusE :: TH.Exp -> TH.Exp -> TH.Exp
mplusE e1 e2 =
    ( (TH.VarE $ TH.mkName "mymplus")
      `TH.AppE` e1) `TH.AppE` e2

-- * monadic operations

compEM :: TH.Exp -> TH.Exp -> TH.Exp
compEM e1 e2 = -- trace (">" ++ show e1 ++ "\n>" ++show e2 ++ "\n") $ 
    case (e1,e2) of
      (TH.LamE p (TH.AppE (TH.VarE n) e),_) | n == TH.mkName "return" ->
          TH.LamE p (TH.AppE e2 e)
      (TH.LamE p n,TH.LamE [TH.VarP v] m) ->
          TH.LamE p (TH.InfixE
                             (Just n)
                             (TH.VarE $ TH.mkName ">>=")
                             (Just e2))
      (TH.LamE p n,TH.LamE [TH.TupP [TH.VarP v]] m) ->
          TH.LamE p (TH.InfixE
                             (Just n)
                             (TH.VarE $ TH.mkName ">>=")
                             (Just e2))
      _ ->
          TH.InfixE 
                (Just e1)
                (TH.VarE $ TH.mkName ">=>")
                (Just e2)
    where
      -- singleOcc v m = v `elem` (variables [] m)
      -- variables x (VarE n) = if n `elem` x then [] else [n]
      -- variables x (AppE e1 e2) = variables x e1 ++ variables x e2
      -- variables x (InfixE me1 e me2) =
      --     (me1 >>= (variables x e)) ++ variables x e ++ (me2 >>= (variables x e))
      -- variables x (LamE ps e) = variables (concatMap varsP ps ++ x) e 
      -- variables x (TupE es)   = concatMap (variables x) es
      -- variables x (CondE e1 e2 e3) = concatMap (variables x) [e1,e2,e3]
      -- variables x (LetE ds e)      = let x' = concatMap varsDL ds ++ x 
      --                                in concatMap (varsDR x) ds ++ variables x' e 
      -- variables x (CaseE e ms)     = variables x e ++ concatMap (varsM x) ms
      -- variables x (DoE stmts)      = variables x e ++ varsSTMS x stmts
      -- variables x (CompE stmts)    = varsSTMS x stmts
      -- variables x (ListE es)       = concatMap (variables x) es
      -- variables x (SigE e _)       = variables x e 
      -- variables x (LitE _)         = []
      -- variables x (ConE _)         = []
      -- variables x _                = error "Not Supported".
      -- varsP (VarP n) = [n]
      -- varsP (TupP ps)   = concatMap varsP ps
      -- varsP (ConP _ ps) = concatMap varsP ps
      -- varsP (InfixP p1 _ p2) = varsP p1 ++ varsP p2
      -- varsP (TildeP p)       = varsP p
      -- varsP (AsP n p)        = varsP p
      -- varsP (RecP _ fps)     = concat [ varsP p | (_,p) <- fps ]
      -- varsP (ListP ps)       = concatMap varsP ps
      -- varsP (SigP p t)       = varsP p 
      -- varsDL (FunD n _)      = [n]
      -- varsDL (ValD p _ _)    = varsP p
      -- varsDL _                 = []
      -- varsDR x (FunD n cs)     = [ concatMap varsP ps ++  | (ps,b,ds) <- cs ]
      -- varsSTMS x []            = []
      -- varsSTMS x (BindS p e:r) = variables (varsP p++x) e++varsSTMS (varsP p++x) r
      -- varsSTMS x (LetS ds:r)   = let x' = concatMap varsDL ds ++ x 
      --                            in concatMap (varsDR x') ds ++ varsSTMS r
      -- varsSTMS x (ParS stmss)  = error "Not Supported"






-- | |compEMn n f g|
--   generates  |\v1 .. vn -> g (f v1 ... vn)|
compEMn :: Int -> TH.Exp -> TH.Exp -> TH.Exp
compEMn 0 e1 e2 =
    TH.InfixE (Just e1)
              (TH.VarE $ TH.mkName ">>=")
              (Just e2)
compEMn 1 e1 e2 = compEM e1 e2
compEMn n e1 e2 =
    let mvs = [ TH.mkName ("m" ++ show i ) | i <- [1..n] ]
        f1 = TH.mkName "f"
        f2 = TH.mkName "g"
        ex = TH.LamE [ TH.VarP v | v <- (f1:f2:mvs) ] $
                 compEMn 0  
                    (mkApp (TH.VarE f1) [TH.VarE v | v <- mvs ])
                    (TH.VarE f2) 
    in mkApp ex [e1,e2]
    -- let vs  = [ TH.mkName ("v" ++ show i) | i <- [1..n] ]
    --     mvs = [ TH.mkName ("m" ++ show i) | i <- [1..n] ]
    --     z   = TH.mkName "z"
    --     f1 = TH.mkName "f"
    --     f2 = TH.mkName "g"
    -- in TH.LamE [ TH.VarP v | v <- (f1:f2:mvs) ] $
    --     TH.DoE $
    --       [ TH.BindS (TH.VarP v) (TH.VarE mv) | (v,mv) <- zip vs mvs ]
    --       ++ [ TH.BindS (TH.VarP z) (mkApp (TH.VarE f1) [TH.VarE v | v <- vs ])]
    --       ++ [ TH.NoBindS $ (TH.VarE f2) `TH.AppE` (TH.VarE z) ]
        
