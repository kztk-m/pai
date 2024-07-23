{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}

module Syntax.Abstract
    (
     Pat(..), Exp(..), Prog(..), Decl(..),
     Name(..), ID, IDMap,
     findEntryPoint,
     patId, expId, decId,
     prog, decl, conP, varP, conE, funE, varE,
     collectVarsE,
     fromCSTtoAST, ast2hs,
    ) where

import           Util

import           Control.Monad       (zipWithM)
import           Control.Monad.State
import           Data.Function       (on)
import           Data.List
import           Syntax.Concrete
import           Text.PrettyPrint

import qualified Data.Foldable       as Foldable
import           Data.Sequence       (Seq, ViewL (..), viewl, (<|), (|>))
import qualified Data.Sequence       as Seq

-- import qualified Language.Haskell.TH as TH
import qualified Syntax.MiniHaskell  as H

import           Data.Map            (Map)
import qualified Data.Map            as Map


#if MIN_VERSION_base(4,9,0)
import           Prelude             hiding ((<>))
#endif

type ID = Int

newtype Prog = Prog { decls :: [Decl] }


data Decl = Decl ID Name [Pat] Exp

data Pat
    = ConP ID Name [ Pat ]
    | VarP ID Name
      deriving (Eq,Ord)

data Exp
    = ConE ID Name [ Exp ]
    | VarE ID Name
    | FunE ID Name [ Exp ]
      deriving (Eq,Ord)

type IDMap = Map ID (SrcSpan, Doc)

--
-- Utilities
--

collectVarsE :: Exp -> [Name]
collectVarsE e =  snub $ vars e
    where
      vars (ConE _ _ es) = concatMap vars es
      vars (FunE _ _ es) = concatMap vars es
      vars (VarE _ v)    = [v]

-- |This function detect the entrypoint of program.
-- If program contains "main" function, it returns "main",
-- otherwise, the funtion declarated the top in the code is used.
findEntryPoint :: Prog -> Name
findEntryPoint (Prog ls)
    | containsMain ls = Name "main"
    | otherwise        = let Decl _ f _ _ =  head ls in f
    where
      containsMain (Decl _ (Name "main") _ _:ls) = True
      containsMain (_:ls)                        = containsMain ls
      containsMain _                             = False

--
-- Id Extraction
--

expId (ConE i _ _) = i
expId (FunE i _ _) = i
expId (VarE i _)   = i

patId (ConP i _ _) = i
patId (VarP i _)   = i

decId (Decl i _ _ _) = i



-- | Converts a CST to an AST
--   Map in the return value represents the mapping from term (expression/pattern/...)
--   ID to its string representation.
fromCSTtoAST :: CProg -> (Prog, Map ID (SrcSpan, Doc))
fromCSTtoAST ds =
    let (_, (_,m,ds')) = runState (mapM convLDecs $ groupLDecs ds) (0,Map.empty,Map.empty)
    in (Prog $ Map.elems ds', m)
    where
      groupLDecs ds = groupBy eq ds
          where eq (L _ (CDecl f _ _)) (L _ (CDecl g _ _)) = f == g
      convLDecs ds =
          do { is <- mapM (\x -> uniqId) ds
             ; zipWithM convLDec is ds }
          where convLDec i (L s (CDecl f ps e)) =
                    do { ps' <- mapM convLPat ps
                       ; let dummy = Decl i f ps' undefined
                       ; addD dummy
                       ; e' <- convLExp e
                       ; let d = Decl i f ps' e'
                       ; updD i d
                       ; add i (s,ppr d) }
      uniqId =
          do { (i,m,ds) <- get; put (i+1,m,ds); return i }
      add k v =
          do { (i,m,ds) <- get; put (i,Map.insert k v m,ds) }
      addD (d@(Decl k _ _ _)) =
          do { (i,m,ds) <- get; put (i,m,Map.insert k d ds) }
      updD k d =
          do { (i,m,ds) <- get
             ; put (i,m,Map.adjust (\_ -> d) k ds) }

      -- convLDec (L s (CDecl f ps e)) =
      --     do { i <- uniqId
      --        ; ps' <- mapM convLPat ps
      --        ; let dummy = Decl i f ps' undefined
      --        ; addD dummy
      --        ; e'  <- convLExp e
      --        ; let d = Decl i f ps' e'
      --        ; updD i d
      --        ; add i (s,ppr d) }
      convLPat (L s (CVarP v))
          = do { i <- uniqId
               ; let p = VarP i v
               ; add i (s,ppr p)
               ; return p }
      convLPat (L s (CConP c ps))
          = do { i   <- uniqId
               ; ps' <- mapM convLPat ps
               ; let p = ConP i c ps'
               ; add i (s,ppr p)
               ; return p }
      convLExp (L s (CLetE p e1 e2))
          = do { i <- uniqId
               ; j <- uniqId
               ; ap  <- convLPat p
               ; ae1 <- convLExp e1
               ; let vs = (freeVars (unLoc e2) \\ varsP (unLoc p))
               ; ae2 <- convLExp e2
               ; let fn = Name $ "letAt" ++ show i
               ; ves <- mapM v2e vs
               ; vps <- mapM v2p vs
               ; let exp = FunE i fn (ae1:ves)
               ; let dcl = Decl j fn (ap:vps) ae2
               ; add i (s, pprLet ap (unLoc e1) (unLoc e2))
               ; addD dcl
               ; return exp }
      convLExp (L s (CVarE v))
          = do { i <- uniqId
               ; let e = VarE i v
               ; add i (s,pprExp e False)
               ; return e }
      convLExp (L s (CConE c es))
          = do { i   <- uniqId
               ; es' <- mapM convLExp es
               ; let e = ConE i c es'
               ; add i (s,pprExp e False)
               ; return e }
      convLExp (L s (CFunE c es))
          = do { i   <- uniqId
               ; es' <- mapM convLExp es
               ; let e = FunE i c es'
               ; add i (s,pprExp e False)
               ; return e }
      v2e v = do { i <- uniqId
                 ; let e = VarE i v
                 ; add i (noSrcSpan, pprExp e False);
                 ; return e }
      v2p v = do { i <- uniqId
                 ; let p = VarP i v
                 ; add i (noSrcSpan, ppr p)
                 ; return p }
      pprLet p e1 e2 =
          sep [ptext "let" <+> ppr p <+> ppr e1,
               ptext "in"  <+> ppr e2 ]

--
-- Id Labelling. Smart constructors to construct examples.
--

uniqId :: State ID ID
uniqId = do { i <- get; put (i+1); return i }

prog :: [State ID Decl]-> Prog
prog ds =
    let decls = evalState (sequence ds) 1
    in Prog decls

decl :: String -> [State ID Pat] -> State ID Exp -> State ID Decl
decl f ps e =
    do { ps' <- sequence ps
       ; i   <- uniqId
       ; e'  <- e
       ; return $ Decl i (Name f) ps' e' }

conP :: String -> [State ID Pat] -> State ID Pat
conP c ps = do { ps' <- sequence ps
               ; i <- uniqId
               ; return $ ConP i (Name c) ps' }

varP :: String -> State ID Pat
varP v    = do { i <- uniqId
               ; return $ VarP i (Name v) }

conE :: String -> [State ID Exp] -> State ID Exp
conE c es = do { es' <- sequence es
               ; i <- uniqId
               ; return $ ConE i (Name c) es' }

funE :: String -> [State ID Exp] -> State ID Exp
funE c es = do { es' <- sequence es
               ; i <- uniqId
               ; return $ FunE i (Name c) es' }

varE :: String -> State ID Exp
varE v = do { i <- uniqId
            ; return $ VarE i (Name v) }




--
-- Pretty Printing
--

instance Ppr Name where
    ppr n = ptext (show n)

instance Ppr Prog where
    ppr (Prog decls) =
        vcat $ map ppr decls

instance Show Prog where
    show = render . ppr

instance Ppr Decl where
    ppr (Decl _ f ps e) =
        ptext (show f) <> parens (hcat $ punctuate comma $ map ppr ps)
        $$ nest 4 (ptext "=" <+> ppr e)

instance Show Decl where
    show = render . ppr

instance Ppr Pat where
    ppr (ConP _ c []) = ptext (show c)
    ppr (ConP _ c ps) = ptext (show c) <>
                        parens (hcat $ punctuate comma $ map ppr ps)
    ppr (VarP _ v)    = ptext (show v)

instance Show Pat where
    show = render . ppr

instance Ppr Exp where
    ppr e = pprExp e True

pprExp :: Exp -> Bool -> Doc
pprExp e debugFlag = ppr' e
    where
      ch x | debugFlag = x
           | otherwise = empty
      ppr' (ConE i c []) = ptext (show c) <> ch (braces (ptext $ show i))
      ppr' (ConE i c es) = ptext (show c) <> ch (braces (ptext $ show i)) <>
                           parens (hcat $ punctuate comma $ map ppr es)
      ppr' (VarE i v)    = ptext (show v) <> ch (braces (ptext $ show i))
      ppr' (FunE i f es) = ptext (show f) <> ch (braces (ptext $ show i)) <>
                           parens (hcat $ punctuate comma $ map ppr es)

instance Show Exp where
    show e = render $ pprExp e True


ast2hs :: Prog -> [H.Dec]
ast2hs (Prog decls) =
    map d2h $ groupBy sameFun decls
    where
      sameFun (Decl _ f _ _) (Decl _ g _ _) = f == g
      d2h [Decl _ f ps e] =
          H.FunD (H.mkName $ show f)
                   [ H.mkSimpleClause (map p2h ps) (e2h e) ]
      d2h (ds@(Decl _ f ps e:_)) =
          H.FunD (H.mkName $ show f)
                   [ H.mkSimpleClause (map p2h ps) (e2h e)
                         | Decl _ f ps e <- ds ]
      p2h (ConP _ c ps) =
          H.ConP (H.mkName $ show c) (map p2h ps)
      p2h (VarP _ v)    = H.VarP $ (H.mkName $ show v)
      e2h (ConE _ c es) =
          foldl H.appE (H.ConE $ H.mkName $ show c) (map e2h es)
      e2h (VarE _ v)    = H.VarE $ (H.mkName $ show v)
      e2h (FunE _ f es) =
          foldl H.appE (H.VarE $ H.mkName $ show f) (map e2h es)


