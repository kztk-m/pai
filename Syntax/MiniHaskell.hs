{-# LANGUAGE CPP #-}

module Syntax.MiniHaskell where

import Text.PrettyPrint as PP
import Text.PrettyPrint.HughesPJClass as PP 

#if MIN_VERSION_base(4,9,0)
import           Prelude          hiding ((<>))
#endif

data Name = Name String
            deriving (Eq, Ord)
data Dec 
  = FunD     Name [Clause]
  | DataD    Name [Name] [Con]
  | ValD     Pat  Exp 
  | CommentD String
    
data Clause 
  = SimpleClause [Pat] Exp

data Con 
  = NormalC Name [Type]

data Type 
  = VarT Name

data Pat
  = VarP Name
  | TupP [Pat]
  | WildP
  | ConP Name [Pat]

data Exp
  = VarE Name
  | ConE Name
  | AppE Exp Exp
  | CaseE Exp [Match]
  | InfixE Exp Exp Exp
  | TupE   [Exp]
  | DoE    [Stmt]
  | LamE [Pat] Exp
  | LitE   Lit 

data Stmt
  = BindS Pat Exp
  | LetS  [Dec]
  | NoBindS   Exp

data Lit
  = StringL String 

data Match = SimpleMatch Pat Exp 

mkName :: String -> Name 
mkName = Name

mkSimpleClause :: [Pat] -> Exp -> Clause 
mkSimpleClause = SimpleClause

mkSimpleMatch :: Pat -> Exp -> Match
mkSimpleMatch = SimpleMatch 

mkCompose :: Exp -> Exp -> Exp 
mkCompose e1 e2 = InfixE e1 (VarE $ mkName ".") e2

aappE :: Exp -> Exp -> Exp
aappE e1 e2 = InfixE e1 (VarE $ mkName "<*>") e2 

appE (LamE (VarP n:ps) e1) e2 | isSimple e2 =
  case ps of
    [] -> replace n e2 e1
    _  -> LamE ps (replace n e2 e1)
  where
    isSimple (VarE _) = True
    isSimple (LitE _) = True
    isSimple _        = False

    replace n e (VarE x) =
      if n == x then e else VarE x
    replace n e (ConE c) = ConE c
    replace n e (AppE e1 e2) = AppE (replace n e e1) (replace n e e2)
    replace n e (CaseE e1 m) = CaseE (replace n e e1) (map (replaceM n e) m)
    replace n e (InfixE e1 e2 e3) = InfixE (replace n e e1) (replace n e e2) (replace n e e3)
    replace n e (TupE es) = TupE $ map (replace n e) es 
    replace n e (DoE  s)  = DoE $ replaceS n e s 
    replace n e (LamE ps e1) =
      if n `elem` concatMap fv ps then
        LamE ps e
      else
        LamE ps (replace n e e1)
    replace n e (LitE l) = LitE l

    replaceM n e (SimpleMatch p e1) =
      if n `elem` fv p then
        SimpleMatch p e
      else
        SimpleMatch p (replace n e e1)

    replaceS :: Name -> Exp -> [Stmt] -> [Stmt]
    replaceS n e [] = []
    replaceS n e (NoBindS e1:ss) =
      NoBindS (replace n e e1): replaceS n e ss
    replaceS n e (BindS p e1:ss) =
      if n `elem` fv p then
        BindS p (replace n e e1):ss
      else
        BindS p (replace n e e1):replaceS n e ss
    replaceS n e (LetS d:ss) =
      if n `elem` concatMap fvLHS d then
        LetS d:ss
      else
        LetS (map (replaceRHS n e) d) : replaceS n e ss

    fvLHS (ValD p _)  = fv p

    replaceRHS n e (ValD p e1) = ValD p (replace n e e1)

appE e1 e2 = AppE e1 e2 

returnE :: Exp -> Exp 
returnE x = VarE (mkName "return") `appE` x

tupE :: [Exp] -> Exp
tupE [x] = x
tupE xs  = TupE xs

tupP :: [Pat] -> Pat
tupP [x] = x
tupP ps  = TupP ps 

mkApps :: Exp -> [Exp] -> Exp 
mkApps f args = foldl appE f args           

tuple :: Int -> Name 
tuple 0 = mkName $ "()"
tuple 1 = mkName $ "id" 
tuple n = mkName $ "(" ++ replicate (n-1) ',' ++ ")"


pprint :: [Dec] -> String
pprint = prettyShow 


class FV a where
  fv :: a -> [Name]

instance FV Pat where
  fv p = go p []
    where
      go (VarP n)      r = n:r 
      go (TupP ps)     r = goList ps r 
      go WildP         r = r
      go (ConP n ps)   r = goList ps r
      goList [] r     = r
      goList (p:ps) r = goList ps (go p r)
  

instance Pretty Name where
  pPrint (Name s) = text s 

instance Show Name where
  show (Name s) = s 

instance Pretty Dec where
  pPrintPrec v k (FunD f cs) =
    vcat [ pPrint f <+> pPrintPrec v 0 c | c <- cs ]

  pPrintPrec v k (DataD d vs cons) =
    vcat [ text "data" <+> pPrint d <+> hsep (map pPrint vs)
         , nest 4 $ vcat $ zipWith f cons ("=":repeat "|")]
    where
      f c delim =
        text delim <+> pPrintPrec v 0 c 
           
  pPrintPrec v k (ValD d c) =
    pPrint d <+> text "=" <+> pPrintPrec v 0 c 
  pPrintPrec v k (CommentD s) =
    text "{-" <+> text s <+> text "-}"

  pPrintList v ds = vcat $ map (pPrintPrec v 0) ds

ifParens b t = if b then parens t else t 

instance Pretty Con where
  pPrintPrec v k (NormalC n ts) = pPrint n <+> hcat (map (pPrintPrec v 0) ts)

instance Pretty Type where
  pPrintPrec v k (VarT n) = pPrint n

instance Pretty Clause where
  pPrintPrec v k (SimpleClause ps e) =
    vcat [ hsep (map (pPrintPrec v 1) ps)
         , (text "=" <+> pPrintPrec v 0 e) ]

instance Pretty Pat where
  pPrintPrec v k (VarP p)     = pPrint p 
  pPrintPrec v k (TupP ps)    = parens $ hcat $ punctuate comma $ map (pPrintPrec v 0) ps 
  pPrintPrec v k WildP        = text "_" 
  pPrintPrec v k (ConP n ps) =
    ifParens (k > 0) $
     pPrint n <+> hsep (map (pPrintPrec v 1) ps)

ppOpR k0 s e1 e2 v k =
  ifParens (k > k0) $
  pPrintPrec v (k0 + 1) e1 <+> text s <+> pPrintPrec v k0 e2 

ppOpL k0 s e1 e2 v k =
  ifParens (k > k0) $
  pPrintPrec v k0 e1 <+> text s <+> pPrintPrec v (k0+1) e2 

instance Pretty Exp where
  pPrintPrec v k (VarE n) = pPrint n 
  pPrintPrec v k (ConE n) = pPrint n 
  pPrintPrec v k (AppE e1 e2) =
    ifParens (k > 10) $
    sep [pPrintPrec v 10 e1, pPrintPrec v (10+1) e2]
  pPrintPrec v k (CaseE e match) =
    vcat [ text "case" <+> pPrintPrec v 0 e <+> text "of", 
           nest 2 (vcat $ map (pPrintPrec v 0) match)]
  pPrintPrec v k (InfixE e1 e2 e3) =
    case e2 of
      VarE (Name ".") ->
        ppOpR 9 "." e1 e3 v k 
      VarE (Name "<*>") ->
        ppOpL 4 "<*>" e1 e3 v k
      _ ->
        parens (pPrintPrec v 20 e1 <+> pPrintPrec v 20 e2 <+> pPrintPrec v 20 e3) 
  pPrintPrec v k (TupE es) =
    parens (sep $ punctuate comma $ map (pPrintPrec v 0) es)
  pPrintPrec v k (DoE ss) =
    ifParens (k > 0) $ 
    text "do" <+> 
    (vcat $ zipWith f ss ("{":repeat ";")) <> text "}"
    where f s t = text t <+> pPrintPrec v 0 s 
  pPrintPrec v k (LamE ps e) =
    ifParens (k > 1) $ 
    sep [ hcat [text "\\", hsep (map (pPrintPrec v 1) ps), text "->"],
          nest 2 (pPrintPrec v 1 e) ]
  pPrintPrec v k (LitE e) =
    pPrint e

instance Pretty Match where
  pPrintPrec v k (SimpleMatch p e) =
    sep [ (pPrintPrec v 0 p) <+> text "->",
          nest 2 (pPrintPrec v 0 e)]

instance Pretty Lit where
  pPrint (StringL s) = text (show s)

instance Pretty Stmt where
  pPrint (BindS p e) =
    sep [ pPrint p <+> text "<-",
          nest 2 (pPrint e) ] 
  pPrint (LetS d) =
    text "let" <+> pPrint d 
  pPrint (NoBindS e) = pPrint e 

