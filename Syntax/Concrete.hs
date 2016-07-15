module Syntax.Concrete (
            CProg, CDecl(..), CExp(..), CPat(..), noSrcSpan,
            Located(..), Name(..), SrcLoc, mkSrcLoc, noLoc, 
            isValidLoc, srcFile, srcLine, srcColumn, freeVars,varsP,
            SrcSpan, startLoc, endLoc, mkSrcSpan, 
            parseString, parseFile, 
           ) where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as Tk
import Text.ParserCombinators.Parsec.Language

import qualified Text.PrettyPrint as PP

import Data.List ( (\\) )
import Util


data Name = Name   String
          | IName  String 
            deriving (Eq,Ord)

instance Show Name where
    show (Name  n) = n
    show (IName n) = "_"++n 



data Located s = L { getLoc :: SrcSpan, unLoc :: s }

instance Show s => Show (Located s) where
    show (L _ s) = "L ... " ++ show s 

data SrcLoc 
    = Loc   String Int  Int
    | NoLoc   

data SrcSpan = SrcSpan { startLoc :: SrcLoc, endLoc :: SrcLoc }

noSrcSpan = SrcSpan { startLoc = NoLoc, endLoc = NoLoc }

mkSrcSpan s e = SrcSpan s e

mkSrcLoc = Loc

noLoc e = L (SrcSpan NoLoc NoLoc) e 

isValidLoc :: SrcLoc -> Bool
isValidLoc (Loc _ _ _) = True
isValidLoc _           = False

srcFile (Loc s _ _) = s 

srcLine   (Loc _ l _) = l
srcColumn (Loc _ _ c) = c 


type CProg = [ Located CDecl ]

data CDecl = CDecl Name [Located CPat] (Located CExp)
             deriving Show 


data CExp 
    = CConE Name [Located CExp] -- ^ C(e1,..,en)
    | CVarE Name                -- ^ v 
    | CFunE Name [Located CExp] -- ^ x 
    | CLetE (Located CPat) 
            (Located CExp) (Located CExp) -- ^ let p = e1 in e2
      deriving Show

data CPat
    = CConP Name [Located CPat]
    | CVarP Name
      deriving Show

instance Ppr CExp where
    ppr (CConE c [])  = PP.ptext (show c)
    ppr (CConE c les) =
        PP.ptext (show c) PP.<>
        PP.parens (PP.hcat $ PP.punctuate PP.comma $ map ppr (map unLoc les))
    ppr (CFunE c les) = 
        PP.ptext (show c) PP.<>
        PP.parens (PP.hcat $ PP.punctuate PP.comma $ map ppr (map unLoc les))
    ppr (CLetE p e1 e2) =
        PP.sep [ ppr (unLoc p) PP.<+> PP.ptext "=" PP.<+> ppr (unLoc e1),
                 ppr (unLoc e2) ]
    ppr (CVarE v) = PP.ptext (show v)

instance Ppr CPat where
    ppr (CConP c [])  = PP.ptext (show c)
    ppr (CConP c les) =
        PP.ptext (show c) PP.<>
        PP.parens (PP.hcat $ PP.punctuate PP.comma $ map ppr (map unLoc les))
    ppr (CVarP v) = PP.ptext (show v)

freeVars (CConE _ es) = snub $ concatMap freeVars $ map unLoc es
freeVars (CVarE v)    = [v]
freeVars (CFunE _ es) = snub $ concatMap freeVars $ map unLoc es
freeVars (CLetE p e1 e2) =
    snub $ freeVars (unLoc e1) ++ (freeVars (unLoc e2) \\ varsP (unLoc p))
varsP (CConP _ ps) = snub $ concatMap varsP $ map unLoc  ps
varsP (CVarP v)    = [v]

getSrcLoc :: Parser SrcLoc
getSrcLoc = 
    do { x <- getPosition 
       ; return $ mkSrcLoc (sourceName x) (sourceLine x) (sourceColumn x) }

varId :: Parser Name
varId = do { c <- lower
           ; cs <- many (alphaNum <|> char '_')
           ; return $ Name (c:cs) }

conId :: Parser Name 
conId = do { c <- upper 
           ; cs <- many (alphaNum <|> char '_')
           ; return $ Name (c:cs) }

number = do { cs <- many1 digit
            ; return $ Name cs }

myLexer = Tk.makeTokenParser 
            $ emptyDef {
                    commentStart = "{-"
                  , commentEnd   = "-}"
                  , commentLine  = "--"           
                  , reservedNames = ["let", "in","case","data","type"]
                 }

parens = Tk.parens myLexer
symbol = Tk.symbol myLexer
comma  = Tk.comma myLexer
lexeme = Tk.lexeme myLexer
reserved = Tk.reserved myLexer
whiteSpace = Tk.whiteSpace myLexer


parseProgram :: String -> String -> Either ParseError CProg
parseProgram srcName =
    parse pProg srcName 

parseString :: String -> Either ParseError CProg
parseString s = 
    parseProgram "" s 


parseFile :: FilePath -> IO (Either ParseError CProg)
parseFile filename =
    return . parseProgram filename =<< readFile filename

{-
parseFile :: FilePath -> IO CProg
parseFile filename =
    do { s <- readFile filename
       ; case parseProgram filename s of
           Right cst -> return cst 
           Left s    -> error $ show s }
-}

pProg :: Parser CProg 
pProg = do { whiteSpace
           ; ds <- many (lexeme pLDecl)
           ; return ds }

pLDecl :: Parser (Located CDecl)
pLDecl = do { sloc  <- getSrcLoc
            ; fName <- lexeme varId 
            ; ps    <- parens (pLPats)
            ; symbol "=" 
            ; e     <- pLExp 
            ; eloc  <- getSrcLoc 
            ; return $ L (mkSrcSpan sloc eloc) $ CDecl fName ps e }

pLPats :: Parser [Located CPat]
pLPats = sepBy pLPat comma 

pLPat :: Parser (Located CPat)
pLPat = do { sloc <- getSrcLoc 
           ; do { c <- lexeme conId
                ; ps <- option [] $ parens pLPats 
                ; eloc <- getSrcLoc 
                ; let ss = mkSrcSpan sloc eloc 
                ; return $ L ss $ CConP c ps }
             <|> 
             do { c <- lexeme $ number
                ; eloc <- getSrcLoc 
                ; let ss = mkSrcSpan sloc eloc 
                ; return $ L ss $ CConP c [] }
             <|>
             do { c <- lexeme varId
                ; eloc <- getSrcLoc 
                ; let ss = mkSrcSpan sloc eloc 
                ; return $ L ss $ CVarP c } }

pLExp :: Parser (Located CExp)
pLExp = do { sloc <- getSrcLoc
           ; do { reserved "let"
                ; p  <- pLPat 
                ; symbol "="
                ; e1  <- pLExp 
                ; reserved "in"
                ; e2  <- pLExp
                ; eloc <- getSrcLoc
                ; let ss = mkSrcSpan sloc eloc 
                ; return $ L ss $ CLetE p e1 e2 } 
             <|>
             do { c  <- lexeme conId
                ; es <- option [] $ parens (sepBy (pLExp) comma)
                ; eloc <- getSrcLoc 
                ; let ss = mkSrcSpan sloc eloc                       
                ; return $ L ss $ CConE c es }
             <|>
             do { c <- lexeme $ number
                ; eloc <- getSrcLoc 
                ; let ss = mkSrcSpan sloc eloc                       
                ; return $ L ss $ CConE c [] }
             <|>
             do { c <- lexeme varId 
                ; do { es <- parens (sepBy (pLExp) comma) 
                     ; eloc <- getSrcLoc 
                     ; let ss = mkSrcSpan sloc eloc 
                     ; return $ L ss $ CFunE c es }
                  <|>
                  do { eloc <- getSrcLoc 
                     ; let ss = mkSrcSpan sloc eloc                      
                     ; return $ L ss $ CVarE c} } }
                      
             
        

