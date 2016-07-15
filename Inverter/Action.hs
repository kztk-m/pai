module Inverter.Action where

import Syntax.Abstract
import TreeAutomata.Automata
import Util 

import Data.Maybe 

import Text.PrettyPrint 

data Act
    = IdA
    | LamA [RecVarName] Act
    | LamAP (Maybe [ [Name] ]) [ Act ] -- this Act is always AppA; AppA only appears here
    | AppA  Act [Name]
    | ConA Name  [Act]
    | VarA RecVarName
    | FieldA  RecVarName FieldName     -- record.field
    | RecordA [(FieldName,Act)] --
    | MergeA  [RecVarName]
    | MarkA
    | LetA [(RecVarName,Act)] Act
    | RunA AState Act
    | ParA Act Act
    | CompA Act Act -- CompA a2 a1 : a1 . a2 
    | CompAn Int Act Act
    | NullA 
    | FixA Act
      deriving (Show,Ord,Eq)

type FieldNames = [Name]
type FieldName  = Name
type RecVarName = (Name,FieldNames)


oneOcc v (LamA xs a) | v `elem` xs = False
                     | otherwise   = oneOcc v a
oneOcc v (VarA v') | v == v' = True
                   | True    = False
oneOcc v (RunA s a) = oneOcc v a 
oneOcc v (ParA a1 a2)  = (oneOcc v a1) || (oneOcc v a2) -- FIXME
oneOcc v (CompA a2 a1) = (oneOcc v a1) || (oneOcc v a2) -- FIXME
oneOcc v NullA         = False
oneOcc v (ConA n as)   = case [ a | a <- as, oneOcc v a ] of
                           [v] -> True
                           _   -> False
oneOcc v _ = False

replaceVar (v,y) (LamA xs a) | v `elem` xs = (LamA xs a)
                             | otherwise   = replaceVar (v,y) a 
replaceVar (v,y) (VarA v') | v == v' = y
                          
replaceVar (v,y) (RunA s a) = replaceVar (v,y) a 
replaceVar (v,y) (ParA  a1 a2) = ParA  (replaceVar (v,y) a1) (replaceVar (v,y) a2)
replaceVar (v,y) (CompA a1 a2) = CompA (replaceVar (v,y) a1) (replaceVar (v,y) a2)
replaceVar (v,y) (ConA n as) = ConA n [ replaceVar (v,y) a | a <- as ] 
                               
replaceVar (v,y) a = a


data AState 
    = FromF Name  -- Automaton state for function call
    | FromE ID    -- Automaton state for expression
      deriving (Eq,Ord)


instance Action Act where
    compA  = cm 
        where cm IdA x = x 
              cm x IdA = x 
              cm (FixA x) (FixA y) | x == y = FixA x
                                   | x /= y = CompA (FixA x) (FixA y)
              cm (LamA [v] x) (y) | oneOcc v x = replaceVar (v,y) x
              cm x y   = CompA x y

--    tupleA = ProdA 
--    takeA  = TakeA 
    parA a1 a2 
         | a1 == a2 = a1
         | a1 /= a2 = ParA a1 a2
    fixA IdA      = IdA
    fixA (FixA a) = FixA a
    fixA a        = FixA a
    compAn = cmn 
        where cmn n IdA y = y
              cmn n x y   = CompAn n x y 
    idA    = IdA
    tuplingA narg lss = -- (\s -> trace (render $ ppr lss $$ ppr s) s) $ 
        LamAP (case arities of 
                 Just ar -> Just [ [ var i j | j <- [1..n] ] | (n,i) <- zip ar [1..] ] 
                 Nothing -> Just [ [Name "_"] | i <- [1..narg] ])
              [ parAs $ snub ls | ls <- lss ]
            where
              lss' :: [ [ ( Maybe [(Int,Int)], Act ) ] ]
              lss' = lss
              parAs []          = error "Hello?" -- This should not be reached
              parAs [(ls,a)]    = case ls of 
                                    Just ls -> AppA a  [ var i (j+1) | ((j,_),i) <- zip ls [1..] ] 
                                    Nothing -> AppA a  [] 
              parAs ((ls,a):xs) = let y  = parAs [(ls,a)] 
                                      ys = parAs xs
                                  in ParA y ys
              arities = foldr (\a r ->
                                   if isNothing a      then r
                                   else if isNothing r then Just $ map snd (fromJust a)
                                   else                     Just $ zipWith (\(i,n) y -> max n y) (fromJust a) (fromJust r)) Nothing
                           $ map (fst) $ concat lss 
              var i j = Name $ "x"++show i ++ "_" ++ show j 
    nullA = NullA


-- * Pretty Printing


instance Ppr Act where
    ppr (IdA)   = ptext "id"
    ppr (LamA [] a) = ppr a
    ppr (LamA rvns a) 
        = cat [ptext "\\" <> 
                         (hsep $ map (pprRVN) rvns)
               <+> ptext "->" <> space, ppr a]
    ppr (LamAP Nothing as)
        = sep [ parens (hsep $ punctuate comma $  map ppr as) ]
    ppr (LamAP (Just []) as) 
        = sep [ parens (hsep $ punctuate comma $ map ppr as ) ]
    ppr (LamAP (Just nss) as)
        = sep [ ptext "\\" <>
                (hsep $ map (\ns -> pprTup (map ppr ns)) nss) <>
                ptext "->",
                parens (hsep $ punctuate comma $ map ppr as) ]
    ppr (AppA a []) 
        = ppr a 
    ppr (AppA a ns) 
        = sep [parens (ppr a), ptext "$",
               (hsep $ map ppr ns) ]
    ppr (ConA c []) 
        = ptext (show c)
    ppr (ConA c as)
        = ptext (show c) <> parens (hcat $ punctuate comma $ map ppr as)
    ppr (VarA rvn) 
        = pprRVN rvn
    ppr (FieldA rvn fn) 
        = pprRVN rvn <> ptext "." <> ptext (show fn)
    ppr (RecordA fas) 
        = braces (sep $ punctuate comma $
                       map (\(f,a) -> ptext (show f) <> colon <> ppr a) fas)
    ppr (MergeA [])  = ptext "{}"
    ppr (MergeA [x]) = pprRVN x
    ppr (MergeA rvns) 
        = (hcat $ punctuate (ptext "*") $ map (pprRVN) rvns)
    ppr (MarkA) 
        = ptext "__"
    -- ppr (ProdA [a]) = ppr a 
    -- ppr (ProdA acts) 
    --     = hcat [ptext "<",
    --             (sep $ punctuate comma $ map ppr acts),
    --             ptext ">"]
    ppr (LetA bind a) 
        = sep [ptext "let" <+>
               braces (sep $ punctuate semi $ 
                           map (\(v,a) -> pprRVN v <+> ptext "=" <+> ppr a) bind),
               ptext "in" <+> ppr a]
    ppr (RunA s a) 
        = ptext ("@" ++show s) <> parens (ppr a)
    -- ppr (TakeA ls)
    --     = ptext "\\" <> 
    --       parens (hsep $ punctuate comma $  zipWith (\(j,n) i -> parens $ pprP i n) ls [1..]) <+>
    --       ptext "->" <+>
    --       parens (hsep $ punctuate comma $ zipWith (\(j,n) i -> var i (j+1)) ls [1..]) 
    --     where
    --       pprP i n = hsep $ punctuate comma $ [ var i j | j <- [1..n] ]
    --       var i j  = ptext ("w" ++ show i ++ "_" ++ show j) 
    ppr (ParA (ParA a1 a2) a3)
        = ppr (ParA a1 (ParA a2 a3))
    ppr (ParA a1 a2)          
        = let as  = takeParAs a2
          in vcat $ ( ptext " " <+> parens (ppr a1)):
                    [ ptext "|" <+> parens (ppr a) | a <- as ]
        where
          takeParAs (ParA a1 a) = a1:takeParAs a
          takeParAs a           = [a]
    ppr (CompA (CompA a3 a2) a1) 
        = ppr (CompA a3 (CompA a2 a1))
    ppr (CompA a2 a1) =
        let a1':as'  = reverse (a2:takeCompAs a1)
        in sep (parens (ppr a1'):
                [ ptext ">>>" <+> parens (ppr a) | a <- as' ])
        where
          takeCompAs (CompA a1 a) = a1:takeCompAs a
          takeCompAs a            = [a]
    ppr (CompAn 0 a2 a1) = sep [parens(ppr a2) <+> ptext "$" <+> parens (ppr a1)]
    ppr (CompAn 1 a2 a1) 
        = ppr (CompA a2 a1)
    ppr (CompAn n a2 a1) 
        = ppr a1 <+> ptext ">" <> ptext (show n) <> ptext ">" <+> ppr a2
    ppr (NullA) = ptext "_|_"
    ppr (FixA a)
        = ptext "fixA" <> brackets (ppr a)
--    ppr s       = ptext $ show s  -- seems that all cases are covered.
        
pprTup []  = parens empty
pprTup [x] = x
pprTup xs  = parens $ hcat $ punctuate comma $ xs 

pprRVN (n,fs) = ptext (show n) <> 
                braces (hcat $ punctuate comma $ map (ptext.show) fs)

instance Show AState where
    show (FromF n) = "F" ++ show n 
    show (FromE i) = "E" ++ show i 

instance Ppr AState where
    ppr s = ptext (show s)