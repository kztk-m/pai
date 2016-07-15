{-# LANGUAGE MultiParamTypeClasses, TemplateHaskell #-}
module Inverter.CodeGen (genCode) where

-- import qualified Language.Haskell.TH as TH

import qualified Syntax.MiniHaskell as H 

import Syntax.Abstract
import TreeAutomata.Automata as TA
import TreeAutomata.Guided as GTA
import Inverter.Action
--import Inverter.HSSyntax
import Util 

import Control.Monad.State

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe 
import Data.Function (on)

import Text.PrettyPrint 
import Debug.Trace



genCode :: (Ord state, Show state) =>
           (Map AState (GTA Int state Name Act), AState, Bool)
           -> [H.Dec]
genCode (gtaMap,entry,isAmb) 
    = [ H.FunD (H.mkName $ "inv_"++show entry) 
        [H.mkSimpleClause [] (if isAmb then 
                              H.VarE $ s2n entry
                            else
                              H.mkCompose
                              (H.VarE $ H.mkName "runI")
                              (H.VarE (s2n entry) ))]  ]
      ++ concat [ genCode' e gta | (e,gta) <-  Map.toList gtaMap ] 
    where genCode' :: (Ord state,Show state) =>
                      AState -> (GTA Int state Name Act) -> [H.Dec]
          genCode' e (gta@(GTA guides initGuide gMap aMap)) = 
            (genDataDecl e (snub $ GTA.states gta) isAmb )
            ++ (genEntryPoint e initGuide aMap)
            ++ (genTraverseFuncs e guides gMap aMap)
            ++ (genSemanticFuncs e aMap isAmb )

-- ifE e e1 e2 
--     = TH.CaseE e [TH.Match (TH.ConP (TH.mkName "True")  []) (TH.NormalB e1) [],
--                   TH.Match (TH.ConP (TH.mkName "False") []) (TH.NormalB e2) []]

-- | The function generates datatype decration for GTA states.
genDataDecl :: (Show entry, Show state) => entry -> [state] -> Bool -> [H.Dec]
genDataDecl e states isAmb
    = [ H.DataD dName vars cs ]
    where
      dName = H.mkName $ "StatesOf" ++ show e
      vars  = if isAmb then 
                  [ s2n s | s <- states ]++[deadStateName]
              else
                  [ s2n s | s <- states ]
      cs    = if isAmb then 
                [ H.NormalC (s2c e s) [H.VarT (s2n s)]
                |  s <- states ]
                ++ [ H.NormalC (deadStateConName e)
                     [H.VarT deadStateName] ]
              else
                  [ H.NormalC (s2c e s)
                    [H.VarT (s2n s)]
                  |  s <- states ]

-- 
--   The function generates inverse function for 
-- a state corresponding to function/expression. 
--
genEntryPoint ::
  (Show state, Show astate, Ord guide, Show guide) =>
  astate -> guide -> TAMap guide state name action -> [H.Dec]
genEntryPoint e ig aMap 
    = [ H.FunD (s2n e) [H.mkSimpleClause [H.VarP x] exp] ]
    where
      TA tMap = fromJust $ Map.lookup ig aMap
      -- FIXME: Automata should have final state.
      fs      = head $ [ dst tr 
                             | (c,trs) <- Map.toList tMap, tr <- trs ]
      errorMsg = "Input is not the range of the expression/function corresponding to the state: " ++ show e
      x  = H.mkName "x"
      y  = H.mkName "y"
      ex = (H.VarE (travName e ig)) `H.AppE` (H.VarE x)      
      exp = H.CaseE ex 
            [ H.mkSimpleMatch (H.ConP (s2c e fs) [H.VarP y]) 
                            (H.VarE y),
              H.mkSimpleMatch (H.WildP) 
                            ((H.VarE $ H.mkName "fail") `H.AppE` (H.LitE $ H.StringL $ errorMsg ) ) ]

-- | 
-- The function determines the traversing way of inverse function.
-- For a guide function 
--    G0 -> C(G1,G2)
-- it generates 
--    trav0 (C(t1,t2)) = sem0 (C(t1,t2)) t1 t2
genTraverseFuncs ::
  (Show entry, Show guide, Ord guide) =>
  entry
  -> [guide]
  -> GuideMap guide Name
  -> TAMap guide state Name action
  -> [H.Dec]
genTraverseFuncs e guides gMap aMap
    = map genTF guides 
      where
        gMap' = Map.fromListWith (++) 
                  [ (g,[(c,gs)]) 
                       | ((g,c),gs) <- Map.toList gMap ]
        genTF g =
            let fName = travName e g  
            in case Map.lookup g gMap' of
                 Just cgs ->
                     H.FunD fName $ (map mkCL $ filter (isConS . fst) cgs) ++ [finCL] -- (map mkCL $ sortBy (compare `on` fst) cgs) 
                 _ ->
                     H.FunD fName [finCL]
            where 
              finCL =
                  let var = H.mkName "t"
                      pat = H.VarP var
                      exp = H.AppE (H.VarE $ semName e g (TopS :: Symbol Name))
                                   (H.VarE var)
                  in  H.mkSimpleClause [pat] exp 
                  where
                    TA tMap = fromJust $ Map.lookup g aMap
              -- We assume 'ConsS c <= TopS' for any c 
              mkCL (ConS c,gs) = 
                  let 
                      pvars = [ H.mkName $ "t" ++ show i 
                                    | (_,i) <- zip gs [1..] ]
                      vars  = [ H.mkName $ "x" ++ show i 
                                    | (_,i) <- zip gs [1..] ]
                      pat   = H.ConP (n2n c) $ map H.VarP pvars
                      tree  = H.mkApps (H.ConE (n2n c)) $ map H.VarE pvars
                      tc g v = (H.VarE (travName e g)) `H.AppE` (H.VarE v)
                      exp   = H.mkApps 
                                (H.VarE (semName e g (ConS c))) 
                                (tree:zipWith tc gs pvars)
                  in H.mkSimpleClause [pat] exp
              mkCL (TopS,_) = finCL

-- | 
-- The function generates the state transition function of gta and variable bindings under the state.
-- Roughly, for a state transition 
--     A <- C(A1,A2) {act}
-- it generates 
--     semC tree (State_A1 t1) (State_A2 t2) = State_A $ [[act]] t1 t2 
-- NB: The variable appears as free variable in [[act]]
genSemanticFuncs ::
  (Show state, Show guide, Show entry, Show name) =>
  entry -> TAMap guide state name Act -> Bool ->  [H.Dec]  
genSemanticFuncs e aMap isAmb     -- gMap was not used and thus removed
    = concatMap (\(g,TA tMap) ->
                     map (\(c,trs) ->
                              let fName = semName e g c 
                              in H.FunD fName 
                                     $ (map (genSF g c) trs)
                                       ++ if isAmb then 
                                              failfunc g c trs
                                          else [])
                         (Map.toList tMap)
--                     ++ (if Map.member TopS tMap then [] else botfunc g)
                ) (Map.toList aMap)
    where
      failfunc g c [] = []
      failfunc g c (Tr src dst act:_)  = 
          let pats  = H.WildP:[H.WildP | _ <- src ]
          in [H.mkSimpleClause pats
                 $ (H.ConE $ deadStateConName e)
                   `H.AppE` (H.ConE $ H.mkName "mymzero")]
      -- -- FIXME: Wrong
      -- botfunc g = case Map.lookup (g,TopS) gMap of
      --               Just _ ->
      --                   let fName = semName e g TopS
      --                   in [TH.FunD fName [mkSimpleClause [] (TH.VarE fName)]]
      --               Nothing ->
      --                   []
      genSF g c (Tr src dst act) 
          = let tvar  = treeVarName
                tvars = [ H.mkName $ "t" ++ show i 
                              | (_,i) <- zip src [1..] ]
                cstates = map (s2c e) src
                dstate  = s2c e dst
                pat = H.VarP tvar:
                      [ H.ConP c [H.VarP t]
                            | (c,t) <- zip cstates tvars ]
                aex = genActExp act 
                -- exp = if False && null tvars then 
                --           aex 
                --       else
                --           let v = TH.mkName "ret" 
                --           in TH.AppE aex
                --                  (TH.TupE $ map TH.VarE tvars)
            in H.mkSimpleClause pat $
               (H.ConE dstate) `H.AppE`
                    (H.mkApps aex (map H.VarE tvars))
               -- (let v = TH.mkName "ret" 
               --  in TH.DoE $
               --     [ TH.BindS (TH.VarP v) exp,
               --       TH.NoBindS $
               --         returnE $ TH.AppE (TH.ConE $ s2c e dst) (TH.VarE v) ])

-- | Generating Haskell program corresponding to actions. 
--   Invoked by genSemanticFuncs.
genActExp :: Act -> H.Exp 
genActExp (MarkA) = H.returnE $ H.VarE treeVarName

genActExp (LamA [] a) = genActExp a 
genActExp (LamA rvns a) =
    let vs = map genR2TP rvns 
    in H.LamE vs (genActExp a) -- TH.LamE [ TH.TupP vs] (genActExp a)
genActExp (ConA n as) =
    let l = length as
        es = [ genActExp a | a <- as ]
    in applyLiftFunc l (H.ConE (n2n n)) es

    -- let vs = [ TH.mkName $ "tmp_x" ++ show i 
    --                | (_,i) <- zip as [1..] ]
    -- in TH.DoE $
    --      [ TH.BindS (TH.VarP v) (genActExp a) | (a,v) <- zip as vs ]
    --      ++ [ TH.NoBindS $ returnE $ 
    --            foldl TH.AppE (TH.ConE (n2n n)) [TH.VarE v | v <- vs ]]

genActExp (VarA rvn)     = H.returnE $ genR2TE rvn
genActExp (FieldA rvn f) = H.returnE $ genR2TiE rvn f 
genActExp (RecordA []) =
   H.returnE $ H.tupE []
genActExp (RecordA [(_,a)]) =
   genActExp a 
genActExp (RecordA rs) =
    let l   = length rs
        rs' = sortBy (compare `on` fst) rs 
        es  = [ genActExp a | (_,a) <- rs' ]
    in applyLiftFunc l (H.ConE $ H.tuple l) es

    -- let vs  = [ TH.mkName $ "tmp_f" ++ show i 
    --                | (_,i) <- zip rs [1..] ]
    --     rs' = sortBy (compare `on` fst) rs
    -- in TH.DoE $
    --     [ TH.BindS (TH.VarP v) (genActExp a) 
    --           | (v,(_,a)) <- zip vs rs' ]
    --     ++ [ TH.NoBindS $ returnE $ TH.TupE $
    --                        [ TH.VarE v | v <- vs ]]

-- genActExp (ProdA [a]) = genActExp a 
-- genActExp (ProdA as) =
--     let var = TH.mkName $ "tmp_in" 
--         vs  = [ TH.mkName $ "tmp_x" ++ show i 
--                     | (_,i) <- zip as [1..] ]
--     in TH.LamE [TH.VarP var]
--          $ TH.DoE $
--            [ TH.BindS (TH.VarP v) (TH.AppE (genActExp a) (TH.VarE var))
--                 | (a,v) <- zip as vs ]
--            ++ [ TH.NoBindS $ returnE $ TH.TupE [TH.VarE v | v <- vs ]]
-- genActExp (TakeA ls) =
--     let pat =
--             TH.TupP
--               [ TH.TupP [ TH.VarP $ var i j  | j <- [1..n] ] 
--                     | ((_,n),i) <- zip ls [1..] ]
--         exp =
--             TH.TupE 
--               [ TH.VarE $ var i (j+1) | ((j,n),i) <- zip ls [1..] ]
--         var i j = TH.mkName $ "x" ++ show i ++ "_" ++ show j
--     in TH.LamE [pat] (returnE exp)

-- genActExp (LamAP Nothing as) = 
--     let vs = [ TH.mkName $ "tmp_r" ++ show i 
--                    | (_,i) <- zip as [1..] ]
--     in  TH.LamE [TH.WildP] $ 
--           TH.DoE $
--             [ TH.BindS (TH.VarP v) (genActExp a) | (v,a) <- zip vs as ]
--             ++ [ TH.NoBindS $ returnE $ TH.TupE [ TH.VarE v | v <- vs] ]
-- genActExp (LamAP (Just nss) as) =
--     let vs = [ TH.mkName $ "tmp_r" ++ show i 
--                    | (_,i) <- zip as [1..] ]
--     in  TH.LamE [(TH.TupP $ [ TH.TupP [ TH.VarP $ n2n n | n <- ns ] | ns <- nss ])] $ 
--           TH.DoE $
--             [ TH.BindS (TH.VarP v) (genActExp a) | (v,a) <- zip vs as ]
--             ++ [ TH.NoBindS $ returnE $ TH.TupE [ TH.VarE v | v <- vs] ]

-- Current code generation rule assume that LamAP appears on the top of Act and 
-- then AppA appears at the second level.
-- e.g.
--  Monad m => (m s1, m s2) -> (m t1, m t2, m t3) -> (m u1, m u2)
genActExp (LamAP Nothing as) 
    = H.tupE [genActExp a | a <- as]
genActExp (LamAP (Just []) as) 
    = H.tupE [ genActExp a | a <- as ]
genActExp (LamAP (Just nss) as) 
    = H.LamE [ H.tupP [ H.VarP $ n2n n | n <- ns ] | ns <- nss] 
         $ H.tupE [ genActExp a | a <- as ]

genActExp (AppA a []) = genActExp a    
genActExp (AppA a ns) =
    let vs = [ H.mkName $ "tmp_r" ++ show i | (_,i) <- zip ns [1..] ]
    in H.DoE $ 
             [ H.BindS (H.VarP v) (H.VarE (n2n n)) | (v,n) <- zip vs ns ]
          ++ [ H.NoBindS $ H.mkApps (genActExp a) [ H.VarE v | v <- vs ] ]
               

-- genActExp (AppA a ns) =
--     mkApp (genActExp a) [ TH.VarE (n2n n) | n <- ns ]
-- --    TH.AppE (genActExp a) $ TH.TupE [ TH.VarE (n2n n) | n <- ns ]


genActExp (LetA bind a) =
    let bs =
            [ H.BindS (genR2TP rvn) (genActExp a)
                  | (rvn,a) <- bind ]
    in H.DoE (bs ++ [H.NoBindS $ genActExp a])

genActExp (RunA state act) =
    let bind x y = H.InfixE x (H.VarE $ H.mkName ">>=") y
        paren  x = H.tupE [x]
    in paren (bind (genActExp act) (H.VarE $ s2n state))

-- genActExp (CompA a (TakeA [])) = genActExp a 
genActExp (CompA a2 a1) =
    compEM (genActExp a1) (genActExp a2)
-- a1 is n argument 
genActExp (CompAn n a2 a1) =
    compEMn n (genActExp a1) (genActExp a2)


genActExp (ParA a1 a2) =
    mplusE (genActExp a1) (genActExp a2)
-- fix (\f x -> x ++ f (A[[a]] >=> x) ) A[[a]]
genActExp (FixA a) =
    let aex = genActExp a 
    in H.mkApps (H.VarE $ H.mkName "fixApp") [aex]
    -- let aex = genActExp a 
    --     f   = TH.mkName "f"
    --     x   = TH.mkName "x"
    --     e   = TH.LamE [TH.VarP f, TH.VarP x] $
    --             appendE (TH.VarE x) 
    --                     (TH.AppE (TH.VarE f)
    --                              (compEM aex (TH.VarE x)))
    -- in TH.AppE (TH.AppE (TH.VarE $ TH.mkName "fix") e) aex
    
genActExp (MergeA [] ) = H.returnE $ H.tupE []
genActExp (MergeA [x]) = H.returnE $ genR2TE x
genActExp (MergeA rvns) 
    = if all singleton xs then 
          H.returnE $ H.tupE
                      $ map (\[x] -> uncurry genR2TiE x) xs
      else 
          makeTupE
          -- -- FIXME
          -- returnE $ TH.TupE
          --             $ map (\x -> foldr1 eq $ map (uncurry genR2TiE) x) xs
    where singleton [x] = True
          singleton _   = False
          fs = snub $ concatMap snd rvns 
          xs = [ [ ((vn,fset),f) | (vn,fset) <- rvns, f `elem` fset ] 
                     | f <- fs]
          tvs = [ H.mkName $ "tv" ++ show i | i <- [1..length xs] ]
          makeTupE = 
              let es = map (\x -> map (uncurry genR2TiE) x) xs
              in makeTup (zip tvs es) 
                    [H.NoBindS (H.returnE $ H.tupE $ [ H.VarE t | t<-tvs ]) ] 
          makeTup [] r = H.DoE r                      
          makeTup ((t,[x]):xs) r =
              makeTup xs (H.LetS [H.ValD (H.VarP t) x]:r)
          makeTup ((t,x):xs) r =
              let ys = init x
                  y  = last x
                  e  = foldr eq (H.returnE y) (map H.returnE ys)
                  eq a b = if isReturn a && isReturn b then
                               H.mkApps (H.VarE $ H.mkName "checkEqPrim")
                                        [unReturn a, unReturn b]
                           else
                               H.mkApps (H.VarE $ H.mkName "checkEq") [a,b]
              in makeTup xs (H.BindS (H.VarP t) e:r)
          
              
              

genActExp (NullA)
    = H.VarE (H.mkName "undefined")

genActExp (IdA) 
    = error "`IdA' should not appear"

-- genActExp _ = TH.VarE 'undefined


--
-- * Other helper functions
--


-- | Generate tuple from record variable in pattern 
genR2TP :: (Show t) => (t, [a]) -> H.Pat
genR2TP (vn,vset) = 
    H.tupP $ map H.VarP $ 
          [ H.mkName $ "r_" ++ show vn ++ show i
                | (_,i) <- zip vset [1..] ]

-- | Generate tuple from record variable in expression
genR2TE :: (Show t) => (t, [a]) -> H.Exp
genR2TE (vn,vset) =
    H.tupE $ map H.VarE $ 
          [ H.mkName $ "r_" ++ show vn ++ show i
                | (_,i) <- zip vset [1..] ]

-- | Generate tuple access from field access of record
genR2TiE :: (Ord a, Show t) => (t, [a]) -> a -> H.Exp
genR2TiE (vn,vset) f =
    case elemIndex f $ sort vset of 
      Just i -> 
          H.VarE (H.mkName $ "r_" ++ show vn ++ show (i+1) )
      Nothing -> -- variable that does not occur in RHS but in LHS
          H.VarE (H.mkName $ "something")

genLiftFunc :: Int -> H.Exp
genLiftFunc n
    | n == 0 = 
        H.VarE $ H.mkName "return"
    | n == 1 = 
        H.VarE $ H.mkName "liftM"
    | n <= 5 =
        H.VarE $ H.mkName ("liftM" ++ show n)
    | otherwise = 
    let f   = H.mkName "fn" 
        pvs = [ H.mkName $ "m_" ++ show i | i <- [1..n] ]
        -- vs  = [ H.mkName $ "z_" ++ show i | i <- [1..n] ]
    in H.LamE [H.VarP v | v <- (f:pvs)] $ 
       foldl H.aappE (H.VarE (H.mkName "return") `H.appE` H.VarE f) (map H.VarE pvs)
       -- H.DoE $
        --   [ H.BindS (H.VarP v) (H.VarE pv) | (v,pv) <- zip vs pvs ]
        --   ++ [ H.NoBindS $ returnE $ 
        --           mkApp (H.VarE f) [H.VarE v | v <- vs] ] 



applyLiftFunc :: Int -> H.Exp -> [H.Exp] -> H.Exp
applyLiftFunc l x es = 
    if all isReturn es then 
        H.returnE $ H.mkApps x (map unReturn es)
    else
        H.mkApps (genLiftFunc l) $ (x:es)

isReturn :: H.Exp -> Bool 
isReturn e = 
    case e of 
      H.AppE (H.VarE x) y | x == H.mkName "return" -> True
      _                                            -> False
unReturn (H.AppE x y) = y 


-------------
n2n :: Name -> H.Name
n2n (Name n)  = H.mkName n 
n2n (IName i) = H.mkName $ "i_" ++ show i 

deadStateName :: H.Name
deadStateName = H.mkName "e_DEAD"

deadStateConName :: Show entry => entry -> H.Name
deadStateConName e = H.mkName $ "S" ++ "_" ++ show e ++ "_DEAD"

s2n :: Show state => state -> H.Name
s2n x = H.mkName $ "e_" ++ show x

s2c :: (Show state,Show entry) => entry -> state -> H.Name
s2c e s 
    = H.mkName $ "S" ++ "_"++ show e ++ "_"++show s

treeVarName :: H.Name 
treeVarName = H.mkName $ "tree" 

travName :: (Show a, Show b) => a -> b -> H.Name
travName e g 
 = H.mkName $ "trav_" ++ shows e ("_" ++ show g)

semName :: (Show state, Show entry, Show symbol) =>
           entry -> state -> symbol -> H.Name
semName e g c
 = H.mkName $ "sem_" ++ shows e ("_" ++ shows g ("_" ++ show c))

mplusE :: H.Exp -> H.Exp -> H.Exp
mplusE e1 e2 =
    ( (H.VarE $ H.mkName "mymplus")
      `H.appE` e1) `H.appE` e2


compEM :: H.Exp -> H.Exp -> H.Exp
compEM e1 e2 = -- trace (">" ++ show e1 ++ "\n>" ++show e2 ++ "\n") $ 
    case (e1,e2) of
      (H.LamE p (H.AppE (H.VarE n) e),_) | n == H.mkName "return" ->
          H.LamE p (H.AppE e2 e)
      (H.LamE p n,H.LamE [H.VarP v] m) ->
          H.LamE p (H.InfixE
                    n
                    (H.VarE $ H.mkName ">>=")
                    e2)
      (H.LamE p n,H.LamE [H.TupP [H.VarP v]] m) ->
        H.LamE p (H.InfixE
                  n
                  (H.VarE $ H.mkName ">>=")
                  e2)
      _ ->
          H.InfixE 
                e1
                (H.VarE $ H.mkName ">=>")
                e2


-- | |compEMn n f g|
--   generates  |\v1 .. vn -> g (f v1 ... vn)|
compEMn :: Int -> H.Exp -> H.Exp -> H.Exp
compEMn 0 e1 e2 =
    H.InfixE e1 (H.VarE $ H.mkName ">>=") e2
              
compEMn 1 e1 e2 = compEM e1 e2
compEMn n e1 e2 =
    let mvs = [ H.mkName ("m" ++ show i ) | i <- [1..n] ]
        f1 = H.mkName "f"
        f2 = H.mkName "g"
        ex = H.LamE [ H.VarP v | v <- (f1:f2:mvs) ] $
                 compEMn 0  
                    (H.mkApps (H.VarE f1) [H.VarE v | v <- mvs ])
                    (H.VarE f2) 
    in H.mkApps ex [e1,e2]
