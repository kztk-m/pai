{-# OPTIONS -XMultiParamTypeClasses -XTemplateHaskell #-}
module Inverter.CodeGen (genCode) where

import qualified Language.Haskell.TH as TH

import Syntax.Abstract
import TreeAutomata.Automata as TA
import TreeAutomata.Guided as GTA
import Inverter.Action
import Inverter.HSSyntax
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
           -> [TH.Dec]
genCode (gtaMap,entry,isAmb) 
    = [ TH.FunD (TH.mkName $ "inv_"++show entry) 
          [mkSimpleClause [] (if isAmb then 
                                  TH.VarE $ s2n entry
                              else 
                                  TH.InfixE 
                                        (Just $ TH.VarE $ TH.mkName "runI") 
                                        (TH.VarE $ TH.mkName ".")
                                        (Just $ TH.VarE (s2n entry) ))]  ]
      ++ concat [ genCode' e gta | (e,gta) <-  Map.toList gtaMap ] 
    where genCode' :: (Ord state,Show state) =>
                      AState -> (GTA Int state Name Act) -> [TH.Dec]
          genCode' e (gta@(GTA guides initGuide gMap aMap)) = 
            (genDataDecl e (snub $ GTA.states gta) isAmb )
            ++ (genEntryPoint e initGuide aMap)
            ++ (genTraverseFuncs e guides gMap aMap)
            ++ (genSemanticFuncs e aMap isAmb )

-- ifE e e1 e2 
--     = TH.CaseE e [TH.Match (TH.ConP (TH.mkName "True")  []) (TH.NormalB e1) [],
--                   TH.Match (TH.ConP (TH.mkName "False") []) (TH.NormalB e2) []]

-- | The function generates datatype decration for GTA states.
genDataDecl :: (Show entry, Show state) => entry -> [state] -> Bool -> [TH.Dec]
genDataDecl e states isAmb
    = [ TH.DataD [] dName vars cs [] ]
    where
      dName = TH.mkName $ "StatesOf" ++ show e
      vars  = if isAmb then 
                  [ s2n s | s <- states ]++[deadStateName]
              else
                  [ s2n s | s <- states ]
      cs    = if isAmb then 
                  [ TH.NormalC (s2c e s)
                               [(TH.NotStrict,TH.VarT (s2n s))]
                    |  s <- states ]
                  ++ [ TH.NormalC (deadStateConName e)
                                      [(TH.NotStrict,TH.VarT deadStateName)]]
              else
                  [ TH.NormalC (s2c e s)
                               [(TH.NotStrict,TH.VarT (s2n s))]
                    |  s <- states ]

-- 
--   The function generates inverse function for 
-- a state corresponding to function/expression. 
--
genEntryPoint ::
  (Show state, Show astate, Ord guide, Show guide) =>
  astate -> guide -> TAMap guide state name action -> [TH.Dec]
genEntryPoint e ig aMap 
    = [ TH.FunD (s2n e) [mkSimpleClause [TH.VarP x] exp] ]
    where
      TA tMap = fromJust $ Map.lookup ig aMap
      -- FIXME: Automata should have final state.
      fs      = head $ [ dst tr 
                             | (c,trs) <- Map.toList tMap, tr <- trs ]
      errorMsg = "Input is not the range of the expression/function corresponding to the state: " ++ show e
      x  = TH.mkName "x"
      y  = TH.mkName "y"
      ex = (TH.VarE (travName e ig)) `TH.AppE` (TH.VarE x)      
      exp = TH.CaseE ex 
            [ mkSimpleMatch (TH.ConP (s2c e fs) [TH.VarP y]) 
                            (TH.VarE y),
              mkSimpleMatch (TH.WildP) 
                            ((TH.VarE $ TH.mkName "fail") `TH.AppE` (TH.LitE $ TH.StringL $ errorMsg ) ) ]

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
  -> [TH.Dec]
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
                     TH.FunD fName $ (map mkCL $ filter (isConS . fst) cgs) ++ [finCL] -- (map mkCL $ sortBy (compare `on` fst) cgs) 
                 _ ->
                     TH.FunD fName [finCL]
            where 
              finCL =
                  let var = TH.mkName "t"
                      pat = TH.VarP var
                      exp = TH.AppE (TH.VarE $ semName e g (TopS :: Symbol Name))
                                    (TH.VarE var)
                  in  mkSimpleClause [pat] exp 
                  where
                    TA tMap = fromJust $ Map.lookup g aMap
              -- We assume 'ConsS c <= TopS' for any c 
              mkCL (ConS c,gs) = 
                  let 
                      pvars = [ TH.mkName $ "t" ++ show i 
                                    | (_,i) <- zip gs [1..] ]
                      vars  = [ TH.mkName $ "x" ++ show i 
                                    | (_,i) <- zip gs [1..] ]
                      pat   = TH.ConP (n2n c) $ map TH.VarP pvars
                      tree  = mkApp (TH.ConE (n2n c)) $ map TH.VarE pvars
                      tc g v = (TH.VarE (travName e g)) `TH.AppE` (TH.VarE v)
                      exp   = mkApp 
                                (TH.VarE (semName e g (ConS c))) 
                                (tree:zipWith tc gs pvars)
                  in mkSimpleClause [pat] exp
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
  entry -> TAMap guide state name Act -> Bool ->  [TH.Dec]  
genSemanticFuncs e aMap isAmb     -- gMap was not used and thus removed
    = concatMap (\(g,TA tMap) ->
                     map (\(c,trs) ->
                              let fName = semName e g c 
                              in TH.FunD fName 
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
          let pats  = TH.WildP:[TH.WildP | _ <- src ]
          in [mkSimpleClause pats
                 $ (TH.ConE $ deadStateConName e)
                   `TH.AppE` (TH.ConE $ TH.mkName "mymzero")]
      -- -- FIXME: Wrong
      -- botfunc g = case Map.lookup (g,TopS) gMap of
      --               Just _ ->
      --                   let fName = semName e g TopS
      --                   in [TH.FunD fName [mkSimpleClause [] (TH.VarE fName)]]
      --               Nothing ->
      --                   []
      genSF g c (Tr src dst act) 
          = let tvar  = treeVarName
                tvars = [ TH.mkName $ "t" ++ show i 
                              | (_,i) <- zip src [1..] ]
                cstates = map (s2c e) src
                dstate  = s2c e dst
                pat = TH.VarP tvar:
                      [ TH.ConP c [TH.VarP t]
                            | (c,t) <- zip cstates tvars ]
                aex = genActExp act 
                -- exp = if False && null tvars then 
                --           aex 
                --       else
                --           let v = TH.mkName "ret" 
                --           in TH.AppE aex
                --                  (TH.TupE $ map TH.VarE tvars)
            in mkSimpleClause pat $
               (TH.ConE dstate) `TH.AppE`
                    (mkApp aex (map TH.VarE tvars))
               -- (let v = TH.mkName "ret" 
               --  in TH.DoE $
               --     [ TH.BindS (TH.VarP v) exp,
               --       TH.NoBindS $
               --         returnE $ TH.AppE (TH.ConE $ s2c e dst) (TH.VarE v) ])

-- | Generating Haskell program corresponding to actions. 
--   Invoked by genSemanticFuncs.
genActExp :: Act -> TH.Exp 
genActExp (MarkA) = returnE $ TH.VarE treeVarName

genActExp (LamA [] a) = genActExp a 
genActExp (LamA rvns a) =
    let vs = map genR2TP rvns 
    in TH.LamE vs (genActExp a) -- TH.LamE [ TH.TupP vs] (genActExp a)
genActExp (ConA n as) =
    let l = length as
        es = [ genActExp a | a <- as ]
    in applyLiftFunc l (TH.ConE (n2n n)) es

    -- let vs = [ TH.mkName $ "tmp_x" ++ show i 
    --                | (_,i) <- zip as [1..] ]
    -- in TH.DoE $
    --      [ TH.BindS (TH.VarP v) (genActExp a) | (a,v) <- zip as vs ]
    --      ++ [ TH.NoBindS $ returnE $ 
    --            foldl TH.AppE (TH.ConE (n2n n)) [TH.VarE v | v <- vs ]]

genActExp (VarA rvn)     = returnE $ genR2TE rvn
genActExp (FieldA rvn f) = returnE $ genR2TiE rvn f 
genActExp (RecordA []) =
   returnE $ TH.TupE []
genActExp (RecordA [(_,a)]) =
   genActExp a 
genActExp (RecordA rs) =
    let l   = length rs
        rs' = sortBy (compare `on` fst) rs 
        es  = [ genActExp a | (_,a) <- rs' ]
    in applyLiftFunc l (TH.ConE $ tuple l) es

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
    = TH.TupE [genActExp a | a <- as]
genActExp (LamAP (Just []) as) 
    = TH.TupE [ genActExp a | a <- as ]
genActExp (LamAP (Just nss) as) 
    = TH.LamE [ TH.TupP [ TH.VarP $ n2n n | n <- ns ] | ns <- nss] 
         $ TH.TupE [ genActExp a | a <- as ]

genActExp (AppA a []) = genActExp a    
genActExp (AppA a ns) =
    let vs = [ TH.mkName $ "tmp_r" ++ show i | (_,i) <- zip ns [1..] ]
    in TH.DoE $ 
             [ TH.BindS (TH.VarP v) (TH.VarE (n2n n)) | (v,n) <- zip vs ns ]
          ++ [ TH.NoBindS $ mkApp (genActExp a) [ TH.VarE v | v <- vs ] ]
               

-- genActExp (AppA a ns) =
--     mkApp (genActExp a) [ TH.VarE (n2n n) | n <- ns ]
-- --    TH.AppE (genActExp a) $ TH.TupE [ TH.VarE (n2n n) | n <- ns ]


genActExp (LetA bind a) =
    let bs =
            [ TH.BindS (genR2TP rvn) (genActExp a)
                  | (rvn,a) <- bind ]
    in TH.DoE (bs ++ [TH.NoBindS $ genActExp a])

genActExp (RunA state act) =
    let bind x y = TH.InfixE (Just x) (TH.VarE $ TH.mkName ">>=") (Just y)
        paren  x = TH.TupE [x]
    in paren (bind (genActExp act) (TH.VarE $ s2n state))

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
    in mkApp (TH.VarE $ TH.mkName "fixApp") [aex]
    -- let aex = genActExp a 
    --     f   = TH.mkName "f"
    --     x   = TH.mkName "x"
    --     e   = TH.LamE [TH.VarP f, TH.VarP x] $
    --             appendE (TH.VarE x) 
    --                     (TH.AppE (TH.VarE f)
    --                              (compEM aex (TH.VarE x)))
    -- in TH.AppE (TH.AppE (TH.VarE $ TH.mkName "fix") e) aex
    
genActExp (MergeA [] ) = returnE $ TH.TupE []
genActExp (MergeA [x]) = returnE $ genR2TE x
genActExp (MergeA rvns) 
    = if all singleton xs then 
          returnE $ TH.TupE
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
          tvs = [ TH.mkName $ "tv" ++ show i | i <- [1..length xs] ]
          makeTupE = 
              let es = map (\x -> map (uncurry genR2TiE) x) xs
              in makeTup (zip tvs es) 
                    [TH.NoBindS (returnE $ TH.TupE $ [ TH.VarE t | t<-tvs ]) ] 
          makeTup [] r = TH.DoE r                      
          makeTup ((t,[x]):xs) r =
              makeTup xs (TH.LetS [TH.ValD (TH.VarP t) (TH.NormalB x) []]:r)
          makeTup ((t,x):xs) r =
              let ys = init x
                  y  = last x
                  e  = foldr eq (returnE y) (map returnE ys)
                  eq a b = if isReturn a && isReturn b then
                               mkApp (TH.VarE $ TH.mkName "checkEqPrim")
                                     [unReturn a, unReturn b]
                           else
                               mkApp (TH.VarE $ TH.mkName "checkEq") [a,b]
              in makeTup xs (TH.BindS (TH.VarP t) e:r)
          
              
              

genActExp (NullA)
    = TH.VarE (TH.mkName "undefined")

genActExp (IdA) 
    = error "`IdA' should not appear"

-- genActExp _ = TH.VarE 'undefined


--
-- * Other helper functions
--


-- | Generate tuple from record variable in pattern 
genR2TP :: (Show t) => (t, [a]) -> TH.Pat
genR2TP (vn,vset) = 
    TH.TupP $ map TH.VarP $ 
          [ TH.mkName $ "r_" ++ show vn ++ show i
                | (_,i) <- zip vset [1..] ]

-- | Generate tuple from record variable in expression
genR2TE :: (Show t) => (t, [a]) -> TH.Exp
genR2TE (vn,vset) =
    TH.TupE $ map TH.VarE $ 
          [ TH.mkName $ "r_" ++ show vn ++ show i
                | (_,i) <- zip vset [1..] ]

-- | Generate tuple access from field access of record
genR2TiE :: (Ord a, Show t) => (t, [a]) -> a -> TH.Exp
genR2TiE (vn,vset) f =
    case elemIndex f $ sort vset of 
      Just i -> 
          TH.VarE (TH.mkName $ "r_" ++ show vn ++ show (i+1) )
      Nothing -> -- variable that does not occur in RHS but in LHS
          TH.VarE (TH.mkName $ "something")

genLiftFunc :: Int -> TH.Exp
genLiftFunc n
    | n == 0 = 
        TH.VarE $ TH.mkName "return"
    | n == 1 = 
        TH.VarE $ TH.mkName "liftM"
    | n <= 5 =
        TH.VarE $ TH.mkName ("liftM" ++ show n)
    | otherwise = 
    let f   = TH.mkName "fn" 
        pvs = [ TH.mkName $ "m_" ++ show i | i <- [1..n] ]
        vs  = [ TH.mkName $ "z_" ++ show i | i <- [1..n] ]
    in TH.LamE [TH.VarP v | v <- (f:pvs)] $ 
        TH.DoE $
          [ TH.BindS (TH.VarP v) (TH.VarE pv) | (v,pv) <- zip vs pvs ]
          ++ [ TH.NoBindS $ returnE $ 
                  mkApp (TH.VarE f) [TH.VarE v | v <- vs] ] 



applyLiftFunc l x es = 
    if all isReturn es then 
        returnE $ mkApp x (map unReturn es)
    else
        mkApp (genLiftFunc l) $ (x:es)

isReturn e = 
    case e of 
      TH.AppE (TH.VarE x) y | x == TH.mkName "return" -> True
      _                                               -> False
unReturn (TH.AppE x y) = y 
