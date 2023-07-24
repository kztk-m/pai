{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

{-|
A naive implementation of guided tree automaton.
-}
module TreeAutomata.Guided (
  GTA(..),   --  guided tree automata
  GuideMap, TAMap,
  mapState, states,
  renumberStates, renumberGuides,
  fromTA2GTAs,
  fromGTAtoTA, --  not used yet
  determinize,
  ) where

import qualified TreeAutomata.Automata as TA (mapState, states)
import           TreeAutomata.Automata as TA hiding (mapState, states)

import           Util

import           Text.PrettyPrint

import           Data.Map              (Map)
import qualified Data.Map              as Map
import           Data.Set              (Set)
import qualified Data.Set              as Set

import           Data.Graph
import           Data.List
import           Data.Maybe

import           Data.Monoid           hiding ((<>))

import           Data.Function         (on)

import           Debug.Trace

#if MIN_VERSION_base(4,9,0)
import           Prelude               hiding ((<>))
#endif

data GTA guide state name action
    = GTA {
        guides       :: [ guide ],
        initialGuide :: guide,
        guideMap     :: GuideMap guide name,
               -- ^ mapping guide of current node
               --   to guide
        automata     :: TAMap guide state name action
      }

type GuideMap guide name = Map (guide,Symbol name) [guide]
type TAMap guide state name action = Map guide (TA state name action)

--
-- * GTA Operations
--

mapState ::
  (Ord state, Ord state') =>
     GTA guide state name action -> Map state state' -> GTA guide state' name action
mapState (GTA guides initGuide gMap aMap) sMap
    = GTA guides initGuide gMap (Map.map (\ta -> TA.mapState ta sMap) aMap)

states :: Ord state => GTA guides state name action -> [state]
states (GTA guides initGuide gMap aMap)
    = concat $ Map.elems $ (Map.map TA.states aMap)

renumberStates ::
     (Ord state) =>
       GTA guide state name action -> GTA guide Int name action
renumberStates (gta@(GTA guides initGuide gMap aMap))
    = mapState gta sMap
      where
        states = concat $ Map.elems $ (Map.map TA.states aMap)
        sMap = Map.fromList $ zip states [0..]

renumberGuides ::
    (Ord guide, Ord name) =>
    GTA guide state name action -> GTA Int state name action
renumberGuides (GTA guides initialGuide gmap amap)
    = GTA [0..(length guides - 1)]
          (k2i initialGuide)
          (Map.map (map k2i) $ Map.mapKeys (\(k,s) -> (k2i k,s)) $ gmap)
          (Map.mapKeys k2i amap)
    where
      k2i k = case elemIndex k guides of { Just v -> v }


--
-- * TA <-> GTA Conversion
--

-- fromTA2GTANaive ::
--     (Ord state, Ord name)
--     => TA state name action -> GTA (Set state) state name action
-- fromTA2GTANaive (TA tMap)
--     = GTA [ Set.empty ]
--           Set.empty
--           (Map.fromList [ ((Set.empty,c), replicate n (Set.empty))
--                           | (c,n) <- cs ])
--           (Map.fromList [ (Set.empty, TA tMap) ])
--       where cs = nub $ concat $ Map.elems
--                      $ Map.mapWithKey (\(ConS c) v->
--                                              [ (c,length (src tr)) | tr <- v ])
--                      $ Map.filterWithKey (\k v -> isConS k) tMap


{-|
The following function applies subset-construction to make
guided tree automaton from tree automaton.

Since how to choose guide depends on the final state of tree automaton.
Since the TA definition above does not require final state of tree automata,
the return value of this function is mapping from a state to
the guided tree automata corresponding to the state.

It is worth noting that acording to algorithm,
the function always returns reduced GTAs.
-}
fromTA2GTAs ::
      (Ord state,Ord name, Action action) =>
        TA state name action -> [state]
          -> Map state (GTA (Set state) state name action)
fromTA2GTAs ta states
    = let ta' = TA.eliminateEps ta
          gtas = map (\s -> (s,fromTA2GTA ta' s)) states
      in Map.fromList gtas


fromTA2GTA ::
    (Ord state,Ord name) =>
        TA state name action -> state
        -> GTA (Set state) state name action
fromTA2GTA (ta@(TA tMap)) state
    = let ig   = Set.singleton state
          (guides,gMap)
               = fixStep ig [] (Map.empty)
          aMap = makeAMapFromStateSets guides ta
      in GTA (reverse guides) ig (updateAGs (initA guides) gMap) aMap
    where
      tMapC  = Map.filterWithKey (\k v -> isConS k) tMap
      initA gs = Set.fromList $ [ g | tr <- lookupMono TopS tMap, g <- gs, Set.member (dst tr) g ]
      updateAGs gs gMap =
          let gs'  = Set.fromList $ [ g' | ((g,c),gs') <- Map.toList gMap, Set.member g gs, g' <- gs' ]
              gs'' = Set.union gs gs'
          in if Set.size gs == Set.size gs'' then
                 Set.fold (\g m -> Map.insert (g,TopS) [] m) gMap gs
             else
                 updateAGs gs'' gMap
      fixStep g guides gMap
          | g `elem` guides = (guides, gMap)
          | otherwise =
              let nextMap =
                    [ (ConS c, map Set.singleton src)
                          | (ConS c, trs) <- Map.toList tMapC,
                            (Tr src dst act) <- trs, Set.member dst g ]
                  gMapDelta =
                    Map.mapKeys (\c -> (g,c)) $
                        Map.fromListWith (zipWith Set.union) nextMap
                  gMap0   = gMap `Map.union` gMapDelta
                  guides0 = g:guides
              in Map.foldr (\gs (guides,gMap) ->
                               foldr (\g (s,m) -> fixStep g s m)
                                     (guides,gMap) gs) (guides0,gMap0) gMapDelta

{-|
It is always possible that GTA is converted to TA.
Note that expressive power of GTA is equivalent to TA.

g --> C(g1,g2,g3)

g:
   s <-- C(s1,s2,s3)

==>
(g,s) <-- C((g1,s1),(g2,s2),(g3,s3))
-}
fromGTAtoTA :: (Ord guide, Ord state, Ord name) =>
                GTA guide state name action
                -> (TA (guide,state) name action, [(guide,state)])
fromGTAtoTA (GTA _ ig gMap aMap) =
    let tMap' = Map.fromListWith (++)
                   [ (c,map (conv g) trs)
                         | (g,TA tMap) <- Map.toList aMap,
                           (c,trs) <- Map.toList tMap ]
    in (TA tMap', filter ((== ig) . fst) $ TA.states (TA tMap'))
        where
          conv g (Tr src dst act) = Tr (map f src) (f dst) act
              where f state = (g,state)



makeAMapFromStateSets ::
    (Ord state, Ord name) =>
      [Set state] -> TA state name action
      -> Map (Set state) (TA state name action)
makeAMapFromStateSets guides (TA tMap) =
    Map.fromList
           $ map (\gs -> (gs,TA $ Map.filter (not.null)
                                $ Map.map (filter (f gs)) tMap))
                 $ guides
        where
          f gs (Tr _ g' _) = Set.member g' gs


--
-- Are these for debugging?
--

data PreTr state = PreTr { presrc :: [state], predst :: state }
                   deriving (Show,Eq,Ord)

instance Ppr state => Ppr (PreTr state) where
    ppr (PreTr src dst) =
        (ppr dst) <+> ptext "<--" <+>
        parens (hsep (punctuate comma $ map ppr src))

tr2pretr tr = PreTr (src tr) (dst tr)

{-|
Determinization.

 s1 <-- c(s1,s2) { a1 }
 s2 <-- c(s2,s1) { a2 }
 s3 <-- c(s2,s2) { a3 }
 s1 <-- n        { a4 }
 s2 <-- n        { a5 }

==>
 {s1,s2}    <-- n
      { tupleA [a4,a5] }
 {s1,s2,s3} <-- c({s1,s2},{s1,s2})
      { tupleA [ (a1 `compA` takeA [(0,2),(1,2)]),
                 (a2 `compA` takeA [(1,2),(0,2)]),
                 (a3 `compA` takeA [(1,2),(1,2)]) ] }

NB:
 We must care about dead state here.
 We insert dead state as follows for some reasons.
 g:
   A    <-- c() {...}
   Dead <-- _   { () }
-}

-- 1. We compute determinized GTA without action
--    by subset construction.
-- 2. We convert states of the determinized GTA from
--    set to list.
-- 3. We compute "tupled" actions
determinize ::
     (Ord state, Ord name, Ord guide, Action action) =>
     GTA guide state name action -> GTA guide [state] name action
determinize (gta@(GTA guides initG gMap aMap))
    = GTA guides initG gMap aMap''
      where
        fromJust' (Just x) = x
        aMap' = Map.mapWithKey (\g (TA tMap) ->
                    TA $ Map.mapWithKey (\c trs ->
                         let trs' = if isTopS c then
                                        []
                                    else
                                        lookupMono TopS tMap
                             ptrs = lookupMono c (snd $ fromJust $ Map.lookup g stMapFix)
                         in applyTupling ([(tr',True)|tr'<-trs']++[(tr,False)|tr <- trs]) ptrs) tMap) aMap
        aMap'' = Map.map (\(TA tMap) ->
                              if Map.member TopS tMap then
                                  TA tMap
                              else
                                  TA $ Map.insert TopS [Tr [] [] (nullA)] tMap) aMap'
        anyMap = Map.map (\(TA tMap) -> Set.fromList $ map dst $
                                        lookupMono TopS tMap) aMap
        conMap = Map.map (\(TA tMap) -> [ ConS c | ConS c <- Map.keys tMap]) aMap
        s = Set.singleton
        initStMap =
            Map.map (\(TA tMap) ->
                         let trs   = lookupMono TopS tMap
                             tMap' = Map.filterWithKey (\k v -> isTopS k) tMap
                             tMap'' = Map.fromListWith (\(PreTr x d) (PreTr _ d') -> PreTr x (Set.union d d'))
                                         [ (c,PreTr [] (s d)) | (c,trs) <- Map.toList tMap', Tr _ d _ <- trs ]
                         in (s (Set.fromList $ map dst $ trs),
                             Map.map (\tr -> [tr]) tMap'')) aMap
        stMapFix = Map.map (\(states,transitions) ->
                             (states,
                              Map.map (map (\(PreTr src dst)
                                            -> PreTr (map Set.toList src) (Set.toList dst) )) transitions)) $
                     fixStep initStMap
        fixStep stMap =
            let stMap' = detStep stMap
            in if checkSize stMap stMap' then
                   fixStep stMap'
               else
                   stMap
            where
              checkSize stMap stMap'
                  = let gs = Map.keys stMap
                    in or $ map (\g -> compare (Map.lookup g stMap) (Map.lookup g stMap')) gs
              compare (Just (_,t)) (Just (_,t')) =
                  Map.size t /= Map.size t' ||
                    ( (sum $ Map.elems $ Map.map length t) /= (sum $ Map.elems $ Map.map length t') )
              compare Nothing Nothing            = False
              compare _ _ = True
        detStep stMap =
            Map.mapWithKey (eachStep stMap) stMap
        eachStep stMap g (states, transitions)
            = foldr (update g stMap (fromJust $ Map.lookup g aMap))
                    (states,transitions) $ lookupMono g conMap
        update g stMap (TA tMap) c (states, transitions) =
            case Map.lookup (g,c) gMap of
              Nothing -> (states, transitions)
              Just gs' ->
                  let childrenStates
                          = [ Set.toList
                              $ fst $ fromJust $ Map.lookup g' stMap | g' <- gs' ]
                      possibleChildrenStates
                          = combination childrenStates
                  in foldr upd (states, transitions) possibleChildrenStates
            where
              trs    = lookupMono c tMap
              anyDst = lookupMono g anyMap
              upd childrenStates (states, transitions) =
                  let nextStates
                          = anyDst `Set.union`
                               Set.fromList [ dst tr | tr <- trs,
                                                       and (zipWith Set.member (src tr) childrenStates) ]
                      cPTrs = lookupMono c transitions
                      pTr   = PreTr childrenStates nextStates
                  in if pTr `elem` cPTrs || Set.null nextStates then
                         (states, transitions)
                     else
                         ((s nextStates) `Set.union` states,
                          Map.insertWith (++) c [pTr] transitions)
        applyTupling trsF ptrs = -- (\s -> trace (render $ ptext ">>>" <> ppr s) s) $
            let v = [ (PreTr presrc predst,
                       [ (dst, [ if isTop then
                                     (Nothing,act)
                                 else
                                     (Just [ (fromJust $ elemIndex s ss, length ss) | (s,ss) <- zip src presrc ],act) ] )
                         | (Tr src dst act,isTop) <- trsF,
                            and (zipWith elem src presrc), dst `elem` predst ])
                       | PreTr presrc predst <- ptrs ]
                v' = map (\(p,x) ->
                              let xx = groupBy ((==) `on` fst) $ sortBy (compare `on` fst) x
                                  x' = map (\v -> case v of
                                                    [x] -> x
                                                    xs  -> foldr1 app xs) xx
                                  app (d, y) (_, y') = (d,y++y')
                              in (p,x')) v
            in map (\(p,x) -> Tr (presrc p) (predst p)
                                       (tuplingA (length $ presrc p) [ fromJust $ lookup d x | d <- (predst p) ])) v'
            -- let v = [ (PreTr presrc predst,
            --            [ (dst, act `compA`
            --                  takeA [ (fromJust $ elemIndex s ss,length ss)
            --                              | (s,ss) <- zip src presrc ] )
            --              | Tr src dst act <- trs,
            --                and (zipWith elem src presrc), dst `elem` predst ] )
            --           | PreTr presrc predst <- ptrs ]
            --     v' = map (\(p,x) ->
            --                   let xx = groupBy ((==) `on` fst) $ sortBy (compare `on` fst) x
            --                       x' = map (\v -> case v of
            --                                         [x] -> x
            --                                         xs  -> foldr1 parAs xs) xx
            --                       parAs = \(d,a) (_,b) -> (d,parA a b)
            --                   in (p,x')) v
            -- in map (\(p,x) -> Tr (presrc p) (predst p)
            --                      (tupleA [ fromJust $ lookup d x | d <- (predst p) ])) v'

lookupMono :: (Ord k, Monoid m) => k -> Map k m -> m
lookupMono c m = case Map.lookup c m of
                Nothing -> mempty
                Just xs -> xs

{-|
 Calculate all the combinations, non-deterministically.

 [1,4] `elem` combination [ [1,2,3], [4,5,6] ]
 [2,6] `elem` combination [ [1,2,3], [4,5,6] ]
 [1,6] `elem` combination [ [1,2,3], [4,5,6] ]
-}
combination :: [ [a] ] -> [ [a] ]
combination [] = return []
combination (x:xs) =
    do { q <- x
       ; qs <- combination xs
       ; return (q:qs) }


--
-- * Pretty Printing
--

instance (Ppr guide, Ppr state, Ppr name, Ppr action, Eq guide)
         => Ppr (GTA guide state name action) where
  ppr (GTA guides initGuide gMap aMap) =
      ptext "INITIAL GUIDE" <> colon $$
      nest 4 (ppr initGuide) $+$
      ptext "GUIDE FUNCTION" <> colon $$
      nest 4 (pprGF guides gMap) $+$
      ptext "GUIDED TRANSITIONS" <> colon $$
      (vcat $ map (\(g,ta) ->
                       nest 4 (ppr g) <> colon $+$
                       nest 8 (ppr ta)) (Map.toList aMap))
    where
      pprGF gs gMap =
          let list  = Map.toList gMap
              gUsed = [ g | ((g,c),gs) <- list ]
              gRest = gs \\ gUsed
          in vcat (map (\((g,c),gs) ->
                      ppr g <+> ptext "-->" <+>
                      ppr c <> parens (hcat $ punctuate comma (map ppr gs))) list) $$
             vcat (map (\g ->
                            ppr g <+> ptext "-->" <+> ptext "__") gRest)

instance (Show guide, Show state, Show name, Show action, Eq guide)
         => Show (GTA guide state name action) where
  show (GTA guides initialGuide guideMap aMap) =
      "INITIAL GUIDE: " ++ show initialGuide ++ "\n" ++
      "GUIDE FUNCTION: \n" ++ showGF guides guideMap ++ "\n" ++
      "GUIDED TRANSITIONS: \n" ++
      (intercalate "\n" $
           map (\(g,ta) ->
                    "  " ++ show g ++ ":\n" ++
                    showTA 4 ta ) (Map.toList aMap))
      where
        showGF gs gMap =
            let list  = Map.toList gMap
                gUsed = [ g | ((g,c),gs) <- list ]
                gRest = gs \\ gUsed
            in renderTable $
                  map (\((g,c),gs) ->
                        [ "  ", show g,
                          " --> ",
                          show c ++ "(" ++ intercalate "," (map show gs) ++ ")"]) list ++
                  map (\g -> ["  ", show g, " --> ", "__"]) gRest



-- Debugging. Unused.

traceAt :: Show a => a -> a
traceAt = \s -> trace (show s) s

-- are these for debugging?

debugS s  = trace ("<<<"++s++">>>")

showMap :: (Show k, Show a, Ord k) => Map k a -> String
showMap m =
    let ks = Map.keys m
    in "{" ++
       (renderTable $
         map (\k -> [ show k, ": ", show $ fromJust $ Map.lookup k m ]) ks)
       ++ "}"

showSet :: (Show a) => Set a -> String
showSet s =
    "{"++intercalate "," (map show $ Set.elems s) ++ "}"

showSM :: (Show a, Show k, Show v, Ord k) => (Set a, Map k v) -> String
showSM (s,m) = showSet s ++ showMap m

showStMap :: (Show k, Show a, Show k1, Show v, Ord k1, Ord k) =>
                Map k (Set a, Map k1 v) -> String
showStMap m =
    let ks = Map.keys m
    in renderTable $
        map (\k -> [ show k, ": ", showSM $ fromJust $ Map.lookup k m ]) ks
