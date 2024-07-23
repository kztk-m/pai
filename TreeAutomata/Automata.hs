{-# LANGUAGE CPP #-}

-- | Tree Automata
module TreeAutomata.Automata (
  TA(..),                    --  tree automata 
  Tr(..),                    --  transition
  Symbol(..),                 
  Action(..),
  isConS, isTopS, isEpsS,
  states, mapState,
  eliminateEps,
  checkAmbiguity,
  showTA
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Maybe
import Data.List

import Data.Monoid hiding ((<>))
import Data.Function (on)

import Control.Monad (mzero, mplus)
import Control.Monad.State hiding (mapState)

import Text.PrettyPrint 

import Util

import Debug.Trace

#if MIN_VERSION_base(4,9,0)
import           Prelude          hiding ((<>))
#endif

newtype TA state name action 
    = TA (Map (Symbol name) [Tr state action]) 
-- ^ NB: length of src is determined by symbol.

data Tr state action 
    = Tr { src :: [state], 
           dst :: state,
           act :: action }
  
--
-- * Symbol.
--

data Symbol name 
    = ConS name    -- ^ a constructor
    | TopS         -- ^ any symbol
    | EpsS         -- ^ epsilon transition
      deriving (Eq,Ord)

isConS (ConS _) = True
isConS _        = False
isTopS (TopS)   = True
isTopS _        = False
isEpsS (EpsS) = True
isEpsS _      = False   

--
-- * TA Operations
--

states :: Ord state => TA state name action -> [state]
states (TA tMap) = 
    Set.toList $
       Map.foldr (\trs s -> 
                     foldr (\tr s ->
                                Set.fromList (dst tr:src tr) `Set.union` s)
                           s trs)
                (Set.empty) tMap

mapState :: 
    (Ord state, Ord state') =>
    TA state name action -> Map state state' 
    -> TA state' name action
mapState (TA transitions) sMap  
    = TA $ Map.map (map convert) transitions 
      where
        f = fromJust . (mapToFunction sMap)
        convert (Tr src dst act) = Tr (map f src) (f dst) act

--
-- * Actions
--

class Action a where
    compA  :: a -> a -> a            -- ^ Sequential composition
                                     --   compA f g implies "f AFTER g".
    compAn :: Int -> a -> a -> a     -- ^ compAn 2 f g -- \x y -> g (f x y)
                                     --   compAn 3 f g -- \x y z -> g (f x y z)
    parA  :: a -> a -> a             -- ^ Non Deterministic Computation
    fixA  :: a -> a                  -- ^ fixA a = a `parA` (a `comp` a) `parA` 
                                     --             (a `comp` a `comp` a) `parA` ...
    fixA a = a `parA` ((fixA a) `compA` a)
               
    tuplingA :: Int -> [ [ (Maybe [(Int,Int)] ,a) ] ] -> a
               -- ^ tuplingA 2 [ [ ([ (i1,n),(j1,m) ],a) ], 
               --              [ ([ (i2,n),(j2,m) ],a2), ([ (i3,n),(j3,m) ],a3) ] ]
               --                 = \(x1,...,xn) (x1,.....,xn) ->  
               --                       ( a1 xi1 xj1, a2 xi2 yi2 `parA` a3 xi3 yi3 ) 
    nullA :: a
    idA :: a

    -- f `compA` takeA [(i,n),(j,m)]  
    -- is a action corresponding to
    -- \(a1,...,ai,...,an) (b1,...,bj,...,bm) -> f ai bj
    -- takeA :: [(Int,Int)] -> a 
    -- -- tupleA [a1,a2,a3] = a1 △ a2 △ a3
    -- tupleA :: [a] -> a 

--
-- * eliminateEps
--

type Path = [PE]
data PE = SimpleE Int
        | FixE    Path
            deriving (Eq,Ord,Show)

instance Ppr PE where
    ppr (SimpleE i) = ptext (show i)
    ppr (FixE    p) = ptext "fix" <> (ppr p)


-- | The function "eliminateEps" eliminates epsilon transitions from tree automata.
{- 
NB: Action is composed via eps-elimination.
If there is eps-transtion
  "s1 <-- s2 { a1 }"
  "s2 <-- s3 { a2 }"
and a rule, 
  "s3 <-- c(s4,s5) { a }"
it generates 
  "s1 <-- c(s4,s5) { a1 `comp` a2 `comp` a }"
  "s2 <-- c(s4,s5) { a2 `comp` a }".

We must be care about (not reflexive) transitive closure 
contains "loop" as
  "s1 <-- s2 { a1 }"
  "s2 <-- s1 { a2 }"
then we have "s1 <-- s1 { fixA (a1 `comp` a2) }".


It is worth nothing that introduction of "parA" and "fixA" in the 
process implies that the grammar corresponding to input TA is ambiguous.
-}

eliminateEps :: (Ord state, Action action, Ord name) => TA state name action -> TA state name action
eliminateEps (TA tMap) = -- trace( render $ ppr extendMap ) $ 
    case eTRs of
      Nothing -> TA tMap
      Just _  -> TA $ Map.map (concatMap extendWithEps) nEpsMap 
    where
      eTRs     = Map.lookup EpsS tMap -- Epsilon Transtions
      nEpsMap  = Map.filterWithKey (\k v -> isConS k || isTopS k) tMap 
      st       = states (TA tMap) 
      eMap = Map.fromListWith (++)
               $ map (\(Tr src dst act) -> (head src, [(dst,act)])) (fromJust eTRs)
      extendMap = f $ Map.fromListWith (++) $
                       [ (k1, [ (k2,a) | a <- as ] ) 
                           | ((k1,k2),as) <- Map.toList $ fromGraphToRegex eMap compA fixA idA ]
          where f x = foldr c x st
                c s m = if Map.member s m then 
                            m
                        else
                            Map.insert s [(s,idA)] m                         
      extendWithEps (Tr src dst act) = -- trace (render $ ppr $ lookupMono dst extendMap ) $ 
          let ls = lookupMono dst extendMap 
          in [Tr src d (compAn (length src) a act) | (d,a) <- ls ]

--
-- * Utilitity
--

mapToFunction :: Ord a => Map a b -> (a -> Maybe b)
mapToFunction m a = Map.lookup a m 

lookupMono :: (Ord k, Monoid m) => k -> Map k m -> m
lookupMono c m = case Map.lookup c m of 
                Nothing -> mempty
                Just xs -> xs

-- | used internally
--   Warshall-Floyd like method is used.
fromGraphToRegex :: 
     Ord v =>
     Map v [(v,a)]    
     -> (a -> a -> a) -- ^ composition
     -> (a -> a)      -- ^ Kleene star
     -> a             -- ^ empty string
     -> Map (v,v) [a]
fromGraphToRegex ajMat compOp fixOp idOp 
    = Map.map (map fst) $ iterateOver (Map.keys ajMat) initMap 
      where
        vertices = snub $ concat [ [k,d] | (k,ls) <-Map.toList ajMat, (d,_) <- ls ]
        ajMat' 
            = Map.fromListWith (++) $ 
                zipWith (\(k,d,a) i -> (k,[(d,a,i)]) )
                    [ (k,d,a) | (k,ls) <- Map.toList ajMat, (d,a) <- ls] [1..]                            
        initMap = Map.fromListWith (++) $
                   [ ((src,dst),[(act,    [SimpleE i])]) | (src,ls) <- Map.toList ajMat', (dst,act,i) <- ls ]
                   ++ [ ((src,src),[(idOp,[])]) | src <- vertices ]
        iterateOver []     y = y
        iterateOver (x:xs) y = iterateOver xs (update x y) 
        update k distMap = -- trace ( render $ ppr distMap $$ ppr k ) $ 
            foldr f distMap [ (k1,k2) | k1 <- vertices, k2 <- vertices ]
            where
              f (k1,k2) m 
                | null l = m
                | otherwise =
                    Map.map g $ Map.insertWith (++) (k1,k2) l m   
                where
                  l = [ (a2 `compOp` (fixOp ak) `compOp` a1, p1 ++ [FixE pk] ++ p2) 
                        | (a1,p1) <- acts1, (a2,p2) <- acts2, (ak,pk) <- actsk ]
                  acts1 = lookupMono (k1,k) distMap
                  acts2 = lookupMono (k,k2) distMap
                  actsk = lookupMono (k,k)  distMap 
        g xs = map head $ groupBy ( (==) `on` snd) $ sortBy (compare `on` snd) xs
          


{-|
Check the grammar corresponding to TA is ambiguous or not.
-}

{-
If we have
a <- c1(a1,a2)
  <- d 
  <- c2(b1,b2,b3)
parsetrees with root "a" is amibiguous if and only if
- overlap (c1(a1,a2),d) or overlap (d,c2(b1,b2,b3)),
- or overlap (c1(a1,a2),c2(b1,b2,b3)),
- or ambiguous a1, or ambiguous a2, 
- or ambiguous d,
- or ambiguous b1, or ambiguous b2, ambiguous b3.

Pairs such that proved to overlapped/non-overlapped should be memoized 
for termination.

NB: We think the following grammar is ambiguous because we consider
epsilon transitions.
a <- a
  <- c(d,f)
d <- n
f <- n

Current implementation does not tell which state causes ambiguity.
-}
-- checkAmbiguity :: 
--    (Ord state, Ord name) => TA state name action -> state -> 
--     Maybe [((Symbol name, [state]), (Symbol name, [state]))]
checkAmbiguity (TA tMap) s = 
    evalState (checkAmb (Set.empty) s) (Set.empty,Set.empty)    
    where
      tr = Map.fromListWith (++)
            [ (dst tr, [(c,src tr)]) | (c,trs) <- Map.toList tMap, tr <- trs ]
      checkOL' t1 t2 = checkOverlap tr Set.empty Set.empty t1 t2  
      checkAmb env s = -- trace (show s) $ 
          case Map.lookup s tr of 
            Nothing -> return Nothing
            Just ls ->
                do { let vs = zip ls [0..]
                   ; let cand = [ (t1,t2) | (t1,i) <- vs, (t2,j) <- vs, i < j ]
                   ; rs <- mapM (\(t1,t2) -> checkOL' t1 t2) cand                             
                   ; if or rs then
                         return $ Just $ [ (t1,t2) | (b,(t1,t2)) <- zip rs cand, b ]
                     else
                         do { let ss = [ l | (_,ss) <- ls, l <- ss, not (Set.member l env)]
                            ; rs' <- mapM (checkAmb (Set.insert s env)) ss
                            ; return $ foldr mplus mzero rs'  }}


{-|
  Check overlap.

  The function dynamically constructs product machine and 
  does non-emptyness check.
-}
{-
  The function is axiomatized as follows.

   Γ,(a,b) |- overlap (a,c)  
  --------------------------- (b <-- c in Grammar)
      Γ |- overlap (a,b)

   Γ,(a,b) |- overlap (c,b)  
  --------------------------- (a <-- c in Grammar)
      Γ |- overlap (a,b)

    Γ,(a,t') |- overlap (t,t')
  ------------------------------(a <-- t in Grammar, t' is not state)
    Γ |- overlap (a,t') 

    Γ,(t,b) |- overlap (t,t')
  ------------------------------(b <-- t' in Grammar, t is not state)
    Γ |- overlap (t,b ) 
   
  
  ---------------------------
    Γ |- overlap (Top,_)

  ---------------------------
    Γ |- overlap (_,Top)

  --------------------------- 
    Γ,(a,b) |- ¬ overlap (a,b)  
  

  --------------------------------------- (c1 /= c2)
   Γ |- ¬ overlap (c1(a1,a2),c2(b1,b2,b3)) 
 
      Γ |- overlap (a1,b1) 
      Γ |- overlap (a2,b2)
  ----------------------------------
   Γ |- overlap (c(a1,a2),c(b1,b2))       
-}

checkOverlap ::
      (Ord name, Ord state) =>
      Map state [(Symbol name, [state])] 
      -> Set (state, state)
      -> Set (state, (Symbol name, [state]))
      -> (Symbol name, [state])
      -> (Symbol name, [state])
      -> State (Set (state,state), Set (state,state)) Bool
checkOverlap tr env env' (EpsS,[s1]) (EpsS,[s2]) 
    | Set.member (s1,s2) env || Set.member (s2,s1) env 
        = return False
    | otherwise 
        = do { (ol,nol) <- get
             ; if Set.member (s1,s2) ol || Set.member (s2,s1) ol then
                   return True
               else if Set.member (s1,s2) nol || Set.member (s2,s1) nol then
                   return False
               else 
                   case Map.lookup s1 tr of
                     Nothing ->
                         return False
                     Just ls -> 
                         do { rs <- mapM (\t1 -> checkOverlap tr (Set.insert (s1,s2) env) env' t1 (EpsS,[s2])) ls 
                            ; if all not rs then
                                  if Set.null env then
                                      do { (ol, nol) <- get
                                         ; put (ol, Set.insert (s1,s2) nol)
                                         ; return False  }
                                  else
                                      return False
                              else
                                  do { (ol,nol) <- get
                                     ; put ( Set.insert (s1,s2) ol, nol)
                                     ; return True } }}
checkOverlap tr env env' _ (TopS,_) =
    return True

checkOverlap tr env env' (EpsS,[s1]) t2 
    | Set.member (s1,t2) env' = return False
    | otherwise = case Map.lookup s1 tr of
        Nothing ->
            return False
        Just ls -> 
            do { rs <- mapM (\t1 -> checkOverlap tr env (Set.insert (s1,t2) env') t1 t2) ls 
               ; if all not rs then
                     return False
                 else
                     return True }    
checkOverlap tr env env' (ConS c1,as1) (ConS c2,as2) 
    | c1 == c2 && length as1 == length as2 
        = -- trace (show env ++ " |-? " ++ show (c1,as1) ++ show (c2,as2) ) $
          let andSearch [] = return True
              andSearch ((t1,t2):xs) =
                  do r <- checkOverlap tr env env' (EpsS,[t1]) (EpsS,[t2])
                     if r then (andSearch xs) else (return False)
          in andSearch $ zip as1 as2 
          -- do { rs <- mapM (\(t1,t2) -> 
          --                      checkOverlap tr env  $ zip as1 as2
          --    ; if and rs then
          --          return True
          --      else
          --          return False }
    | otherwise 
        = return False
checkOverlap tr env env' t1 t2 
    = -- trace (show env ++ " |-? " ++ show t1 ++ show t2 ) $
      checkOverlap tr env env' t2 t1

--
-- * Pretty Printing
--

instance Ppr name => Ppr (Symbol name) where
    ppr (ConS name) = ppr name
    ppr (TopS)      = ptext "__"
    ppr (EpsS)      = empty
  
instance Show name => Show (Symbol name) where
    show (ConS name) = show name 
    show (TopS)      = "__"
    show (EpsS)      = ""

instance (Show state, Show name, Show action) 
         => Show (TA state name action)
    where
      show = showTA 0

instance (Show state, Show action) => Show (Tr state action) where
      show tr
          = (show $ dst tr) ++  
            " <-- " ++ "??("++ (show $ src tr) ++ ")"  ++ " " ++
            "{" ++ show (act tr) ++ "}" 

instance (Ppr state, Ppr action) => Ppr (Tr state action) where
    ppr tr 
        = (ppr $ dst tr) <+>
          ptext "<--" <+> parens (hsep (punctuate comma $ map ppr (src tr)))
          <+> braces (ppr (act tr))

showTA :: (Show action, Show t, Show state) =>
                Int -> TA state t action -> String
showTA indent (TA tMap) 
    =  renderTable . 
           map (replicate indent ' ':) .
                concatMap (\(c,trs) ->showTRs c trs) . Map.toList $ tMap
    where
      showTRs c trs
          =  map (\tr -> [ show $ dst tr, 
                            " <-- ",
                            showRHS c tr, " ", 
                            "{" ++ show (act tr) ++ "}" ]) trs

      showRHS (ConS name) (Tr src _ _) 
          | null src  = show name
          | otherwise = show name ++ "(" ++
                        intercalate "," (map show src)
                        ++ ")"
      showRHS (EpsS) (Tr [s] _ _) 
          = show s
      showRHS topS _ = show topS

instance (Ppr state, Ppr name, Ppr action) => 
         (Ppr (TA state name action)) where  
   ppr (TA tMap) 
       = vcat (map (\(c,trs) -> pprTRs c trs) (Map.toList tMap))
         where
           pprTRs c trs
               = vcat (map 
                       (\tr ->
                            ppr (dst tr) $$
                            nest 4 (ptext "<--" <+> pprRHS c tr) $$
--                            nest 4 (braces (ptext "..."))
                            nest 4 (braces (space <> ppr (act tr) <> space))
                       ) trs)
           pprRHS (ConS name) tr 
               | null (src tr) 
                   = ppr name
               | otherwise  
                   = ppr name <> 
                     parens (hsep $ punctuate comma $ map ppr (src tr))
           pprRHS (EpsS) (Tr [s] _ _) = ppr s
           pprRHS topS _ = ppr topS

--
-- Debugging and Testing
--

-- instance Action ([[Char]]) where
--     compA as bs = map (\[x,y] -> x ++ " . " ++y) $ combination [as,bs]
--     parA  = (++)
--     tupleA [] = [[]]
--     tupleA as = map (\x -> "<"++x++">") $ 
--                    foldr1 (zipWith (\x y -> x ++ ",  " ++ y)) as
--     takeA ls = 
--         ["\\(" ++ 
--          intercalate "," 
--          (zipWith (\(i,n) x -> "(" ++ intercalate "," (map (\i -> x++show i) [0..(n-1)]) ++ ")") ls xs) ++
--          ") --> " ++ "(" ++ intercalate "," (zipWith (\i x -> x++(show $ fst i)) ls xs)++")"]
--         where
--           xs = ["x" ++ show i | i <- [0..] ]
               

-- testTA = 
--     TA $ Map.fromListWith (++)
--            [(EpsS, [ Tr [2] 1 ["a2"], Tr [3] 2 ["a1"] ]),
--             (ConS "c", [ Tr [1,2] 3 ["a3"] ]),
--             (ConS "n", [ Tr [] 2 ["a4"] ])]

-- testTA' = 
--     TA $ Map.fromListWith (++)
--            [(EpsS, [ Tr [2] 1 ["a2"], Tr [3] 2 ["a1"] ]),
--             (ConS "c", [ Tr [1,2] 3 ["a3"] ]),
--             (ConS "n", [ Tr [] 2 ["a4"] ]),
--             (ConS "n", [ Tr [] 3 ["a4"] ]) ]



