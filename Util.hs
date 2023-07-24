{-# LANGUAGE CPP #-}
module Util where

import Text.PrettyPrint 
import Data.List (group, sort, head,intercalate)
import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Maybe (fromJust)

#if MIN_VERSION_base(4,9,0)
import           Prelude          hiding ((<>))
#endif


class Ppr p where
    ppr :: p -> Doc

instance Ppr Bool where
    ppr = ptext . show 
instance Ppr Int where
    ppr = ptext . show 

instance Ppr a => Ppr [a] where
    ppr s = brackets (sep $ punctuate comma $ map ppr s)

instance (Ppr a,Ppr b) => Ppr (a,b) where
    ppr (a,b) = parens (ppr a <> comma <> ppr b)

instance (Ppr a,Ppr b,Ppr c) => Ppr (a,b,c) where
    ppr (a,b,c) = parens (ppr a <> comma <> ppr b <> comma <> ppr c)


instance Ppr a => Ppr (Maybe a) where
    ppr Nothing  = ptext "Nothing"
    ppr (Just s) = ptext "Just" <+> ppr s 

instance (Ppr s,Ord s) => Ppr (Set s) where
    ppr s =
        let elems = Set.elems s 
        in braces ( sep $ punctuate comma $ map ppr elems )
instance (Ppr k, Ppr v, Ord k) => Ppr (Map k v) where 
    ppr m =     
        let ks = Map.keys m 
        in braces ( vcat $ 
                   map (\k ->
                            ppr k <> colon $$
                            nest 8 (ppr $ fromJust $ Map.lookup k m) 
                       ) ks
                  )

fromJust' (Just x) = x

renderTable :: [ [String] ] -> String
renderTable lists = 
    intercalate "\n" $
      map truncSp $ map concat $ map (zipWith (\m s -> fill m s) maxes) lists
    where
      truncSp xs = reverse (f (reverse xs))
          where 
            f (' ':x)  = f x
            f x        = x
      fill l s = take l (s ++ cycle " ")
      maxes = foldr (zipWith max) (cycle [0]) (map (map length) lists)

{-# SPECIALIZE snub :: [Int] -> [Int] #-}
{-# SPECIALIZE snub :: [String] -> [String] #-}
snub :: Ord a => [a] -> [a]
snub = map head . group .  sort  
