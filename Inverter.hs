module Inverter where

import Syntax.Concrete
import Syntax.Abstract

import TreeAutomata.Automata
import TreeAutomata.Guided

import Inverter.Action
import Inverter.Build 
import Inverter.CodeGen

import Data.Maybe (isJust)
import Data.Map (Map)
import Data.List (nub)

import Util
import qualified Language.Haskell.TH as TH

import Text.PrettyPrint 

type AmbiguityInfo = Maybe ([(Name, Name)], [(ID, ID)])

invert ::
  CProg
  -> (Prog,
      Map ID (SrcSpan, Doc),
      TA AState Name Act,
      Map AState (GTA Int Int Name Act),
      AmbiguityInfo,
      [TH.Dec])
invert cprog =
  let (prog, imap)       = fromCSTtoAST cprog
      (ta, entry, other) = fromProgramToTA prog
      ambiguity          = 
          fmap snub $ foldr merge Nothing 
                    $ map (checkAmbiguity ta) (entry : other)
              where merge Nothing x = x
                    merge x Nothing = x 
                    merge (Just a) (Just b) = Just (a++b)
      gtaMap             = fromTAtoDGTA ta (entry : other) 
      code               = genCode (gtaMap, entry, isJust ambiguity)
  in (prog,
      imap, 
      ta, 
      gtaMap,
      ambiguityInfo ambiguity,
      code)

ambiguityInfo ::
  Maybe [((Symbol name1, [AState]), (Symbol name2, [AState]))]
  -> AmbiguityInfo
ambiguityInfo Nothing = Nothing
ambiguityInfo (Just collisions) = 
    let epss = [ (s1,s2)| ((EpsS,[s1]), (EpsS,[s2])) <- collisions ]
    in Just ([(n1, n2) | (FromF n1, FromF n2) <- filter funOverlap epss],
             [(i1, i2) | (FromE i1, FromE i2) <- filter exprOverlap epss])
  where funOverlap (FromF _, FromF _) = True
        funOverlap _ = False

        exprOverlap (FromE _, FromE _) = True
        exprOverlap _ = False