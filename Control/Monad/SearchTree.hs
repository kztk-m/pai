{-# LANGUAGE CPP        #-}
{-# LANGUAGE Rank2Types #-}
-- |
-- Module      : Control.Monad.SearchTree
-- Copyright   : Sebastian Fischer
-- License     : BSD3
--
-- Maintainer  : Sebastian Fischer (sebf@informatik.uni-kiel.de)
-- Stability   : experimental
-- Portability : portable
--
-- This Haskell library provides an implementation of the MonadPlus
-- type class that represents the search space as a tree whose
-- constructors represent mzero, return, and mplus.
--
-- Such a tree can be used to implement different search strategies,
-- e.g., by using a queue. It can also be used as a basis for parallel
-- search strategies that evaluate different parts of the search space
-- concurrently.

-- Kazutaka Matsuda: 
--   2023-07-24 Make it compatible with GHC 9.2.X (haven't checked 9.4/9.6).

module Control.Monad.SearchTree ( SearchTree(..), Search, searchTree ) where

import           Control.Applicative
import           Control.Monad

#if MIN_VERSION_base(4,9,0)
import           Control.Monad.Fail
#endif

-- |
-- The type @SearchTree a@ represents non-deterministic computations
-- as a tree structure.
data SearchTree a = None | One a | Choice (SearchTree a) (SearchTree a)
 deriving Show

instance Functor SearchTree where
  fmap _ None         = None
  fmap f (One x)      = One (f x)
  fmap f (Choice s t) = Choice (fmap f s) (fmap f t)

instance Applicative SearchTree where
  pure  = One
  (<*>) = ap

instance Alternative SearchTree where
  empty = mzero
  (<|>) = mplus

instance Monad SearchTree where
  return = pure

  None       >>= _ = None
  One x      >>= f = f x
  Choice s t >>= f = Choice (s >>= f) (t >>= f)

#if MIN_VERSION_base(4,9,0)
instance MonadFail SearchTree where
  fail _ = None
#else
  fail _ = None
#endif

instance MonadPlus SearchTree where
  mzero = None
  mplus = Choice

-- |
-- Another search monad based on continuations that produce search
-- trees.
newtype Search a = Search {

  -- | Passes a continuation to a monadic search action.
  search :: forall r . (a -> SearchTree r) -> SearchTree r

 }

-- | Computes the @SearchTree@ representation of a @Search@ action.
searchTree :: Search a -> SearchTree a
searchTree a = search a One

instance Functor Search where
  fmap f a = Search (\k -> search a (k . f))

instance Applicative Search where
  pure x = Search ($ x)
  (<*>)  = ap

instance Alternative Search where
  empty = mzero
  (<|>) = mplus

instance Monad Search where
  return  = pure
  a >>= f = Search (\k -> search a (\x -> search (f x) k))

#if MIN_VERSION_base(4,9,0)
instance MonadFail Search where
  fail _ = mzero
#else
  fail _ = mzero
#endif


instance MonadPlus Search where
  mzero       = Search (const mzero)
  a `mplus` b = Search (\k -> search a k `mplus` search b k)