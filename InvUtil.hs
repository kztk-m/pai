module InvUtil 
    (
     (>=>), I(..), 
     checkEq, checkEqPrim, fixApp, Default, something, mymplus, mymzero
    ) where 

-- import Control.Monad ()
import Control.Monad ( (>=>), liftM, liftM2, liftM3, mplus, mzero )                     
               
class Default a where
    something :: a 

instance Default Int        where { something = 0 }
instance Default Integer    where { something = 0 }
instance Default Float      where { something = 0 }
instance Default Double     where { something = 0 }
instance Default [a]        where { something = [] }
instance Default (Maybe a)  where { something = Nothing }
instance (Default a, Default b) => Default (a,b) where
    something = (something, something)
instance (Default a, Default b, Default c) => Default (a,b,c) where
    something = (something, something, something)

instance Default a => Default (Either a b) where
    something = Left something


newtype I x = I { runI :: x }
    deriving (Show)

instance Functor I where
  {-# INLINE [1] fmap #-}
  fmap f (I x) = I (f x)

instance Applicative I where
  {-# INLINE [1] pure #-}
  pure = I

  {-# INLINE [1] (<*>) #-}
  I f <*> I x = I (f x)

instance Monad I where 
    {-# INLINE [1] return #-}
    return        = I
    {-# INLINE [1] (>>=) #-}
    (>>=) (I x) f = f x
    {-# INLINE [1] fail #-}
    fail x = error x

{-# INLINABLE checkEq #-}
{-# SPECIALIZE INLINE [2] checkEq :: Eq a => I a -> I a -> I a #-}
checkEq :: (Monad m,Eq a) => m a -> m a -> m a 
checkEq x y =
    do { a <- x 
       ; b <- y 
       ; checkEqPrim a b }

{-# INLINABLE  checkEqPrim #-}
{-# SPECIALIZE INLINE [2] checkEqPrim :: Eq a => a -> a -> I a #-}
checkEqPrim a b | a == b = return a 
                | True   = fail $ "Incosistency Found"
                
fixApp a y = 
    let f x y = x y `mplus` f (a >=> x) y
    in f return y

-- Currently, these functions are less polymorphic 
-- because typing issue.
mymplus :: [a] -> [a] -> [a]
mymplus = mplus 

mymzero :: [a]
mymzero = mzero

-- zeroPossibility = []
-- addPossibility [] ys = ys
-- addPossibility (x:xs) ys = x:addPossibility ys xs

{-# RULES
"checkEqPrim"[3] forall x y. checkEq (return x) (return y) = checkEqPrim x y
  #-}

{-# RULES
"return2"  forall f x y. return (x,y) >>= (\(a,b) -> f a b) = f x y 
  #-}

{-# RULES
"SimplifyLiftM2"[3]   forall f x. liftM f (return x) = return (f x)
"SimplifyLiftM2"[3]   forall f x y. liftM2 f (return x) (return y) = return (f x y)
"SimplifyLiftM3"[3]   forall f x y z. liftM3 f (return x) (return y) (return z) = return (f x y z)
"SimplifyReturn0"[3]  forall x. return () >>= (\() -> x) = x
"SimplifyReturn1'"[3] forall x. return x >>= (\y -> return y) = return x
  #-}
