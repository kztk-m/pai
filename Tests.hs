module Tests where

import AST
import CST (parseString)

import TA
import GTA

import CodeGen (fromProgramToGTA)
import Util (ppr)

import Text.PrettyPrint 


consE a b = conE "Cons" [a,b]
nilE      = conE "Nil"  []
consP a b = conP "Cons" [a,b]
nilP      = conP "Nil"  []

testId = 
    prog $ 
      [ decl "idList" [ conP "Nil" [] ] (conE "Nil" []),
        decl "idList" [ conP "Cons" [varP "a", varP "x"] ]
                      ( conE "Cons" [varE "a",
                                    funE "idList" [varE "x"]]) ]

testSnoc =
    prog $
      [ decl "snoc" [ nilP, varP "b" ] (consE (varE "b") nilE),
        decl "snoc" [ consP (varP "a") (varP "x"), varP "b"]
             (consE (varE "a") (funE "snoc" [varE "x", varE "b"])) ]

testAcc =
    prog $ 
      [ decl "f" [ nilP, varP "y" ]
             (consE end (varE "y")),
        decl "f" [ consP (varP "a") (varP "x"), varP "y"]
             (consE (l (varE "a"))
                   (funE "f" [varE "x", (consE (r (varE "a")) (varE "y")) ]))]
          where
            l x = conE "L" [x]
            r x = conE "R" [x]
            end = conE "End" []
             
testAppend =
    prog $ 
         [ decl "app" [ nilP, varP "y" ] (varE "y"),
           decl "app" [ consP (varP "a") (varP "x"), varP "y"]
                (consE (varE "a") (funE "app" [varE "x", varE "y"])) ]
                
testAdd =
    prog $ 
         [ decl "add" [ conP "Z" [], varP "y" ] (varE "y"),
           decl "add" [ conP "S" [varP "x"], varP "y"]
                (conE "S" [funE "add" [varE "x", varE "y"]]) ]

-- Currenlty, accoding to handling of dead state this function does not work.
--  - "traverse" function must consider the "dead state" case.
--  - since enough constraint is not avaiable for dead state, 
--    Haskell's type check fails.
testReverse = 
    case (parseString $
             "reverse(x) = rev(x,Nil)\n"
          ++ "rev(Nil,y) = y\n"
          ++ "rev(Cons(a,x),y) = rev(x,Cons(a,y))") of 
      Right x -> fst $ fromCSTtoAST x 
      Left  x -> error $ show x 

testSimpleRec =
    case (parseString $
             "f(Z)    = Z\n"
          ++ "f(S(x)) = f(x)") of 
      Right x -> fst $ fromCSTtoAST x 
      Left  x -> error $ show x 

test :: Prog -> IO () 
test = putStrLn . render . ppr . fromProgramToGTA 
