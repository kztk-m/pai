 `PaI`: A System for Grammar-based Program Inversion
=======================================================


What is this?
-------------

This is an implementation of the paper 
"Grammar-based Approach to Invertible Programs" 
written by Kazutaka Matsuda et al.

The program takes a input program written in a
original programming language, and produces a Haskell code of its inverse.





~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ {.shell}
$ cat examples/snoc.txt
snoc(Nil,y)       = Cons(y,Nil)
snoc(Cons(a,x),y) = Cons(a,snoc(x,y)) 

$ ./pai examples/snoc.txt -i MyData > test.hs
$ ghci test.hs
...
Ok, module loaded: MyData, InvSnoc, InvUtil.
*Invsnoc> :t snoc 
snoc :: List x -> x -> List x 
*Invsnoc> :t inv_Fsnoc 
inv_Fsnoc :: List t -> (List t, t)
*Invsnoc> snoc (Cons 1 (Cons 2 Nil)) 3
Cons 1 (Cons 2 (Cons 3 Nil))
*Invsnoc> inv_Fsnoc (Cons 1 (Cons 2 (Cons 3 Nil)))
(Cons 1 (Cons 2 Nil),3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


For non-injective fucntion, 
the system can generate a right inverse that enumerates 
possible corresponding inputs.


~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.shell}
$ cat examples/add.txt
-- Noninjective program but linear & treeless
-- Hence, the correct right inverse is obtained.
add(Z,y) = y
add(S(x),y) = S(add(x,y))
$ ./pai examples/add.txt -i MyData > test.hs
--- Ambiguity Info ------------------------------
System failed to prove the injectivity because of following reasons: 
Possibly range-overlapping expressions: 
    at (3,12) -- (4,1)
        y
    at (4,15) -- (5,1)
        S(add{9}(x{10},y{11}))
$ ghci test.hs
...
Ok, modules loaded: MyData, Invadd, InvUtil.
*Invadd> :t add
add :: Nat -> Nat -> Nat
*Invadd> :t inv_Fadd
inv_Fadd :: Nat -> [(Nat,Nat)]
*Invadd> add (S Z) (S (S Z))
S (S (S Z))
*Invadd> inv_Fadd (S (S (S Z)))
[(Z,S (S (S Z))),(S Z,S (S Z)),(S (S Z),S Z),(S (S (S Z)),Z)]
*Invadd> map (uncurry add) $ inv_Fadd (S (S (S Z)))
[S (S (S Z)),S (S (S Z)),S (S (S Z)),S (S (S Z))]
*Invadd> :m +Data.List
*Invadd Data.List> nub $ map (uncurry add) $ inv_Fadd (S (S (S Z)))
[S (S (S Z))]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


 How to build
--------------
   0. Install [GHC] over 6.8.2.
   1. Download tar file: [pai.tar.gz](./pai.tar.gz)
   2. Unpack the tar file: `tar zxvf pai.tar.gz`
   3. `make`
     - In case of trouble, please edit make file to fix the problem.
     - `pai` (or, `pai.exe` in Windows) is the name of the program inverter
     - Directory `examples` contains some examples.
     - `MyData.hs` contains data declarations for the examples.
     - `InvUtil.hs` contains function defintions used in the generated inverses.

[GHC]: http://www.haskell.org/ghc/    

 Options of `pai`
------------------

`-i MODULE_NAME`
:    It inserts "import MODULE_NAME" to a generated inverse program.

`-f INPUT_FILE`
:    It specifies input file.

`-m MODULE_NAME`
:    It specifies the module name of a generated inverse program.

`-d`
:    It turns on debugMode flag.

`-h`
:    Not implemented. (Show help)

`-t`
:    With this flag, `pai` shows elapsed time of code generation.


 Syntax of Input Program
-----------------------------

    <Prog> ::= <Decl> ... <Decl>
    
    <Decl> ::= FunName(<Pat>,...,<Pat>) = <Exp>
    <Pat>  ::= ConName(<Pat>,...,<Pat>)
            |  VarName 
    <Exp>  ::= FunName(<Exp>,...,<Exp>)
            |  ConName(<Exp>,...,<Exp>)
            |  VarName 
            |  let <Pat> = <Exp> in <Exp>
    
    FunName = [a-z] [a-zA-Z0-9_]*
    VarName = [a-z] [a-zA-Z0-9_]*
    ConName = [A-Z] [a-zA-Z0-9_]*


 Limitations & Known Issues
-----------------------------

  * The derived code may not accept a value in the range of 
    original function if the ambiguity test does not succeed.



