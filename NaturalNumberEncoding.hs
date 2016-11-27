
-- | NaturalNumberEnconding

{-# LANGUAGE UnicodeSyntax #-}

module NaturalNumberEncoding 
  where

import Numeric.Natural ( Natural )
import Data.List(union, (\\))
import Test.QuickCheck ( (==>), Property, quickCheck )

type Sym = String

data Expr = Var Sym
          | App Expr Expr
          | Lam Sym Expr
          deriving (Eq, Read)

instance Show Expr where
  show (Var x)    = x  
  show (App m n)  = "(" ++ show m ++ " " ++ show n ++ ")"  
  show (Lam x m)  = "λ" ++ x ++ "." ++ show m  

data Type = Base | Arrow Type Type
    deriving (Eq, Read, Show)

whnf ∷ Expr → Expr
whnf ee = spine ee []
  where 
    spine ∷ Expr → [Expr] → Expr
    spine (App f a) as = spine f (a:as)
    spine (Lam x e) (a:as) = spine (subst x a e) as
    spine f as = foldl App f as

nf ∷ Expr → Expr
nf ee = spine ee []
  where 
    spine ∷ Expr → [Expr] → Expr
    spine (App f a) as = spine f (a:as)
    spine (Lam x e) [] = Lam x (nf e)
    spine (Lam x e) (a:as) = spine (subst x a e) as
    spine f as  = app f as

    app ∷ Expr → [Expr] → Expr
    app f as    = foldl App f (map nf as)

betaEq ∷ Expr → Expr → Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)        

freeVars ∷ Expr → [Sym]
freeVars (Var x)    = [x]
freeVars (App f a)  = freeVars f `union` freeVars a
freeVars (Lam i e)  = freeVars e \\ [i]

subst ∷ Sym → Expr → Expr → Expr
subst v x = sub  -- subst v x b = sub b
  where
    sub ∷ Expr → Expr
    sub e@(Var i) = if i == v then x else e
    sub (App f a) = App (sub f) (sub a)
    sub (Lam i e) =
      if v == i then
        Lam i e
      else if i `elem` fvx then
        let i' ∷ Sym
            i' = cloneSym e i

            e' ∷ Expr
            e' = substVar i i' e
        in  Lam i' (sub e')
      else
        Lam i (sub e)

    fvx ∷ [Sym]
    fvx = freeVars x

    cloneSym ∷ Expr → Sym → Sym
    cloneSym e i = loop i
      where
        loop ∷ Sym → Sym
        loop i' = if i' `elem` vars then loop (i ++ "'") else i'
        
        vars ∷ [Sym]
        vars = fvx ++ freeVars e

substVar ∷ Sym → Sym → Expr → Expr
substVar x s' = subst x (Var s')

alphaEq ∷ Expr → Expr → Bool
alphaEq (Var v)   (Var v')    = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (substVar s' s e')
alphaEq _ _ = False

app2 ∷ Expr → Expr → Expr → Expr
app2 f x = App $ App f x

app3 ∷ Expr → Expr → Expr → Expr → Expr 
app3 f x y = App $ App (App f x) y

true ∷ Expr
true = Lam "x" (Lam "y" (Var "x"))

false ∷ Expr
false = Lam "x" (Lam "y" (Var "y"))

iff ∷ Expr
iff = Lam "p" $ Lam "x" $ Lam "y" $ app2 (Var "p") (Var "x") (Var "y")

pair ∷ Expr
pair = Lam "x" (Lam "y" (Lam "f" (app2 (Var "f") (Var "x") (Var "y"))))

zero ∷ Expr
zero = Lam "x" $ Var "x"

succ' ∷ Expr
succ' = Lam "x" $ Lam "z" (app2 (Var "z") false (Var "x"))

pred' ∷ Expr
pred' = Lam "x" $ App (Var "x") false

isZero ∷ Expr
isZero = Lam "x" $ App (Var "x") true

pairing :: Expr
pairing = Lam "M" $ Lam "N" $ Lam "z" $ App (App (Var "z") (Var "M")) (Var "N")

eN ∷ Natural → Expr
eN 0 = zero
eN n = app2 pairing false (eN (n-1))

y = Lam "f" $ App (Lam "x" (App (Var "f") (App (Var "x") (Var "x")))) (Lam "x" (App (Var "f") (App (Var "x") (Var "x"))))

eAdd = App y (Lam "a" $ Lam "x" $ Lam "y" (app3 iff (App isZero (Var "x")) (Var "y") resto))
  where
      resto ∷ Expr
      resto = App succ' (App (App (Var "a") (App pred' (Var "x"))) (Var "y"))

eMult ∷ Expr
eMult = App y (Lam "a" $ Lam "n" $ Lam "m" (app3 iff (App isZero (Var "n")) zero (app3 iff (App isZero (Var "m")) zero resto)))
  where
    resto :: Expr
    resto = addW (App (App (Var "a") (App pred' (Var "n"))) (Var "m")) (Var "m")

predW ∷ Expr → Expr
predW = App pred'

addW ∷ Expr → Expr → Expr
addW = app2 eAdd

multW ∷ Expr → Expr → Expr
multW = app2 eMult

propPred ∷ Natural → Property
propPred n = n > 0 ==> betaEq (predW $ eN n) (eN $ n - 1)

propAdd ∷ Natural → Natural → Bool
propAdd m n = betaEq (addW (eN m) (eN n)) (eN $ m + n)

propMult ∷ Natural → Natural → Bool
propMult m n = betaEq (multW (eN m) (eN n)) (eN $ m * n)

tests ∷ IO ()
tests = do
  quickCheck propPred
  quickCheck propAdd
  quickCheck propMult

uno     = nf $ App succ' zero
dos     = nf $ App succ' uno
tres    = nf $ App succ' dos
cuatro  = nf $ App succ' tres

tZero     = betaEq zero (eN 0)
tUno      = betaEq uno (eN 1)
tDos      = betaEq dos (eN 2)
tTres     = betaEq tres (eN 3)
tCuatro   = betaEq cuatro (eN 4)

mytests = [tZero ,tUno ,tDos ,tTres ,tCuatro]

main ∷ IO ()
main = print 1
