
-- | NatEncoding module

{-# LANGUAGE UnicodeSyntax #-}

{-|
Module      : NatEncoding
Description : alternative encoding for the natural numbers
Copyright   : (c) Camilo Rodriguez and Jonathan Prieto-Cubide, 2016
License     : GPL-3
Maintainer  : Camilo Rodriguez and Jonathan Prieto-Cubide
Stability   : stable
Portability : POSIX

NatEnconding is a Haskell program intends to provide an alternative
enconding for the natural numbers.
-}
module NatEncoding
  where


import           Data.List       (union, (\\))
import           Numeric.Natural (Natural)
import           Test.QuickCheck (Property, quickCheck, (==>))

-- @Adapted from Lennart Augustsson's blog <https://goo.gl/3p6R0P>
type Sym = String

data Expr 
  -- | The 'Var Sym' represents the normal form in ´v`|variable´'` 
  = Var Sym
  -- | The 'App Expr Expr' represents the normal form in ´(` λ-term λ-term ´)`
  | App Expr Expr
  -- | The 'Lam Sym Expr' represents the normal form in ´(λ` variable λ-term ´)`
  | Lam Sym Expr
  deriving (Eq, Read)

instance Show Expr where
  show (Var x)   = x
  show (App m n) = show m ++ " " ++ show n
  show (Lam x m) = "λ" ++ x ++ "." ++ show m

-- |The 'nf' function finds the normal form of a λ-term.
nf ∷ Expr → Expr
nf ee = spine ee []
  where
    spine ∷ Expr → [Expr] → Expr
    spine (App f a) as     = spine f (a:as)
    spine (Lam x e) []     = Lam x (nf e)
    spine (Lam x e) (a:as) = spine (subst x a e) as
    spine f as             = app f as

    app ∷ Expr → [Expr] → Expr
    app f as    = foldl App f (map nf as)

-- |The 'betaEq' function will return if a couple λ-term are equal.
betaEq ∷ Expr → Expr → Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

-- |The 'freeVars' function finds the free var.
freeVars ∷ Expr → [Sym]
freeVars (Var x)   = [x]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i e) = freeVars e \\ [i]

-- |The 'subst' function will replace all free occurrences of v by b inside x.
subst ∷ Sym → Expr → Expr → Expr
subst v x = sub  -- subst v x b = sub b
  where
    sub ∷ Expr → Expr
    sub e@(Var i)     = if i == v then x else e
    sub (App f a)     = App (sub f) (sub a)
    sub (Lam i e)
      | v == i        =  Lam i e
      | i `elem` fvx  =
        let i' ∷ Sym
            i' = cloneSym e i

            e' ∷ Expr
            e' = substVar i i' e
        in  Lam i' (sub e')
      | otherwise     =  Lam i $ sub e

    fvx ∷ [Sym]
    fvx = freeVars x

    cloneSym ∷ Expr → Sym → Sym
    cloneSym e i = loop i
      where
        loop ∷ Sym → Sym
        loop i' = if i' `elem` vars then loop (i ++ "'") else i'

        vars ∷ [Sym]
        vars = fvx ++ freeVars e

-- |The 'substVar' function is a utility for replace one variable with another.
substVar ∷ Sym → Sym → Expr → Expr
substVar x s' = subst x (Var s')

-- |The 'alphaEq' function is for compare couple λ-term are equal.
alphaEq ∷ Expr → Expr → Bool
alphaEq (Var v)   (Var v')    = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (substVar s' s e')
alphaEq _ _                   = False

-- |The 'app2' function is for realize two applications in one λ-term.
app2 ∷ Expr → Expr → Expr → Expr
app2 f x = App $ App f x

-- |The 'app3' function is for realize three applications in one λ-term.
app3 ∷ Expr → Expr → Expr → Expr → Expr
app3 f x y = App $ App (App f x) y

-- |The 'x¹, y¹, f¹' function that returns one variable.
x¹, y¹, f¹ ∷ Expr
x¹ = Var "x"
y¹ = Var "y"
f¹ = Var "f"

-- |The 'true' function that implements the combinator K.
true ∷ Expr
true = Lam "x" $ Lam "y" x¹

-- |The 'false' function that implements the combinator K*.  
false ∷ Expr
false = Lam "x" $ Lam "y" y¹

-- |The 'false' function that implements the combinator if.
iff ∷ Expr
iff = Lam "f" $ Lam "x" $ Lam "y" $ app2 f¹ x¹ y¹

-- |The 'testIf' function applies iff.
testIf ∷ Expr → Expr → Expr → Expr
testIf = app3 iff

-- |The 'pair' function that implements the combinator pair.
pair ∷ Expr
pair = Lam "x" $ Lam "y" $ Lam "f" $ app2 f¹ x¹ y¹

-- |The 'zero' function that implements the combinator I.
zero ∷ Expr
zero = Lam "x" $ Var "x"

-- |The 'isZero' function that implements the combinator Zero.
isZero ∷ Expr
isZero = Lam "x" $ App x¹ true

-- |The 'testIf' function is for apply the combinator Zero.
tZero ∷ Expr → Expr
tZero = App isZero

-- |The 'succ'' function that implements the combinator S+.
succ' ∷ Expr
succ' = Lam "x" $ Lam "y" $ app2 y¹ false x¹

-- |The 'pred'' function that implements the combinator P-.
pred' ∷ Expr
pred' = Lam "x" $ App x¹ false

-- |The 'yComb' function that implements the combinator Y.
yComb ∷ Expr
yComb = Lam "f" $ App (Lam "x" fxx) (Lam "x" fxx)
  where
    fxx ∷ Expr
    fxx = App f¹ $ App x¹ x¹

-- |The 'applyY' function is for apply the combinator Y.
applyY ∷ Expr → Expr
applyY = App yComb

-- |The 'n¹, m¹, a¹' function that returns one variable.
n¹, m¹, a¹ ∷ Expr
n¹ = Var "n"
m¹ = Var "m"
a¹ = Var "a"

-- |The 'eN' function returns the λ-term associated with the natural number n
eN ∷ Natural → Expr
eN 0  = zero
eN nn = app2 pair false $ eN (nn-1)

-- |The 'eAdd' function addition
eAdd ∷ Expr
eAdd = applyY $ Lam "a" $ Lam "n" $ Lam "m" $
  testIf (tZero n¹) m¹ suma
    where
      -- n+m = succ((n-1) + m)
      suma ∷ Expr
      suma = App succ' $ app2 a¹ (predW n¹) m¹

-- |The 'eMult' function multiplication
eMult ∷ Expr
eMult = applyY $ Lam "a" $ Lam "n" $ Lam "m" $
  testIf (tZero n¹) zero $ testIf (tZero m¹) zero multi
    where
      -- multi = ((n-1) * m) + m
      multi ∷ Expr
      multi = addW (app2 a¹ (predW n¹) m¹) m¹

-- |The 'predW' function is for apply predecessor
predW ∷ Expr → Expr
predW = App pred'

-- |The 'predW' function is for apply addition
addW ∷ Expr → Expr → Expr
addW = app2 eAdd

-- |The 'predW' function is for apply multiplication
multW ∷ Expr → Expr → Expr
multW = app2 eMult

-- |The 'propPred' function test of predecessor
propPred ∷ Natural → Property
propPred n = n > 0 ==> betaEq (predW $ eN n) (eN $ n - 1)

-- |The 'propAdd' function test of addition
propAdd ∷ Natural → Natural → Bool
propAdd m n = betaEq (addW (eN m) (eN n)) (eN $ m + n)

-- |The 'propMult' function test of multiplication
propMult ∷ Natural → Natural → Bool
propMult m n = betaEq (multW (eN m) (eN n)) (eN $ m * n)

-- |The 'tests' is the function execute tests to valid operations of NatEncoding
tests ∷ IO ()
tests = do
  quickCheck propPred
  quickCheck propAdd
  quickCheck propMult

main ∷ IO ()
main = tests
