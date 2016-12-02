

{-|
Module      : NatEncoding
Description : alternative encoding for the natural numbers
Copyright   : (c) Camilo Rodríguez and Jonathan Prieto-Cubides, 2016
License     : GPL-3
Maintainer  : Camilo Rodríguez and Jonathan Prieto-Cubides
Stability   : stable
Portability : POSIX

NatEnconding is a Haskell program intends to provide an alternative
encoding for the natural numbers.
-}

{-# LANGUAGE UnicodeSyntax #-}

module NatEncoding
  where


import           Data.List       (union, (\\))
import           Numeric.Natural (Natural)
import           Test.QuickCheck (Property, quickCheck, (==>))

-- | The 'Var Sym' defined one String kind
type Sym = String

-- | The 'Expr' defined one data set for λ-term
data Expr
  -- | The 'Var Sym' represents the normal form in ´v`|variable´'`
  = Var Sym
  -- | The 'App Expr Expr' represents the normal form in ´(` λ-term λ-term ´)`
  | App Expr Expr
  -- | The 'Lam Sym Expr' represents the normal form in ´(λ` variable λ-term ´)`
  | Lam Sym Expr
  deriving (Eq, Read)

-- | The 'Show Expr' defined one interface for show the λ-term
instance Show Expr where
  show (Var x)   = x
  show (App m n) = show m ++ " " ++ show n
  show (Lam x m) = "λ" ++ x ++ "." ++ show m

-- | The 'nf' function finds the normal form of a λ-term.
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

-- | The 'betaEq' function asserts if two λ-terms are equal.
betaEq ∷ Expr → Expr → Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

-- | The 'freeVars' function finds the free variables of a λ-term.
freeVars ∷ Expr → [Sym]
freeVars (Var x)   = [x]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i e) = freeVars e \\ [i]

-- | The 'subst' function replaces all free occurrences of v by b inside x.
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

-- | The 'substVar' function replaces one variable with another.
substVar ∷ Sym → Sym → Expr → Expr
substVar x s' = subst x (Var s')

-- | The 'alphaEq' function is for compare couple λ-term are equal.
alphaEq ∷ Expr → Expr → Bool
alphaEq (Var v)   (Var v')    = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (substVar s' s e')
alphaEq _ _                   = False

-- | The 'app²' function performs two applications in one λ-term.
app² ∷ Expr → Expr → Expr → Expr
app²  f x = App $ App f x

-- | The 'app³' function performs three applications.
app³ ∷ Expr → Expr → Expr → Expr → Expr
app³ f x y = App $ App (App f x) y

-- | The 'x¹, y¹, f¹' are handy variables.
x¹, y¹, f¹ ∷ Expr
x¹ = Var "x"
y¹ = Var "y"
f¹ = Var "f"

-- | The 'true' function is the combinator K.
true ∷ Expr
true = Lam "x" $ Lam "y" x¹

-- | The 'false' function is the combinator K*.
false ∷ Expr
false = Lam "x" $ Lam "y" y¹

-- | The 'false' function is the combinator if-then-else.
iff ∷ Expr
iff = Lam "f" $ Lam "x" $ Lam "y" $ app² f¹ x¹ y¹

-- | The 'testIf' function applies iff.
testIf ∷ Expr → Expr → Expr → Expr
testIf = app³ iff

-- | The 'pair' function is the combinator pair.
pair ∷ Expr
pair = Lam "x" $ Lam "y" $ Lam "f" $ app² f¹ x¹ y¹

-- | The 'zero' function is the combinator I.
zero ∷ Expr
zero = Lam "x" $ Var "x"

-- | The 'isZero' function is the combinator Zero.
isZero ∷ Expr
isZero = Lam "x" $ App x¹ true

-- | The 'testIf' function applies the combinator Zero.
tZero ∷ Expr → Expr
tZero = App isZero

-- | The 'succ'' function is the combinator S+.
succ' ∷ Expr
succ' = Lam "x" $ Lam "y" $ app² y¹ false x¹

-- | The 'pred'' function is the combinator P-.
pred' ∷ Expr
pred' = Lam "x" $ App x¹ false

-- | The 'yComb' function is the combinator Y.
yComb ∷ Expr
yComb = Lam "f" $ App (Lam "x" fxx) (Lam "x" fxx)
  where
    fxx ∷ Expr
    fxx = App f¹ $ App x¹ x¹

-- | The 'applyY' function applies the combinator Y.
applyY ∷ Expr → Expr
applyY = App yComb

-- | The 'n¹, m¹, a¹' are handy variables.
n¹, m¹, a¹ ∷ Expr
n¹ = Var "n"
m¹ = Var "m"
a¹ = Var "a"

-- | The 'eN' function returns the λ-term associated with the natural number n.
eN ∷ Natural → Expr
eN 0  = zero
eN nn = app² pair false $ eN (nn-1)

-- | The 'eAdd' function addition.
eAdd ∷ Expr
eAdd = applyY $ Lam "a" $ Lam "n" $ Lam "m" $
  testIf (tZero n¹) m¹ suma
    where
      -- n+m = succ((n-1) + m)
      suma ∷ Expr
      suma = App succ' $ app² a¹ (predW n¹) m¹

-- | The 'eMult' performs the multiplication between two encoded naturals.
eMult ∷ Expr
eMult = applyY $ Lam "a" $ Lam "n" $ Lam "m" $
  testIf (tZero n¹) zero $ testIf (tZero m¹) zero multi
    where
      -- multi = ((n-1) * m) + m
      multi ∷ Expr
      multi = addW (app² a¹ (predW n¹) m¹) m¹


-- The next functions were taken from
-- http://www1.eafit.edu.co/asr/courses/ffpl-CM0848/lab.html

-- | The 'predW' function is for apply predecessor.
predW ∷ Expr → Expr
predW = App pred'

-- | The 'predW' function applies addition.
addW ∷ Expr → Expr → Expr
addW = app² eAdd

-- | The 'predW' function applies multiplication.
multW ∷ Expr → Expr → Expr
multW = app² eMult

-- | The 'propPred' function tests the predecessor function.
propPred ∷ Natural → Property
propPred n = n > 0 ==> betaEq (predW $ eN n) (eN $ n - 1)

-- | The 'propAdd' function tests  the addition function.
propAdd ∷ Natural → Natural → Bool
propAdd m n = betaEq (addW (eN m) (eN n)) (eN $ m + n)

-- | The 'propMult' function tests the multiplication function.
propMult ∷ Natural → Natural → Bool
propMult m n = betaEq (multW (eN m) (eN n)) (eN $ m * n)

-- | The 'tests' function executes tests to valid operations of NatEncoding.
tests ∷ IO ()
tests = do
  quickCheck propPred
  quickCheck propAdd
  quickCheck propMult

-- | The 'main' init NatEncoding test
main ∷ IO ()
main = tests
