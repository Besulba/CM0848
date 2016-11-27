
-- | NatEncoding module

{-# LANGUAGE UnicodeSyntax #-}

module NatEncoding
  where


import           Data.List       (union, (\\))
import           Numeric.Natural (Natural)
import           Test.QuickCheck (Property, quickCheck, (==>))

-- @Adapted from Lennart Augustsson's blog https://goo.gl/3p6R0P
type Sym = String

data Expr = Var Sym
          | App Expr Expr
          | Lam Sym Expr
          deriving (Eq, Read)

instance Show Expr where
  show (Var x)   = x
  show (App m n) = show m ++ " " ++ show n
  show (Lam x m) = "λ" ++ x ++ "." ++ show m

data Type = Base | Arrow Type Type
          deriving (Eq, Read, Show)

-- | The method nf finds the normal form of a λ-term.
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

betaEq ∷ Expr → Expr → Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

freeVars ∷ Expr → [Sym]
freeVars (Var x)   = [x]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i e) = freeVars e \\ [i]

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

substVar ∷ Sym → Sym → Expr → Expr
substVar x s' = subst x (Var s')

alphaEq ∷ Expr → Expr → Bool
alphaEq (Var v)   (Var v')    = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (substVar s' s e')
alphaEq _ _                   = False

app2 ∷ Expr → Expr → Expr → Expr
app2 f x = App $ App f x

app3 ∷ Expr → Expr → Expr → Expr → Expr
app3 f x y = App $ App (App f x) y

x¹, y¹, f¹ ∷ Expr
x¹ = Var "x"
y¹ = Var "y"
f¹ = Var "f"

true ∷ Expr
true = Lam "x" $ Lam "y" x¹

false ∷ Expr
false = Lam "x" $ Lam "y" y¹

iff ∷ Expr
iff = Lam "f" $ Lam "x" $ Lam "y" $ app2 f¹ x¹ y¹

testIf ∷ Expr → Expr → Expr → Expr
testIf = app3 iff

pair ∷ Expr
pair = Lam "x" $ Lam "y" $ Lam "f" $ app2 f¹ x¹ y¹

zero ∷ Expr
zero = Lam "x" $ Var "x"

isZero ∷ Expr
isZero = Lam "x" $ App x¹ true

tZero ∷ Expr → Expr
tZero = App isZero

succ' ∷ Expr
succ' = Lam "x" $ Lam "y" $ app2 y¹ false x¹

pred' ∷ Expr
pred' = Lam "x" $ App x¹ false

yComb ∷ Expr
yComb = Lam "f" $ App (Lam "x" fxx) (Lam "x" fxx)
  where
    fxx ∷ Expr
    fxx = App f¹ $ App x¹ x¹

applyY ∷ Expr → Expr
applyY = App yComb

n¹, m¹, a¹ ∷ Expr
n¹ = Var "n"
m¹ = Var "m"
a¹ = Var "a"

eN ∷ Natural → Expr
eN 0  = zero
eN nn = app2 pair false $ eN (nn-1)

eAdd ∷ Expr
eAdd = applyY $ Lam "a" $ Lam "n" $ Lam "m" $
  testIf (tZero n¹) m¹ suma
    where
      -- n+m = succ((n-1) + m)
      suma ∷ Expr
      suma = App succ' $ app2 a¹ (predW n¹) m¹

eMult ∷ Expr
eMult = applyY $ Lam "a" $ Lam "n" $ Lam "m" $
  testIf (tZero n¹) zero $ testIf (tZero m¹) zero multi
    where
      -- multi = ((n-1) * m) + m
      multi ∷ Expr
      multi = addW (app2 a¹ (predW n¹) m¹) m

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

main ∷ IO ()
main = return ()
