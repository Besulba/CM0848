# NatEnconding.hs

Camilo Rodriguez and Jonathan Prieto-Cubides

NatEnconding is a Haskell program intends to provide
an alternative enconding for the natural numbers
into the λ-calculus. This enconding follows an inductive
definition of natural numbers using *pairings*
(See more details in Ref.~Barendregt, 2000).
The type of λ-terms as the β-rule, α-rule were adapted from
the blog's version of Augustsson in its blog.

The enconding is as follows.

For all x ∈ ℕ,

```
    [0] := λx.x
    [n] := [false,[n]]
```

where `false := λxy.y`.

Other λ-terms used in the implementation were:

```
    true    := λxy.x
    succ    := λx.[false,[x]]
    pred    := λx.xfalse
    isZero  := λx.xtrue
```

### Definitions

In this section we show the definition of the arithmetic operators.

* Adding function

```
addW ≡ Y (λanm.if (isZero n) then m else (succ (a (pred n) m)))
```

* Multiplying function

```Haskell
multiW ≡ Y (λanm.
    if (isZero n) then zero
    else (if (isZero m) then zero else (addW m (a (pred n) m)))
```
* Predecessor function

```Haskell
predW ≡ λx.pred x
```

### Usage

Load the module as usual in Haskell, and then try the following.
In the following examples, `nf` is the function that normalizes an
λ-expression.

* Obtaining an enconding of a natural number

```Haskell
-- | Three examples are given below:
--
--  >>> nf $ eN 0
--  0 = λx.x 
--
--  >>> nf $ eN 1
--  1 = λf.f λx.λy.y λx.x
--
--  >>> nf $ eN 2
--  2 = λf.f λx.λy.y λf.f λx.λy.y λx.x
```

* Adding two natural numbers

```Haskell
-- | One examples are given below:
--
-- >>> nf $ addW (eN 0) (eN 2)
-- 0 + 2 = 2 = λf.f λx.λy.y λf.f λx.λy.y λx.x
```

* Multiplying two natural numbers

```Haskell
-- | One examples are given below:
--
-- >>> nf $ multW (eN 1) (eN 1)
-- 1 * 1 = 1 = λf.f λx.λy.y λx.x
```

### Testing

The module is using QuickCheck testing, and you can check with

```
$ runghc NatEnconding.hs
```

or calling the function `tests`.


### References

Barendregt, Henk and Barendsen, Erik (2000). *Introduction to Lambda Calculus*.
Revisited edition, Mar. 2000 (Chap. 3).

<<<<<<< HEAD
### Acknowledgment

Augustsson, Lennart. An Implementation of a Dependently Typed Lambda Calculus *Simpler, Easier!*. Blog version, Oct. 2007.
