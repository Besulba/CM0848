# NatEncoding.hs

Camilo Rodriguez and Jonathan Prieto-Cubides

NatEnconding is a Haskell program intends to provide
an alternative encoding for the natural numbers
into the λ-calculus. This encoding follows an inductive
definition of natural numbers using *pairings*
(See more details in Barendregt, 2000)). We adapted a version
of the simple λ-calculus exposed by Augustsson in his
[blog](http://augustss.blogspot.com.co/2007_10_01_archive.html)
using the datatype for λ-terms, the β-rule, and α-rule.

The encoding is as follows.

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

* Obtaining an encoding of a natural number

```Haskell
> let x = Var "x"
> let zero = Lam x x
> let one = App succ' zero
> let two = App succ' uno
> eN 0
λx.x
> eN 1
λx.λy.λf.f x y λx.λy.y λx.x
> nf $ eN 1
λf.f λx.λy.y λx.x
> betaEq (eN 1) uno
True
```

* Adding two natural numbers

```Haskell
> nf $ addW (eN 0) (eN 2)
λf.f λx.λy.y λf.f λx.λy.y λx.x
> nf $ eN 2
λf.f λx.λy.y λf.f λx.λy.y λx.x

```

* Multiplying two natural numbers

```Haskell
>nf $ multW (eN 2) (eN 2)
λy.y λx.λy.y λy.y λx.λy.y λf.f λx.λy.y λf.f λx.λy.y λx.x
> nf $ eN 4
λf.f λx.λy.y λf.f λx.λy.y λf.f λx.λy.y λf.f λx.λy.y λx.x
```

### Testing

The module is using QuickCheck testing, and you can check with

```
$ runghc NatEncoding.hs
```

or calling the function `tests`.


### References

* Barendregt, Henk and Barendsen, Erik (2000). *Introduction to Lambda Calculus*.
Mar. 2000 (Chap. 3).

* Augustsson, Lennart. *Simpler, Easier!*. Blog version, Oct. 2007.