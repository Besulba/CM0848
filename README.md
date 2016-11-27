# NatEnconding.hs

Camilo Rodriguez and Jonathan Prieto-Cubides

NatEnconding is a Haskell program intends to provide
an alternative enconding for the natural numbers.
This enconding follows an inductive definition of
natural numbers using *pairing*. The enconding is as
follows.

```
    [0] := λx.x
    [n] := [false,[n]]
```

where

```
    true  := λxy.x
    false := λxy.y
    succ  := λx.[false,[x]]
    pred  := λx.xfalse
    Zero  := λx.xtrue
```

### References

Barendregt, Henk and Barendsen, Erik (2000). *Introduction to Lambda Calculus*.
Revisited edition, Mar. 2000 (Chap. 3).
