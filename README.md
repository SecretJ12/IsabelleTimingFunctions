# BachelorThesisTimingFunctions
The goal of the bachelor thesis is to extend the Proof Assistant Isabelle
by an automatic generator for runtime functions.

## Content
Repository consists of three parts:
- `src` contains the generator itself
- `test` tests the generator against all the timing function of "Functional Data Structures and Algorithms" [1]
  - Current proofs are based on the devel version of the AFP as well as the newest version of Isabelle
- `proof` contains a formalization about the correctness of the translation schema. Proof by David Sands [2]

## Generator
The generator implements the following commands
```Isabelle
define_time_0 {NameOfFunction}
define_time_fun {NameOfFunction} [equations {thms list}]
```
The first command marks functions as constants. Therefore they will be translated to 0.
Constructors are seen as constants by default as well a the following functions:
```Isabelle
+, -, *, /, div, <, ≤, Not, ∧, ∨, =, Num.numeral_class.numeral
```

Expressions will be converted by the following schema (conversion function represented by T)
- Constants: `T c = 0`
- Zero functions / Constructors: `T (f a b ...) = T a + T b + ...`
- Functions: `T (f a b ...) = T_f a b ...`
- If-else: `T (if b then t else f) = T b + if b then T t else T f`
- Case: `T (case c of a1 => c1 | a2 => c2 | ...) = T c + (case c of a1 => T c1 | a2 => T c2 | ...)`
- Let: `T (let x = e in c) = T e + (λx. T c) e`

Functions definitions will be translated by the following schema
- Non-recursive function: `T (f (a,b,c,...) = e) = (T_f (a,b,c,...) = T e)`
- Recursive function: `T (f (a,b,c,...) = e) = (T_f (a,b,c,...) = 1 + T e)`

Expressions translated to 0 will be neglected when used in another expression.
Functions called by the specified function will be translated automatically.

With the keyword `equations` you can specify theorems proofing another probably easier version of the terms.
An example can be found in `test/T_Splay_Tree.thy`

## Restrictions
The following constructs are not allowed
- Lambdas
- Partial applications
- Mutual recursion

## Links
- [1] https://functional-algorithms-verified.org/
- [2] https://spiral.imperial.ac.uk/bitstream/10044/1/46536/2/Sands-D-1990-PhD-Thesis.pdf