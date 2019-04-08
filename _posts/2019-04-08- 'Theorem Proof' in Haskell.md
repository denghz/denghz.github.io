---
layout:     post   				    # 使用的布局（不需要改）
title:      '"Theorem Proof" in Haskell'			# 标题 
subtitle:   '类型即命题，程序则证明' #副标题
# permalink:
date:       2019-04-08 	# 时间
author:     DHZ 						# 作者
header-img: img/haskell.jpg	#这篇文章标题背景图片
catalog: true 						# 是否归档
tags:								#标签
    - lambda calculus
    - functional programming
    - programmimng
    - Haskell
    - logic
    - type theorem
---

## Programs *are* Proofs!

It sounds really weird that program are proofs, but this is where it gets *really* fun.

Think about the types in the simple typed language:

```
type ::= primitive | function | ( type )
primitive ::= A | B | C | D | ...
function ::= type -> type
```

Look at the type "A -> A". Now, instead of seeing "->" as the function type constructor, try looking at it as logical implication. "A implies A" is clearly a theorem of intuitionistic logic. So the type "A -> A" is a *theorem* in the corresponding logic.

Now, look at "A -> B". That's *not* a theorem, unless there's some other context that proves it. As a function type, that's the type of a function which, without including any context of any kind, can take a parameter of type A, and return a value of a *different* type B. You can't do that - there's got to be some context which provides a value of type B - and to access the context, there's got to be something to allow the function to access its context: a free variable. Same thing in the logic and the lambda calculus: you need some kind of context to establish "A->B" as a theorem (in the logic)

If there is a closed expression whose type is a theorem in the corresponding intuitionistic logic, then the expression that has that type *is a proof* of the theorem.

![curry-howard-iso](/img/curry-howard-iso.jpg)

As all we known, Haskell doesn't have [dependent type](<https://en.wikipedia.org/wiki/Dependent_type>), but we can get very close with extensions, e.g. "GADT (Generalized Algebraic Data Type)", and prove theorem by it.

### Use GADT to "simulate" Dependent Type

First we need types to represent **values**

```haskell
data Z
data S n
```

Notice that `Z` and `S n` are just types, you cannot construct values with these types. We need to connect them with some values we can construct.

```haskell
data Nat :: * -> * where
	Zero :: Nat Z
	Succ :: Nat n -> Nat (S n)
```

Now we have natural numbers whose values is represented by types .

```haskell
(Succ Zero) :: Nat (S Z) -- 1
(Succ (Succ Zero)) :: Nat (S (S Z)) --2
```

In another words, its type is isomorphic to its value.

It is meaningless to have only numbers, so the next thing is to build arithmetic on it.

What would be `Nat n + Nat m` ?

Firstly, it should by a `Nat`, and then its type should correspond to the sum.

With the help of GHC's Type Family and Type Operator extension, we can give reasonable definition of addition and multiplication on the level of types.

```haskell
type family (:+:) (n :: *) (m :: *) :: *
type instance Z   :+: m = m
type instance S n :+: m = S (n :+: m)
  
type family (:*:) (n :: *) (m :: *) :: *
type instance Z   :*: m = Z
type instance S n :*: m = m :+: (n :*: m)
```

Then the addition and multiplication on the level of values.

```haskell
infixl 4 + -- priority 4
(+) :: Nat n -> Nat m -> Nat (n :+: m)
Zero + n = n
(Succ x) + n = Succ (x + n)
  
infixl 5 * -- priority 5
(*) :: Nat n -> Nat m -> Nat (n :*: m)
Zero * _ = Zero
(Succ n) * m = m + n * m
```

For instance

```Haskell
(Succ (Succ Zero)) * (Succ (Succ Zero)) :: Nat (S (S (S (S Z))))
```

Since we have natural numbers based on types, we can define `Vector` now (`List` that have length information in their types).

```haskell
data Vec * -> * -> * where
	VNil :: Vec a Z -- []
	VCons :: a -> Vec a n -> Vec a (S n) -- (:)
 
(++) :: Vec a n -> Vec a m -> Vec a (n :+: m)
VNil ++ ys = ys
VCons x xs ++ y = VCons x (xs ++ y)
```

As long as we have length information, them we can build `safeHead` and `safeTail`. 

```haskell
safeHead :: Vec a (S n) -> a
safeHead (VCons x _) = x

safeTail :: Vec a (S n) -> Vec a n
safteTail (VCons _ xs) = xs
```

The type `Vec a (S n)` says that the input vector cannot be empty, so these two functions are **total** functions.

We can define *subtraction/maximum/minimum* type operator and then some other utility function of `Vector` in similar ways.

Give priorities to type operators to save some brackets later.

```haskell
infixl 2 ===
infixl 4 :+:
infixr 4 :-:
infixl 5 :*:
```

### Proof Simple Theorem now!

`Haskell` doesn't have `Prop`, so we need to describe "Equal" from scratch.

Start with defining the type which means two `Nat` equal.

```haskell
data Equal :: * -> * -> * where
    EqZ :: Equal Z Z -- 0 == 0
    EqS :: Equal n m -> Equal (S n) (S m) -- n == m => (n+1) == (m+1)
    
infixl 2 === -- priority 2
type x === y = Equal x y -- give Equal x y a shorter name
```

Now prove that `Equal` is an equivalence relationship.

It's reflexive.   $$n = n$$

```haskell
ref :: Nat n -> n === n
ref Zero = EqZ
ref (Succ n) = EqS (refl n)
```

It's symmetric.   $$ n = m \implies m = n​$$

```haskell
sym :: n === m -> m === n
sym EqZ = EqZ
sym (EqS eq) = EqS (sym eq)
```

It's transitive.   $$a = b, b = c \implies a = c$$

```haskell
infixl 3 <=> -- priority 3
(<=>) :: a === b -> b === c -> a === c
EqZ <=> EqZ = EqZ
EqS eq1 <=> EqS eq2 = EqS (eq1 <=> eq2)
```

#### Associativity of Addition

```haskell
plusComb :: Nat n -> Nat m -> Nat p -> n :+: (m :+: p) === n :+: m :+: p
```

[(A+B)+C = A+(B+C)?Prove it!](<https://www.codewars.com/kata/5c2fcbcba305ad2c4a91122d>)

#### Commutativity of Addition

```haskell
plusCommutes :: Nat n -> Nat m -> n :+: m === m :+: n
```

Commutativity is harder, but I give an idea here.

First prove the case that `m = 0`

```haskell
plusZero :: Nat a -> Z :+: a === a :+: Z
```

And prove a lemma that

```haskell
rightS :: Nat a -> Nat b -> S a :+: b === a :+: S b
```

Then use the lemma to prove the theorem.

**Or it also can be done without the lemma.**

[A+B = B+A? Prove it!](<https://www.codewars.com/kata/a-plus-b-equals-b-plus-a-prove-it/haskell>)

#### Commutativity of multiplication

Here comes the multiplication.

The idea is almost the same, but need more lemmas, e.g.:

```haskell
multCommuteS :: Nat n -> Nat m -> m :*: S n === m :+: m :*: n
plusSwap :: Nat a -> Nat b -> Nat c -> a :+: (b :+: c) === b :+: (a :+: c)
```

The proof would look like this:

```haskell
equalPlus :: Nat a -> Nat b -> a === b -> Nat c -> a :+: c === b :+: c
equalPlus a b eq Zero = symm (nPlusZero a) <=> eq <=> nPlusZero b
equalPlus a b eq (Succ c) = nPlusSm a c <=> Fuck (equalPlus a b eq c) <=> symm (nPlusSm b c)
  
equalPlus' :: Nat a -> Nat b -> a === b -> Nat c -> c :+: a === c :+: b
equalPlus' a b eq c = plusCommutes c a <=> equalPlus a b eq c <=> plusCommutes b c
  
plusSwap' :: Nat a -> Nat b -> Nat c -> a :+: b :+: c === b :+: a :+: c
plusSwap' a b = equalPlus (a + b) (b + a) (plusCommutes a b)
  
plusSwap :: Nat a -> Nat b -> Nat c -> a :+: (b :+: c) === b :+: (a :+: c)
plusSwap a b c = plusCommute a b c <=> plusSwap' a b c <=> symm (plusCommute b a c)
  
multCommuteS_1 :: Nat n -> Nat m -> n :+: (m :*: S n) === m :+: (n :+: (m :*: n))
multCommuteS_1 n m = equalPlus' (m * Succ n) (m + m * n) (multCommuteS n m) n <=> plusSwap n m (m * n)
  
multCommuteS :: Nat n -> Nat m -> m :*: S n === m :+: m :*: n
multCommuteS _ Zero = Refl
multCommuteS n (Succ m) = Fuck $ multCommuteS_1 n m
  
multCommutes :: Nat n -> Nat m -> n :*: m === m :*: n
multCommutes Zero m = symm $ multNZero m
multCommutes (Succ n) m = symm
      (multCommuteS n m <=> equalPlus' (m * n) (n * m) (multCommutes m n) m)
```

### Beyond the Naturals

We have just described the "Equal" of Naturals, but how to describe "Equal" of any value?

```haskell
data Equal :: * -> * -> * where
      Refl :: Equal a a
      Derive :: Equal a b -> Equal (p a) (p b)
```

`Refl` corresponds to `EqZ`, `Derive` corresponds to `EqS`. From the definition, `Refl` is reflexivity.  `sym` 's definition is similar to before, but the proof of transitivity needs to be modified.

```haskell
(<=>) :: a === b -> b === c -> a === c
Refl        <=> Refl        = Refl
Derive x <=> Refl        = Derive $ x      <=> Refl
Refl        <=> Derive y = Derive $ Refl <=> y
Derive x <=> Derive y = Derive $ x      <=> y
```

We can try another data to see how the new `Equal` works.

We define `Bool` in type.

```haskell
data T
data F
```

and corresponded value

```haskell
data Boolean :: * -> * where
	Tr :: Boolean T
	Fa :: Boolean F
```

Then we need *negate*, *or* , *and* in type.

```haskell
type family Inv (n :: *) :: *
type instance Inv T = F
type instance Inv F = T
  
type family (||) (n :: *) (m :: *) :: *
type instance T || T = T
type instance F || T = T
type instance T || F = T
type instance F || F = F
  
type family (&&) (n :: *) (m :: *) :: *
type instance T && T = T
type instance T && F = F
type instance F && T = F
type instance F && F = F
```

first prove double negation $$p \equiv \: \sim(\sim p)$$

```haskell
 doubleNeg :: Boolean b -> Inv (Inv b) === b
 doubleNeg Tr = Refl
 doubleNeg Fa = Refl
```

Then De Morgan's Rule

```haskell
demorgan :: Boolean a -> Boolean b -> Inv (a && b) === Inv a || Inv b
demorgan Tr Tr = Refl
demorgan Tr Fa = Refl
demorgan Fa Tr = Refl
demorgan Fa Fa = Refl
```

Similarly, we can prove some properties of Naturals by type families, e.g. parity.

```haskell
type family IsOdd (n :: *) :: *
type instance IsOdd Z = F
type instance IsOdd (S Z) = T
type instance IsOdd (S (S n)) = IsOdd n
  
type family IsEven (n :: *) :: *
type instance IsEven Z = T
type instance IsEven (S Z) = F
type instance IsEven (S (S n)) = IsEven n
```
##### Other ways to describe **Property**

We use `Equal` to describe that two types equal, in the same way, we can describe some other relationships, e.g.
another way of describing parity:

```haskell
data Even :: * -> * where
      ZeroEven :: Even Z
      Add2Even :: Even n -> Even (S (S n))
  
data Odd :: * -> * where
      OneOdd :: Odd (S Z)
      Add2Odd :: Odd n -> Odd (S (S n))
```
or x > y?

```haskell
data Greater :: * -> * where
      GreZ :: Greater (S Z) Z
      GreS1 :: Greater x y -> Greater (S x) y
      GreS2 :: Greater x y -> Greater (S x) (S y)
```