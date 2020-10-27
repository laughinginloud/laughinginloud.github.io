---
title: "Extending Peano axioms to Z"
author: laughinginloud
date: Oct 27, 2020
tags: [maths, haskell]
description: Experimenting with Peano axioms
image: peano.jpg
---

# Extending Peano axioms to $\mathbb{Z}$

## Introduction

I’m a simple man: to make me happy you just need recursion. So, when at the beginning of my Haskell journey I was introduced to Peano axioms, I was ecstatic. So simple, so elegant, yet so powerful. I fell in love with them.

A few weeks ago I started preparing some little examples to introduce a few of my friends to functional programming, so I decided to implement the natural numbers using these axioms, to show them the power of the type system. So I began wondering: how can I take this further? How can I extend these axioms to the integers?

## The introduction of a new function

So, first of all, let’s see those beautiful axioms again, shall we?

1. $\exists \; 0 \in \mathbb{N}$;

2. $\exists \; S : \mathbb{N} \to \mathbb{N}$;

3. $x \neq y \implies S(x) \neq S(y)$;

4. $S(x) \neq 0, \forall x$;

5. if  $U \subseteq \mathbb{N} :$

   1. $0 \in U$
   2. $x \in U \implies S(x) \in U$

   then $U = \mathbb{N}$.

Pretty straightforward. We just define a base number, $0$, and a function, $S$, which gives us the next number. The first few numbers are then:
$$
\begin{aligned}
0 &= 0\\
1 &= S(0)\\
2 &= S(1) = S(S(0))\\
3 &= S(2) = S(S(1)) = S(S(S(0)))\\
&\dots
\end{aligned}
$$
And so on. But how can we define $\mathbb{Z}$ with these axioms? We just can’t: we need something more. So, my first idea was to use a new function, called $P$. I’m sure you’ve already guessed where this is headed, but I’ll define a few laws nonetheless.

- $P : \mathbb{Z} \to \mathbb{Z}$;

- $x \neq y \implies P(x) \neq P(y)$;

- $P(S(x)) = S(P(x)) = x$.

So, simply put, $P$ gives us the previous number, so it’s just $S^{-1}$ (which is implied by the last law). We now need to change the original axioms a bit, so that they refer to $\mathbb{Z}$ and not $\mathbb{N}$. Furthermore, the fourth axiom doesn’t make sense anymore, because we can go below $0$: we aren’t in $[0;\infty)$ anymore, because we’re now in $(-\infty; \infty)$. So, a few numbers as an example:
$$
\begin{aligned}
0 &= 0\\
1 &= S(0)\\
-1 &= P(0)\\
2 &= S(S(0))\\
-2 &= P(P(0))\\
&\dots
\end{aligned}
$$
We could also say, for example, that $0 = P(1)$, but, since we said that $P = S^{-1}$, it just becomes $0 = P(S(0)) = 0$, so we still have a single representation for all numbers, which is good. This function also gives us a simple and elegant way to calculate the sum of two numbers, which is the same that we could do with the normal axioms: substitute $0$ in one of the numbers with the other number. So, $S(S(0)) + P(P(0)) = S(S(P(P(0))) = 0$. To calculate the difference we need a new function, which we’ll call $N$. The definition is:
$$
N(x) =
\begin{cases}
0 & \text{if } x = 0\\
P(N(x')) & \text{if } x = S(x')\\
S(N(x')) & \text{if } x = P(x')
\end{cases}
$$
Pretty easy. It just negates a number, so, for example, $N(S(0)) = P(0)$. This way, we can easily translate the fundamental law of subtraction, which is $x - y = x + (-y)$: we just transliterate $-y$ into $N(y)$ et voilà, we get our definition.

Now, the last operation: multiplication. Peano’s definition is:
$$
x \times y =
\begin{cases}
0 & \text{if } y = 0\\
x & \text{if } y = 1\\
x + (x \times (y - 1)) & \text{otherwise}
\end{cases}
$$

Our definition is just an extension:
$$
x \times y =
\begin{cases}
0 & \text{if } y = 0\\
x & \text{if } y = 1\\
N(x) \times N(y) & \text{if } x < 0 \and y < 0\\
N(N(x) \times y) & \text{if } x < 0\\
N(x \times N(y)) & \text{if } y < 0\\
x + (x \times (y - 1)) & \text{otherwise}
\end{cases}
$$
Basically, we just need to check for plus and minuses, to get the correct signum in the result.

It’s now time to put everything together. May I present to you the Generic Integer Axioms™ (for lack of a better name):

1. $\exists \; 0 \in \mathbb{Z}$;

2. $\exists \; S : \mathbb{Z} \to \mathbb{Z}, \,P : \mathbb{Z} \to \mathbb{Z}$;

3. $x \neq y \implies S(x) \neq S(y) \, \and \, P(x) \neq P(y) $;

4. $S(P(x)) = P(S(x)) = x, \forall x$;

5. if  $U \subseteq \mathbb{Z} :$

   1. $0 \in U$
   2. $x \in U \implies S(x), \, P(x) \in U$

   then $U = \mathbb{Z}$.

We managed to extend the axioms to $\mathbb{Z}$. Yay!

Now, let’s implement them. My language of choice is Haskell:

```haskell
{-# LANGUAGE LambdaCase #-}

module PeanoZ where

import Prelude hiding (Int)

data Int = Z | S Int | P Int
    deriving (Show, Read, Eq)

normalize :: Int -> Int
normalize = \case
    Z        -> Z
    P (S x') -> normalize x'
    S (P x') -> normalize x'
    P x'     -> P (normalize x')
    S x'     -> S (normalize x')
        
instance Ord Int where
    compare x y =
        case (x, y) of
            (P x', P y') -> compare x' y'
            (P _, _)     -> LT
            (_, P _)     -> GT
            (Z, Z)       -> EQ
            (Z, _)       -> LT
            (_, Z)       -> GT
            (S x', S y') -> compare x' y'

instance Num Int where
    (+) x y =
        normalize
        (
            case (x, y) of
                (_, Z)    -> x
                (_, P y') -> P ((+) x y')
                (_, S y') -> S ((+) x y')
        )

    (*) x y =
        normalize
        (
            case (x, y) of
                (_, Z)     -> Z
                (_, S Z)   -> x
                (P _, P _) -> (*) (negate x) (negate y)
                (P _, _)   -> negate ((*) (negate x) y)
                (_, P _)   -> negate ((*) x (negate y))
                (_, S y')  -> (+) ((*) x y') x
        )

    abs =
        (\case
            x@(P _) -> negate x
            x       -> x
        ) . normalize

    signum =
        (\case
            Z   -> 0
            P _ -> -1
            _   -> 1
        ) . normalize

    fromInteger x
        | x == 0    = Z
        | x < 0     = negate (fromInteger (abs x))
        | otherwise = S (fromInteger (x - 1))

    negate = 
        (\case
            Z   -> Z
            P x -> S (negate x)
            S x -> P (negate x)
        ) . normalize

instance Enum Int where
    toEnum = fromInteger . toInteger

    fromEnum = \case
        Z   -> 0
        P x -> (fromEnum x) - 1
        S x -> (fromEnum x) + 1
```

So, there it is: our own definition of `Int`. Technically, it should be better to call it `Integer`, since it can theoretically reach arbitrary length, although GHC has a recursion limit, but I decided to call it `Int` for brevity’s sake.

So this is the end. Or is it?

## An alternative definition

When exploring my new definition of $\mathbb{Z}$, I noticed something: we don’t need $P$. That is probably the most elegant definition, but we can be a little more *minimalistic*. In fact, we define two new major functions: $P$ and $N$. But we could just ditch $P$ and use only $N$. How? Simple: it basically acts as a binary flag. Let’s see a few exemplary numbers to get the idea:
$$
\begin{aligned}
0 &= 0\\
1 &= S(0)\\
-1 &= N(S(0))\\
2 &= S(S(0))\\
-2 &= N(S(S(0)))\\
&\dots
\end{aligned}
$$
We now need to define a few laws.

- $N : \mathbb{Z} \to \mathbb{Z}$;
- $N(0) = 0$;
- $N(N(x)) = x$;
- $x \neq y \implies N(x) \neq N(y)$;
- $S(N(S(x))) = N(x)$.

Basically, we just defined $P$ as $N(S)$, but with the added benefit of the double negation. It sort of works like a mixture of both $P$ and the previous definition of $N$: we get the best of both worlds with a single function.

I also think that these two definition of $\mathbb{Z}$ differ in how we can conceive them. I think the first one is a line, going from $-\infty$ to $\infty$, directly extending Peano’s idea, whilst the second defines two overlapping rays: the first going from $0$ to $\infty$, so $\mathbb{N}$ as Peano defined it, and the second goes from $0$ to $-\infty$. We also define a function, $N$, to jump between these two rays. In the end, the result is identical, but it’s different how we get there.

With this second definition, a problem arises: sum. In fact, we now need to take care of our “new” function $N$. Let’s see it:
$$
x + y =
\begin{cases}
x & \text{if } y = 0\\
N(x' + y') & \text{if } x = N(x') \, \and \, y = N(y')\\
N(x') + y' & \text{if } x = N(S(x')) \, \and \, y = S(y')\\
x' + S(y') & \text{if } x = S(x') \, \and \, y = N(S(y'))\\
S(x) + y' & \text{if } y = S(y')\\
\end{cases}
$$
It also works for differentiation, keeping in mind the rule $x - y = x + (-y)$. Multiplication, on the other hand, it’s the same as before. *Phew*.

Okay, it’s now time to put everything together (again). May I present to you, the Minimalistic Integer Axioms™:

1. $\exists \; 0 \in \mathbb{Z}$;

2. $\exists \; S : \mathbb{Z} \to \mathbb{Z}, \, N : \mathbb{Z} \to \mathbb{Z}$;

3. $x \neq y \implies S(x) \neq S(y) \, \and \, N(x) \neq N(y) $;

4. $S(x) \neq 0, \, \forall x$;

5. $N(0) = 0$;

6. $N(N(x)) = x, \, \forall x$;

7. $S(N(S(x))) = N(x)$;

8. if  $U \subseteq \mathbb{Z} :$

   1. $0 \in U$
   2. $x \in U \implies S(x), \, N(x) \in U$

   then $U = \mathbb{Z}$.

I’ve defined them *minimalistic* but they’re more than the generic ones. *Amazing*.

It’s now time for Haskell to shine:

```haskell
{-# LANGUAGE LambdaCase #-}

module PeanoZ where

import Prelude hiding (Int)

data Int = Z | S Int | N Int
    deriving (Show, Read)

instance Eq Int where
    (==) x y =
        case (x, y) of
            (Z, Z)       -> True
            (S x', S y') -> (==) x' y'
            (N Z, Z)     -> True
            (Z, N Z)     -> True
            (_, _)       -> False

normalize :: Int -> Int
normalize = \case
    Z           -> Z
    N Z         -> Z
    N (N x)     -> normalize x
    N x         -> negate (normalize x)
    S (N (S x)) -> normalize (negate (normalize x))
    S x         -> S (normalize x)

instance Ord Int where
    compare x y =
        case (x, y) of
            (N x', N y') -> compare x' y'
            (N _, _)     -> LT
            (_, N _)     -> GT
            (Z, Z)       -> EQ
            (Z, _)       -> LT
            (_, Z)       -> GT
            (S x', S y') -> compare x' y'

instance Num Int where
    (+) x y =
        normalize
        (
            case (x, y) of
                (_, Z)           -> x
                (N x', N y')     -> negate ((+) x' y')
                (N (S x'), S y') -> (+) (negate x') y'
                (S x', N (S y')) -> (+) x' (negate y')
                (_, S y')        -> (+) (S x) y'
        )

    (*) x y =
        normalize
        (
            case (x, y) of
                (_, Z)       -> Z
                (_, S Z)     -> x
                (N x', N y') -> (*) x' y'
                (N x', _)    -> negate ((*) x' y)
                (_, N y')    -> negate ((*) x y')
                (_, S y')    -> (+) ((*) x y') x
        )

    abs =
        (\case
            N x -> x
            x   -> x
        ) . normalize

    signum =
        (\case
            Z   -> 0
            N _ -> -1
            _   -> 1
        ) . normalize

    fromInteger x
        | x == 0    = Z
        | x < 0     = N (fromInteger (abs x))
        | otherwise = S (fromInteger (x - 1))

    negate =
        (\case
            Z   -> Z
            N x -> x
            x   -> N x
        ) . normalize

instance Enum Int where
    toEnum = fromInteger . toInteger

    fromEnum = \case
        Z   -> 0
        N x -> negate (fromEnum x)
        S x -> (fromEnum x) + 1
```

This time I’ve decided to manually implement `Eq` just to be sure that $N(0) = 0$. It should never happen, but better safe than sorry.

## Conclusion

Okay, we’ve done it: we managed to extend Peano axioms to $\mathbb{Z}$. Nice! So, should you use this definition of `Int` instead of GHC’s? *Absolutely not*. This was just a game, a way to flex the muscles of Haskell’s type system. This definition is highly inefficient. I made it only for fun and to relax a bit. That being said, feel free to test it yourself and maybe improve it.

So, you’ve reached the end of this article. This was a not-so-serious diary of a little game of mine, to basically test how much I knew about Haskell. I’ve come a long way, but the road ahead is still long. I hope that you had fun time reading this and maybe you even learned one or two new things along the way. Goodbye!