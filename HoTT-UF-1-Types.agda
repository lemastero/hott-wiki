{- univalent mathematics vs classic mathematics
------------------------------------------------
1. basic things are types not sets
types are higher groupoids
type of truth      is -1-groupoids  e.g. booleans
type of N          is 0-groupoid    e.g. sets
type of monoids    is 1-groupoid    ???
type of categories id 2-groupoid    ???

2. HoTT encode logic
mathematical statemens are types not truth values (t.v. are special kind of type)
logical operations are sepcial case of type operations
mathematic is first and logic is derived

3. equality

(it is not the case that things are true or not,
they can be true in many ways,
e.g. for sets we want to know if they have the same objects,
for monoid not only the same objects but does it preserve homomorphisms so m. isomorphism
for categories we want equivalence of categories)

value of equality ≡ is a identity type, not neccessarily a truth value
identity type collect the ways mathematical objects are identified
identity type for N          is -1-groupoid - truth (they can be equal in at most 1 way)
identity type for monoids    is 0-groupoid - set (monoid isomorphisms)
identity type for categories is 1-groupoid (equivalences of categories)

4. universe levels (levels of types) are n-groupoids (possibly infintiy groupoids)

5. univalence axiom
* univalence axiom there is a canonical bijectin between
type equivalences and type identifications
* univalence is refinement of isomorphism that works uniformly for all types

6. distinguish property (unspecified ting exists) from data or structure (specific thing exists)

MLTT = STLC + identity types + universes
HoTT = MLTT (containins: identity types & universes) + univalence axiom

HoTT do not assume:
- axiom of choice (AOC)
- principle of excluded middle (EM)
but those axioms are consistent and can be assumed.
Formulation of AOC and EM formulated inside HoTT differs from those in formulated in sets.

Resources:
  https://github.com/martinescardo/TypeTopology/blob/master/source/SpartanMLTT.lagda
-}

{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-1-Types where

open import HoTT-UF-0-Universes public

{- Spartan MLTT
---------------
- empty type (Nothing/Void/Zero)
- one element type (Unit/One)
- type of natural numbers (Nat)
- type formers: binary sum (either), product (tuple), dependent product, dependent sum, identity type
- universes
-}

{-
type theory: empty type
logic: false
set theory: empty set
category theory: initial object
homotopy theory: space that have no points

formation rules:

G ctx
----------- 0-FORM
G |- 0 : U

no introduction rules


If I get element of 0
I can construct whatever I like (there is morphism to any other object)

e:Zero  A type
-------------- Zero-ELIM
absurd(e): A

I can proove any equation I like (uniqueness of morphism to any object):
TODO study this later (covered by lectures by Andrey Bauer) WTF is this?

e:Zero  s:A  t:A  A type
-------------------------
  s ≡ t

no equations

HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#emptytype
HoTT Book https://homotopytypetheory.org/book/ A.2.3
-}
data Zero : Type Universe0 where

-- TODO this is dependent version of absurd? is this universal property of 0 ???
-- property of Zero holds (vacuously) for every value from Zero
Zero-induction : (P : Zero -> Type UniverseU)
                          -- no base case
                          -- no inductive case
 -> (x : Zero) -> P x     -- property P holds for all elements of type Zero
Zero-induction A ()

-- type is empty when we have a function to the empty type
not : Type UniverseU -> Type UniverseU
not X = X -> Zero

-- unique function from Zero to any type A
Zero-recursion : (A : Type UniverseU) -> Zero -> A
Zero-recursion A a = Zero-induction (\ _ -> A) a

absurd         : (A : Type UniverseU) -> Zero -> A
absurd = Zero-recursion

{-
type theory: one element type
logic: truth
set theory: one element set (singleton)
category theory: terminal object
homotopy theory: one-point space

------- One-FORM
1 type

------ One-INTRO
* : 1

no elimination rules

equations - uniqueness:

s:1  t:1
--------
s ≡ t

or alternatively

s:1
------
s ≡1 *

HoTT Book https://homotopytypetheory.org/book/ A.2.8
HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#onepointtype
-}
data One : Type Universe0 where
  <> : One

-- for any property P of type One, if P(<>) it holds for <>
-- then P(x) it holds for all x: One
One-induction : (P : One -> Type UniverseU)
  -> P <>               -- base case
                        -- no inductive case
  -> (x : One) -> P x   -- property P holds for every element of One
One-induction P a <> = a

-- special case of One-induction when P do not depend on x
One-recursion : (P : Type UniverseU) ->
  P ->
  (One -> P)
One-recursion P a x = One-induction (\ _ -> P) a x

-- unique function from any type to One
unit : {A : Type UniverseU} -> A -> One
unit x = <>

{-
binary sum type
type theory: sum type (either)
category theory: coproduct
sets: disjoint union
logic: or

formation rule:

A type  B type
--------------
A + B type

introduction rules

   a : A
--------------
left(a) : A+B

   b : B
--------------
right(b) : A+B

elimination rule:

a:A |- ca:C   b:B |- cb:C  ab: A+B
----------------------------------
    case(a.M;b.N;ab): A+B

computation rules:

x:A|-M:C y:B­­|-N:C O:A
------------------------------
case(x.M;y.N,left(O))≡M[O/x]:C

x:A|-M:C y:B­­|-N:C O:B
------------------------------
case(x.M;y.N,right(O))≡N[O/y]:C


HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#binarysum
HoTT Book https://homotopytypetheory.org/book/ A.2.6
-}
data _+_ (X : Type UniverseU) (Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
 Left : X -> X + Y
 Right : Y -> X + Y

infixr 20 _+_

+-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : X + Y -> Type UniverseW)
 -> ((x : X) -> P (Left  x))   -- base case Left
 -> ((y : Y) -> P (Right y))   -- base case Right
                               -- no inductive case
 -> (z : X + Y) -> P z         -- property P holds for all elements of X + Y
+-induction P f _ (Left x) = f x
+-induction P _ g (Right y) = g y

+0-right-id : {A : Type UniverseU} -> A + Zero -> A
+0-right-id = {!   !}

+0-left-id : {A : Type UniverseU} -> Zero + A -> A
+0-left-id x = {!   !}

comm-+ : {A B : Type UniverseU} -> A + B -> B + A
comm-+ x = {!   !}

assocLR-+ : {A B C : Type UniverseU} -> (A + B) + C -> A + (B + C)
assocLR-+ x = {!   !}

assocRL-+ : {A B C : Type UniverseU} -> A + (B + C) -> (A + B) + C
assocRL-+ x = {!   !}

{-
binary product
category theory: product
-}
record _*_ (S : Type UniverseU)(T : Type UniverseV) : Type (UniverseU umax UniverseV)  where
  constructor _,_
  field
    fst : S
    snd : T

-- TODO * induction, recursion,

right-unit-One* : {A : Type UniverseU} -> (A * One) -> A
right-unit-One* x = {!   !}

left-unit-One* : {A : Type UniverseU} -> One * A -> A
left-unit-One* x = {!   !}

comm-* : {A : Type UniverseU}{B : Type UniverseU} -> A * B -> B * A
comm-* x = {!   !}

assocLR-* : {A B C : Set} -> (A * B) * C -> A * (B * C)
assocLR-* x = {!   !}

assocRL-* : {A B C : Type UniverseU} -> A * (B * C) -> (A * B) * C
assocRL-* x = {!   !}

{-
type theory: 2 element type
classic logic: booleans
set theory: 2 element set
category theory: -
homotopy theory: 2-point space (?)
-}

data Bool : Type Universe0 where
  True : Bool
  False : Bool

-- intuition we can draw truth table
--        | b | P b |
--  true  |   |     |
--  false |   |     |
Bool-induction : (A : Bool -> Type UniverseU)
 -> A True             -- base case True
 -> A False            -- base case False
 -> (b : Bool) -> A b  -- property P holds for all elements b
Bool-induction A aT aF True = aT
Bool-induction A aT aF False = aF

Bool-recursion : (A : Type UniverseU)
 -> A
 -> (Bool -> A -> A)
 -> Bool -> A
-- Bool-recursion A a f b = f b a -- TODO why not this
Bool-recursion A a f b = a

--Nat-recursion X = Nat-induction (\ _ -> X)

-- type Bool formulated using binary sum and One type
2T : Type Universe0
2T = One + One

data YesPerhapsNo : Type Universe0 where
  Yes : YesPerhapsNo
  Perhaps : YesPerhapsNo
  No : YesPerhapsNo

-- TODO YesMaybeNo induction recursion

{- type of natural numbers

formation rules:

------
N type

introduction rules:

-------
0 : Nat

n: Nat
------------
Succ n : Nat

elimination rules: induction principle

-- similar to Peano Axioms
-- N consist of element Zero and successor function Succ

HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#naturalnumbers
HoTT Book https://homotopytypetheory.org/book/ A.2.9
-}
data Nat : Type Universe0 where
  ZeroN : Nat
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}


_+N_ : Nat -> Nat -> Nat
a +N b     = {!   !}

_*N_ : Nat -> Nat -> Nat
a *N b     = {!   !}

_^N_ : Nat -> Nat -> Nat
a ^N b       = {!   !}

{-
Induction principle
a0 : P(Zero) is base case
A is function that create sth from natural numbers
we want f that will move base case to next step
f  : Π(n:N).P(n) -> P(Succ(n))
P  : Nat -> UniverseU

indN(P,a0,f,k):P(k)
indN(P,a0,f,0) ≡ a0
indN(P,a0,f,Succ(m)) ≡P(Succ(m)) f m (indN(P,a0,f,m))

Usuall induction principle P: Nat -> Bool and last 2 equations will dissapear

base case       a0 : P Zero
induction setp  f : (n : Nat) -> P n -> P (Succ n)
number n say how to get an element of type A n by primitve recursion
-}
Nat-induction : (P : Nat -> Type UniverseU)
 -> P ZeroN                           -- base case
 -> ((n : Nat) -> P n -> P (Succ n))  -- inductive case
 -> (n : Nat) -> P n                  -- property P holds for all element of N
Nat-induction P s t = h
  where
     h : (k : Nat) -> P k
     h 0        = s
     h (Succ n) = t n (h n)

Nat-induction-2 : (P : Nat -> Type UniverseU)
 -> P ZeroN                           -- base case
 -> ((n : Nat) -> P n -> P (Succ n))  -- inductive case
 -> (n : Nat) -> P n                  -- property P holds for all element of N
Nat-induction-2 P P0 t 0 = P0
Nat-induction-2 P P0 t (Succ n) = t n (Nat-induction-2 P P0 t n) -- TODO is this correct ?

{-
Recurson principle is induction principle specialized to the clase
where P(n) = A
-}
Nat-recursion : (A : Type UniverseU)
 -> A
 -> (Nat -> A -> A)
 -> Nat -> A
Nat-recursion X = Nat-induction (\ _ -> X) -- TODO implement differently

Nat-iteration : (A : Type UniverseU)
 -> A
 -> (A -> A)
 -> Nat -> A
Nat-iteration A x f = Nat-recursion A x (\ _ x -> f x) -- TODO implement differently

data Fibonacci : Type Universe0 where
  fib0 : Fibonacci
  fib1 : Fibonacci
  nextFib : Fibonacci -> Fibonacci -> Fibonacci

Fibonacci-induction : (P : Fibonacci -> Type UniverseU)
  -> P fib0
  -> P fib1
  -> ((f1 : Fibonacci) -> (f2 : Fibonacci) -> P f1 -> P f2 -> P (nextFib f1 f2))
  -> (f : Fibonacci) -> P f
Fibonacci-induction P Pf0 Pf1 ffPff fib0 = Pf0
Fibonacci-induction P Pf0 Pf1 ffPff fib1 = Pf1
Fibonacci-induction P Pf0 Pf1 ffPff (nextFib f1 f2) =
  ffPff f1
        f2
        (Fibonacci-induction P Pf0 Pf1 ffPff f1)
        (Fibonacci-induction P Pf0 Pf1 ffPff f2)

-- TODO fib-recursion
-- TODO fib-iteration

-- TODO recursion, 1+X = Maybe X,
data Maybe (X : Type UniverseU) : Type UniverseU where
  Just : (x : X) -> Maybe X
  Nothing : Maybe X

Maybe-induction : {X : Type UniverseU} (P : Maybe X -> Type UniverseW)
  -> ((x : X) -> P (Just  x))   -- base case Just x -> P (Just x)
  -> P Nothing                  -- base case           P Nothing
  -> (mx : Maybe X) -> P mx     -- property P holds for all Maybe X
Maybe-induction P PJx PN (Just x) = PJx x
Maybe-induction P _ PN Nothing = PN

-- TODO recursion, 1 + Either == Wedge
data Wedge (X : Type UniverseU)(Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  nowhere : Wedge X Y
  here : (x : X) -> Wedge X Y
  there : (y : Y) -> Wedge X Y

Wedge-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : Wedge X Y -> Type UniverseW)
 -> P nowhere
 -> ((x : X) -> P (here x))
 -> ((y : Y) -> P (there y))
 -> (w : Wedge X Y) -> P w
Wedge-induction P pn _ _ nowhere = pn
Wedge-induction P _ ph _ (here x) = ph x
Wedge-induction P _ _ pt (there y) = pt y

-- TODO recursion, 1 + Pair == Smash
data Smash (X : Type UniverseU) (Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  nada : Smash X Y
  smash : (x : X) -> (y : Y) -> Smash X Y

Smash-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : Smash X Y -> Type UniverseW)
  -> P nada
  -> ((x : X) -> (y : Y) -> P (smash x y))
  -> (s : Smash X Y) -> P s
Smash-induction P pn ps nada = pn
Smash-induction P pn ps (smash x y) = ps x y

-- TODO recursion, Pair + Either == These
data These (X : Type UniverseU)(Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  this : (x : X) -> These X Y
  that : (y : Y) -> These X Y
  these : (x : X) -> (y : Y) -> These X Y

-- TODO induction
These-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : These X Y -> Type UniverseW)
  -> ((x : X) -> P (this x))
  -> ((y : Y) -> P (that y))
  -> ((x : X) -> (y : Y) -> P (these x y))
  -> (t : These X Y) -> P t
These-induction P xpx ypy xypxy (this x) = xpx x
These-induction P xpx ypy xypxy (that y) = ypy y
These-induction P xpx ypy xypxy (these x y) = xypxy x y

-- TODO recursion, 1 + These == Can
data Can (X : Type UniverseU)(Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  non : Can X Y
  one : (x : X) -> Can X Y
  eno : (y : Y) -> Can X Y
  two : (x : X) -> (y : Y) -> Can X Y

-- Fin n type of numbers 0 ... n-1
data Fin : Nat -> Set where  -- TODO use UniverseU
  fzero : {n : Nat} -> Fin (Succ n)          -- 0 belongs to every Fin n
  fsucc : {n : Nat} -> Fin n -> Fin (Succ n) -- for all natural numbers n they are part of Fin (n+1)

-- TODO Fin induction
-- TODO Fin recursion
-- TODO max fin
-- TODO min fin

-- TODO List

-- TODO NonEmptyList

-- TODO Vector

-- TODO Function type
-- TODO Function induction
-- TODO Function recursion
