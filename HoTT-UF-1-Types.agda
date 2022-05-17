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
Zero-induction : (ZeroProperty : Zero -> Type UniverseU)
 -> (x : Zero)
 -> ZeroProperty x
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
  -> P <>
  -> (x : One)
  -> P x
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
 Left : X → X + Y
 Right : Y → X + Y

+-induction : {X : Type UniverseU} {Y : Type UniverseV} (A : X + Y -> Type UniverseW)
 -> ((x : X) -> A (Left x))
 -> ((y : Y) -> A (Right y))
 -> (z : X + Y) -> A z
+-induction A f g (Left x) = f x
+-induction A f g (Right y) = g y

id-right-Zero+ : {A : Type UniverseU} -> A + Zero -> A
id-right-Zero+ = {!   !}

id-left-Zero+ : {A : Type UniverseU} -> Zero + A -> A
id-left-Zero+ x = {!   !}

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

Bool-induction : (A : Bool -> Type UniverseU)
 -> A True
 -> A False
 -> (n : Bool)
 -> A n
Bool-induction A aT aF True = aT
Bool-induction A aT aF False = aF

-- type Bool formulated using binary sum and One type
2T : Type Universe0
2T = One + One

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
a +N b     = ?

_*N_ : Nat -> Nat -> Nat
a *N b     = ?

_^N_ : Nat -> Nat -> Nat
a ^N b       = ?

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
 -> P ZeroN
 -> ((n : Nat) -> P n -> P (Succ n))
 -> (n : Nat) -> P n
Nat-induction P s t = h
  where
     h : (k : Nat) -> P k
     h 0        = s
     h (Succ n) = t n (h n)

{-
Recurson principle is induction principle specialized to the clase
where P(n) = A
-}
Nat-recursion : (A : Type UniverseU)
 -> A
 -> (Nat -> A -> A)
 -> Nat -> A
Nat-recursion X = Nat-induction (\ _ -> X)

Nat-iteration : (A : Type UniverseU)
 -> A
 -> (A -> A)
 -> Nat -> A
Nat-iteration A x f = Nat-recursion A x (\ _ x -> f x)

infixr 20 _+_
