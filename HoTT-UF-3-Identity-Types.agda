{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-3-Identity-Types where

open import HoTT-UF-2-Dependent-Types public

{-
type theory: identity type (identification, equality)
homotopy theory:
set theory:

structure of identity type

rules for equality

A type    A ≡ B    A ≡ B   B ≡ C
------   ------   ---------------
A ≡ A     B ≡ A       A ≡ C

this is not simple type (0,1,2,N) or type depending on parameter like +
rarther it is type family
for given type X we have function Id X : X -> X -> UniverseU
for any fixed element x : X type
Sigma y : Y, Id X x y is always a sigleton (has 1 element namely refl)

-}

data Id (X : Type UniverseU) : X -> X -> Type UniverseU where
  refl : (x : X) -> Id X x x

-- identity type with implicit parameter

_≡_ : {X : Type UniverseU} ->  X -> X -> Type UniverseU
x ≡ y = Id _ x y

-- pointwise equality of functions
_∼_ : {X : Type UniverseU} {A : X → Type UniverseV } -> Π A -> Π A -> Type (UniverseU umax UniverseV)
f ∼ g = ∀ x → f x ≡ g x

-- exercise MGS 2022
-- ap : {X : Type UniverseU} {Y : Type UniverseV} {x1 x2 : X} -> (f : X -> Y) -> (x1 ≡ x2) -> (f x1) ≡ (f x2)
-- ap = {!   !}

-- ex1 : {X : Type UniverseU} {x1 x2 : X} -> ap (id X) ~ id (x1 ≡ x2)
-- ex1 = ?

-- ex2 : {X : Type UniverseU {Y : UniverseV} {Z : UniverseW} (f : X -> Y) (g : Y -> Z) {x x1 ; X} (p : x ≡ x1)
--  -> ap (g . f) p ≡ (ap g . ap f) p
-- ex2 {U V W X Y Z} f g {x} {.x} (refl .x) = refl (refl (g (f x)))

-- with explicit arguemts
-- app : {X : Type UniverseU} {Y : Type UniverseV} {x1 x2 : X} -> (f : X -> Y) -> (x1 ≡ x2) -> (f x1) ≡ (f x2)
-- app = {!   !}

-- is-singl : Type UniverseU -> Type UniverseU
-- is-singl X = Σ x : X , ((y : X) -> x ≡ y)

-- singl : {X : Type UniverseU} -> X -> Type UniverseU
-- singl {U} {X} x = Σ b: A , a ≡ b

-- ex3 : {X : Type Universe U} (x : X) -> is-singl ( singl x )
-- ex3 x = (x , (refl x)), ?

{-
Identity types In some Quillen model

for some types like N we can proove that Id has at most 1 inhavitant
if we assume axiom K then for all types have at most 1 inhavitant of type Id so all types are sets
if we do not assume axiom K we work in universe where
types that have at most 1 inabitant of Id are 1-groupoids
types that have at most 2 inhabitants of Id type are 2-groupoids (esp type of Id of 1-groupoid)
...
univalence gives example of types where Id have more that 1 inhabitant

= is definitional equality
≡ judgemental equality (or identification type), can be more than 1
HoTT swaps this
-}

-- identity-induction principle
-- ≡-induction
-- is related to Yoneda lemma in category theory that says that
-- certain natural transformations are uniquely determined by their action on the identity arrows,
-- even if they are defined for all arrows

-- J states that all identifications between any 2 points is defined by action on reflexive identifications
J : (X : Type UniverseU) (A : (x y : X) -> x ≡ y -> Type UniverseV )
 -> ((x : X) -> A x x (refl x))
 -> (x y : X) (p : x ≡ y) -> A x y p
J X A f x x (refl x) = f x

H : {X : Type UniverseU} (x : X) (B : (y : X) -> x ≡ y -> (Type UniverseV))
 -> B x (refl x)
 -> (y : X) (p : x ≡ y)
 -> B y p
H x B b x (refl x) = b

-- transport along Id
transport : {A : Type UniverseU} (B : A -> Type UniverseV) {s t : A}
 -> s ≡ t -- p
 -> B s
 -> B t
transport B (refl s) u = id (B s) u

transport-using-J : {X : Type UniverseU} (A : X -> Type UniverseV) {x y : X}
 -> x ≡ y
 -> A x
 -> A y
transport-using-J {UniverseU} {UniverseV} {X} A {x} {y} =
  J X (\x y _ -> A x -> A y) (\x -> id (A x)) x y

-- ≡-recursion is non dependent version of ≡-induction (J)
nondep-H : {X : Type UniverseU} (x : X) (A : X -> Type UniverseV)
 -> A x
 -> (y : X)
 -> x ≡ y
 -> A y
nondep-H x A = H x (\ y _ -> A y)

transportH : {X : Type UniverseU} (A : X -> Type UniverseV) {x y : X}
  -> x ≡ y
  -> A x
  -> A y
transportH A {x} {y} p a = nondep-H x A a y p

-- transportH coincide transportJ conicide transport
transports-agreement1 : {X : Type UniverseU} (A : X -> Type UniverseV) {x y : X} (p : x ≡ y)
  -> (transportH A p ≡ transport A p)
transports-agreement1 A (refl x) =
 refl (transport A (refl x))

transports-agreement2 : {X : Type UniverseU} (A : X -> Type UniverseV) {x y : X} (p : x ≡ y)
  -> (transport-using-J A p ≡ transport A p)
transports-agreement2 A (refl x) = refl (transport A (refl x))

-- composition of identity types
lhs : { X : Type UniverseU} {x  y : X} -> x ≡ y -> X
lhs {UniverseU} {X} {x} {y} p = x

_≡-compose_ : {X : Type UniverseU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
p ≡-compose q = transport (lhs p ≡_) q p

-- TODO

decidable : Type UniverseU -> Type UniverseU
decidable A = A + (not A)

has-decidable-equality : Type UniverseU -> Type UniverseU
has-decidable-equality X = (x y : X) -> decidable (x ≡ y)

-- Bool-has-decidable-equality : has-decidable-equality Bool
-- Bool-has-decidable-equality = {!   !}

---------------------------------- TODO
-- video 2 Identity types 1:01:59
-- conor video 4 beginning https://www.youtube.com/watch?v=OZeDRtRmgkw

-- -2-groupoids
-- Contractible types
-- other names: singleton type
-- type is contractible if there is designated c : X
-- that is identified with each x : X
is-singleton : Type UniverseU -> Type UniverseU
is-singleton X = Σ c ꞉ X , ((x : X) -> c ≡ x)

is--2-groupoid : Type UniverseU -> Type UniverseU
is--2-groupoid = is-singleton

-- element c : X is center of contraction

is-center : (X : Type UniverseU) -> X -> Type UniverseU
is-center X c = (x : X) -> c ≡ x

-- 1 is singleton, every type is singleton if it is equivalent to 1
Unit-is-contractible : is-singleton One
Unit-is-contractible = <> , One-induction (\x -> <> ≡ x) (refl <>)

-- -1-groupoids
-- subsingletons (propositions, truth values)
-- type is subsingleton if it has at most 1 element (any 2 of its elements are equal or identified)
-- PI(x y : A) x ≡A y
-- in topology type there is continous selection of map between x and y or is empty
is-subsingleton : Type UniverseU -> Type UniverseU
is-subsingleton X = (x y : X) -> x ≡ y

Void-is-subsingleton : is-subsingleton Zero
Void-is-subsingleton x y = absurd (x ≡ y) x

is--1-groupoid : Type UniverseU -> Type UniverseU
is--1-groupoid = is-subsingleton

is-proposition : Type UniverseU -> Type UniverseU
is-proposition = is-subsingleton

is-truth-value : Type UniverseU -> Type UniverseU
is-truth-value = is-subsingleton

-- type is set if there is at most 1 way for any two of its elements to be equal
-- 0-groupoids
is-set : Type UniverseU -> Type UniverseU
is-set X = (x y : X) -> is-subsingleton (x ≡ y)

-- Univalent Excluded Middle
Univalent-EM : forall UniverseU -> Type (UNext UniverseU)
Univalent-EM U = (X : Type U) -> is-subsingleton X -> X + (not X)

{-
homotopy levels
-2 : contractible space (exactly 1 point up to paths)
-1 : propositions (has at most 1 point up to paths)
 0 : sets (space whos path space is propositions)
 1 : groupoids (space whose path space is set)
 ...

propositions -> logic encoded as homotopy theory (via Curry-Howards)
sets -> ZFC axioms ?, membership ?, powerset, subset, intersection, ...
groupoids -> categories (?)

structure vs property

example groups:
- all groups are space
- group is space

Group := Sigma(G:UniverseU,unit:G,multiply:GxG->G)(inverse:G->G).isGroup(G,unit,multi,inverse)
isGroup(G,unit, multi,inverse) :=
 (Pi(x,y,z:G).m(m(x,y),z) =G m(x,m(y,z)) ) x
 (Pi(x:G).m(x,e)=x * m(e,x)=x * m(x,i(x))=e * m(i(x),x) =e)

this is wrong from type theory point of view !

there is 2 ways to proove ((x*y)*z)*t = x*((y*z)*t)
we have unintended extra structure
this matter in category theory

so we can:
- quotient
- we might say some stuff land in propositions or sets

insist that G is a set (0-type)
Group := Sigma(G:0-Type, ....

other examples:
* algebraic structures: ring, modules, the carrier type should be a set
* category

C0 : U space of objects
C1 : C0 x C0 -> 0-Type  morphisms
if we do not say 0-Type we will have problem on isomorphisms
0-Typ := Sigma (X:U). isSet(X)
-}

infix   0 Id
infix   0 _≡_
