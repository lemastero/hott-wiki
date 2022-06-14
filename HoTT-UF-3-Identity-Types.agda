{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-3-Identity-Types where

open import HoTT-UF-2-Dependent-Types public

-- TODO there is no meaning to True False (they have meaning bc you assinged it) but there is one for 1 an 0
-- TODO comment from chat
-- for all x y(x) => a(x, y(x) )
-- there exists x such that y(x) => a(x, y(x))

{-
type theory: identity type (identification, equality)
homotopy theory:
-}

data Id (X : Type UniverseU) : X -> X -> Type UniverseU where
  refl : (x : X) -> Id X x x

-- identity type with implicit parameter

_≡_ : {X : Type UniverseU} ->  X -> X -> Type UniverseU
x ≡ y = Id _ x y

-- to proove property of Id it is enough to prove the easy case - refl
J : (X : Type UniverseU)
    ( A : ((x y : X)  -> x ≡ y -> Type UniverseV) ) -- A is property of Id
 -> ((x : X) -> A x x (refl x))                     -- show that property holds for refl
 -> (x y : X) (p : x ≡ y) -> A x y p                -- then it holds for evry member of Id x y
J X A f x x (refl x) = f x
-- J X A f x y (refl x) = ?   TODO do it

H : {X : Type UniverseU}
    (x : X)                                        -- forall x
    ( B : ((y : X)   -> x ≡ y -> Type UniverseV))  -- B is property of Id
 -> B x (refl x)                                   -- B holds for x and refl
 -> (y : X) (p : x ≡ y)                            -- then for every y equal to x
 -> B y p                                          -- then B holds
H x B b x (refl x) = b

-- J defined using H
J-using-H : (X : Type UniverseU) (A : (x y : X) -> x ≡ y -> Type UniverseV)
          -> ((x : X) -> A x x (refl x))
          -> (x y : X) (p : x ≡ y) -> A x y p
J-using-H X A f x = H x (A x) (f x)

Js-alignment : (X : Type UniverseU) (A : (x y : X) -> x ≡ y -> Type UniverseV)
               (f : (x : X) -> A x x (refl x)) (x y : X) (p : x ≡ y)
            -> J X A f x y p ≡ J-using-H X A f x y p
Js-alignment X A f x x (refl x) = refl (f x)
-- Js-alignment X A f x y x=y = {!   !} -- TODO do it

-- transport along Id (cong)
transport : { X : Type UniverseU }
   (A : X -> Type UniverseV) -- B is property
   {x y : X}                    -- forall s,t
   -> x ≡ y                    -- if they are equal
   -> A x                      -- B holds for s
   -> A y                      -- then B holds for t
transport A (refl s) u = id (A s) u

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
lhs : { X : Type UniverseU} {x y : X} -> x ≡ y -> X
lhs {U} {X} {x} {y} p = x

rhs : { X : Type UniverseU} {x y : X} -> x ≡ y -> X
rhs {U} {X} {x} {y} p = y

_≡-compose_ : {X : Type UniverseU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
x=y ≡-compose y=z = transport (lhs x=y ≡_) y=z x=y

-- TODO Exeercise different definition
_≡-compose''_ : {X : Type UniverseU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
_≡-compose''_ {x} {y} {z} x=y y=z = {!   !}

-- Utilities for writing proofs

-- ≡ associativity
_=[_>=_ : {X : Type UniverseU}(x : X){y z : X} -> (x ≡ y) -> (y ≡ z) -> (x ≡ z)
-- x =[ refl x >= x==z = x==z
x =[ x=y >= y=z = x=y ≡-compose y=z

-- ≡ reflexivity
_[QED] : {X : Type UniverseU}(x : X) -> x ≡ x
x [QED] = refl x

infixr 2 _=[_>=_
infix 3 _[QED]

-- ≡ commutativity
Id-inverse : {X : Type UniverseU} {x y : X} -> x ≡ y -> y ≡ x
Id-inverse p = transport (_≡ lhs p) p (refl (lhs p) )

-- Id-compose using transport
_≡-compose'_ : {X : Type UniverseU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
x=y ≡-compose' y=z = transport ( _≡ rhs y=z ) (Id-inverse x=y) y=z

compose-agreement : {X : Type UniverseU} {x y z : X} (p : x ≡ y) (q : y ≡ z)
                  -> p ≡-compose'' q ≡ p ≡-compose q
compose-agreement (refl _) (refl _) = refl (refl _)

-- refl is neutral element of ≡-compose

-- p ≡-compose (refl y) ≡ p
≡-compose-right-nel : {X : Type UniverseU} {x y : X} (p : x ≡ y)
      -> p ≡-compose (refl y) ≡ p
≡-compose-right-nel x=y = (refl x=y)

-- (refl y) ≡-compose' q ≡ q
≡-compose'-left-nel : {X : Type UniverseU} {y z : X} (q : y ≡ z)
      -> (refl y) ≡-compose' q ≡ q
≡-compose'-left-nel y=z = refl y=z

-- Exercise

≡-compose-left-nel : {X : Type UniverseU} {x y : X} (p : x ≡ y)
                   -> (refl x) ≡-compose p ≡ p
≡-compose-left-nel (refl _) = refl _

≡-compose'-right-nel : {X : Type UniverseU} {x y : X} (p : x ≡ y)
      -> p ≡-compose' (refl y) ≡ p
≡-compose'-right-nel x=y = {!   !}  -- TODO WIP

-- cong
ap : {X : Type UniverseU} {Y : Type UniverseV} (f : X -> Y) {x y : X} -> (x ≡ y) -> f x ≡ f y
ap f {x} {y} p = transport (\ - -> f x ≡ f -) p (refl (f x))

-- different proof
ap' : {X : Type UniverseU} {Y : Type UniverseV} (f : X -> Y) {x y : X} -> (x ≡ y) -> f x ≡ f y
ap' f (refl _) = refl _

-- pointwise equality of functions
_∼_ : {X : Type UniverseU} {A : X → Type UniverseV } -> Π A -> Π A -> Type (UniverseU umax UniverseV)
f ∼ g = ∀ x -> f x ≡ g x


{- Exercise x <= y  <=>  Σ z : Nat , x + z == y
----------------------------------------------- -}

open Arithmetic public

cong : {X Y : Set}(f : X -> Y){x y : X} -> (x ≡ y) -> f x ≡ f y
cong f (refl _) = refl _

+left-identity : forall (n : Nat) -> (0 +N n) ≡ n
+left-identity zero = refl 0
+left-identity (succ n) = cong succ (+left-identity n)

exerciseLeIffExistDifference1 : (x y : Nat) -> (x <= y) -> -Σ Nat \ d -> (x +N d) ≡ y
exerciseLeIffExistDifference1 x y x<=y = {!   !} -- TODO WIP

exerciseLeIffExistDifference2 : (x y : Nat) -> (-Σ Nat \ d -> (x +N d) ≡ y) -> (x <= y)
exerciseLeIffExistDifference2 x y sg = {!   !} -- TODO WIP

-- TODO WIP review exercise MGS 2022
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

infix   0 Id
infix   0 _≡_
