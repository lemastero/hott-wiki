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

data Id (X : Type UnivU) : X -> X -> Type UnivU where
  refl : (x : X) -> Id X x x

-- identity type with implicit parameter

_≡_ : {X : Type UnivU} ->  X -> X -> Type UnivU
x ≡ y = Id _ x y

-- to proove property of Id it is enough to prove the easy case - refl
J : (X : Type UnivU)
    ( A : ((x y : X)  -> x ≡ y -> Type UnivV) ) -- A is property of Id
 -> ((x : X) -> A x x (refl x))                     -- show that property holds for refl
                                     -- no iductive case
 -> (x y : X) (p : x ≡ y) -> A x y p                -- then it holds for evry member of Id x y
J X A f x x (refl x) = f x

-- H principle TODO what is purpose of it?
H : {X : Type UnivU}
    (x : X)                                        -- forall x
    ( B : ((y : X)   -> x ≡ y -> Type UnivV))  -- B is property of Id
 -> B x (refl x)                                   -- B holds for x and refl
 -> (y : X) (p : x ≡ y)                            -- then for every y equal to x
 -> B y p                                          -- then B holds
H x B b x (refl x) = b

-- J defined using H
J-using-H : (X : Type UnivU) (A : (x y : X) -> x ≡ y -> Type UnivV)
          -> ((x : X) -> A x x (refl x))
          -> (x y : X) (p : x ≡ y) -> A x y p
J-using-H X A f x = H x (A x) (f x)

Js-alignment : (X : Type UnivU) (A : (x y : X) -> x ≡ y -> Type UnivV)
               (f : (x : X) -> A x x (refl x)) (x y : X) (p : x ≡ y)
            -> J X A f x y p ≡ J-using-H X A f x y p
Js-alignment X A f x x (refl x) = refl (f x)


-- Identity type is congruence relation
-- Conor McBride =$=
-- PLFA transport along Id (cong)
transport : { X : Type UnivU }
   (A : X -> Type UnivV)   -- B is property
   {x y : X}                   -- forall s,t
   -> x ≡ y                    -- if they are equal
   -> A x                      -- B holds for s
   -> A y                      -- then B holds for t
transport A (refl s) u = id (A s) u

transport-using-J : {X : Type UnivU} (A : X -> Type UnivV) {x y : X}
 -> x ≡ y
 -> A x
 -> A y
transport-using-J {UnivU} {UnivV} {X} A {x} {y} =
  J X (\x y _ -> A x -> A y) (\x -> id (A x)) x y

-- TODO non dependent J ???

-- ≡-recursion is non dependent version of ≡-induction (J)
nondep-H : {X : Type UnivU} (x : X) (A : X -> Type UnivV)
 -> A x
 -> (y : X)
 -> x ≡ y
 -> A y
nondep-H x A = H x (\ y _ -> A y)

transportH : {X : Type UnivU} (A : X -> Type UnivV) {x y : X}
  -> x ≡ y
  -> A x
  -> A y
transportH A {x} {y} p a = nondep-H x A a y p

-- transportH coincide transportJ conicide transport
transports-agreement1 : {X : Type UnivU} (A : X -> Type UnivV) {x y : X} (p : x ≡ y)
  -> (transportH A p ≡ transport A p)
transports-agreement1 A (refl x) =
 refl (transport A (refl x))

transports-agreement2 : {X : Type UnivU} (A : X -> Type UnivV) {x y : X} (p : x ≡ y)
  -> (transport-using-J A p ≡ transport A p)
transports-agreement2 A (refl x) = refl (transport A (refl x))

lhs : { X : Type UnivU} {x y : X} -> x ≡ y -> X
lhs {U} {X} {x} {y} p = x

rhs : { X : Type UnivU} {x y : X} -> x ≡ y -> X
rhs {U} {X} {x} {y} p = y

-- composition of identity types
_≡-compose_ : {X : Type UnivU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
x=y ≡-compose y=z = transport (lhs x=y ≡_) y=z x=y -- TODO how this work ?

_≡-compose''_ : {X : Type UnivU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
_≡-compose''_ {x} {y} {z} (refl .z) (refl z) = refl z

-- Utilities for writing proofs

-- ≡ associativity
_=[_>=_ : {X : Type UnivU}(x : X){y z : X} -> (x ≡ y) -> (y ≡ z) -> (x ≡ z)
-- x =[ refl x >= x==z = x==z
x =[ x=y >= y=z = x=y ≡-compose y=z

-- ≡ reflexivity
_[QED] : {X : Type UnivU}(x : X) -> x ≡ x
x [QED] = refl x

infixr 2 _=[_>=_
infix 3 _[QED]

-- ≡ commutativity
≡-swap : {X : Type UnivU} {x y : X} -> x ≡ y -> y ≡ x
≡-swap p = transport (_≡ lhs p) p (refl (lhs p) )

-- Id-compose using transport
_≡-compose'_ : {X : Type UnivU} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
x=y ≡-compose' y=z = transport ( _≡ rhs y=z ) (≡-swap x=y) y=z

compose-agreement : {X : Type UnivU} {x y z : X} (p : x ≡ y) (q : y ≡ z)
                  -> p ≡-compose'' q ≡ p ≡-compose q
compose-agreement (refl _) (refl _) = refl (refl _)

-- refl is neutral element of ≡-compose

-- p ≡-compose (refl y) ≡ p
≡-compose-right-nel : {X : Type UnivU} {x y : X} (p : x ≡ y)
      -> p ≡-compose (refl y) ≡ p
≡-compose-right-nel x=y = (refl x=y)

-- (refl y) ≡-compose' q ≡ q
≡-compose'-left-nel : {X : Type UnivU} {y z : X} (q : y ≡ z)
      -> (refl y) ≡-compose' q ≡ q
≡-compose'-left-nel y=z = refl y=z

-- Exercise

≡-compose-left-nel : {X : Type UnivU} {x y : X} (p : x ≡ y)
                   -> (refl x) ≡-compose p ≡ p
≡-compose-left-nel (refl _) = refl _

{-
≡-compose'-right-nel : {X : Type UnivU} {x y : X} (p : x ≡ y)
      -> p ≡-compose' (refl y) ≡ p
≡-compose'-right-nel x=y = {!   !}  -- TODO WIP
-}

-- cong
ap : {X : Type UnivU} {Y : Type UnivV} (f : X -> Y) {x y : X} -> (x ≡ y) -> f x ≡ f y
ap f {x} {y} p = transport (\ - -> f x ≡ f -) p (refl (f x))

-- different proof
ap' : {X : Type UnivU} {Y : Type UnivV} (f : X -> Y) {x y : X} -> (x ≡ y) -> f x ≡ f y
ap' f (refl _) = refl _

-- pointwise equality of functions
_∼_ : {X : Type UnivU} {A : X → Type UnivV } -> Π A -> Π A -> Type (UnivU umax UnivV)
f ∼ g = ∀ x -> f x ≡ g x


infix   0 Id
infix   0 _≡_
