{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-2-Dependent-Types where

open import HoTT-UF-1-Types public

{-
type theory: dependent sum type (Sigma)
logic: designated existance (we know which element fulfills condition)
programming: dependen product
homotopy theory: total space
-}

record Σ {X : Type UniverseU} (Y : X -> Type UniverseV) : Type (UniverseU umax UniverseV) where
  constructor
    _,_
  field
    x : X
    y : Y x

infixr 50 _,_

fst : {X : Type UniverseU} {Y : X -> Type UniverseV} -> Σ Y -> X
fst (x , y) = x

snd : {X : Type UniverseU} {Y : X -> Type UniverseV} -> (z : Σ Y) -> Y (fst z)
snd (x , y) = y

-- TODO how to remove this and just use sigma
-- unfortunately we use some unicode that I do not understand how this works

-Σ : (X : Type UniverseU) (Y : X -> Type UniverseV) -> Type (UniverseU umax UniverseV)
-Σ X Y = Σ Y

syntax -Σ X (\ x -> y) = Σ x ꞉ X , y

-- for property A and all z : Σ y proove that A z is enough to prove we have A(x,y) for x:X and y:Y x
-- called also: uncurry, Σ-elimination
Σ-induction : {X : Type UniverseU} {Y : X -> Type UniverseV} {P : Σ Y -> Type UniverseW}
 -> ((x : X) (y : Y x) -> P (x , y))
 -> ((x , y) : Σ Y) -> P (x , y)
Σ-induction f (x , y) = f x y

uncurry : {X : Type UniverseU} {Y : X -> Type UniverseV} {P : Σ Y -> Type UniverseW}
 -> ((x : X) -> (y : Y x) -> P (x , y)) -- f: x -> y -> g (x y)
 -> ((x , y) : Σ Y)                     -- (x, y)
 -> P (x , y)
uncurry f (x , y) = f x y

-- inverse of Σ-induction

curry : {X : Type UniverseU} {Y : X -> Type UniverseV} {A : Σ Y -> Type UniverseW}
 -> (((x , y) : Σ Y) -> A (x , y))
 -> ((x : X) (y : Y x) -> A (x , y))
curry f x y = f (x , y)

_×_ : Type UniverseU -> Type UniverseV -> Type (UniverseU umax UniverseV)
X × Y = Σ x ꞉ X , Y

infixr 30 _×_

{-
type theory: dependent product type Pi(x: X),A(x)
logic: universal quantifier
programming: dependen function
homotopy theory: space of sections
-}

Π : {X : Type UniverseU} (A : X -> Type UniverseV) -> Type (UniverseU umax UniverseV)
Π {UniverseU} {UniverseV} {X} A = (x : X) -> A x

-- identity function
id : (X : Type UniverseU) -> X -> X
id X x = x

-- dependent function composition (Y -> Z) -> (X -> Y) -> (X -> Z)
-- if Z y holds for all y: Y then for any given f: X -> Y we have that Z (f x) holds for all x: X
_compose_ : {X : Type UniverseU} {Y : Type UniverseV} {Z : Y -> Type UniverseW}
  -> ((y : Y) -> Z y)
  -> (f : X -> Y)
  -> (x : X) -> Z (f x)
g compose f = \x -> g (f x)

-- TODO can I compose two dependent types and have "forgetfull" transformation: forall x. x y -> y
-- TODO can I compose two dependent types and have ... TODO

domain : {X : Type UniverseU} {Y : Type UniverseV} -> (X -> Y) -> Type UniverseU
domain {U} {V} {X} {Y} f = X

codomain : {X : Type UniverseU} {Y : Type UniverseV} -> (X -> Y) -> (Type UniverseV)
codomain {U} {V} {X} {Y} f = Y

type-of : {X : Type UniverseU} -> X -> (Type UniverseU)
type-of {U} {X} x = X
