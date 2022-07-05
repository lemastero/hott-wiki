{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-2-Dependent-Types where

open import HoTT-UF-1-Types public

{-
type theory: dependent sum type (Sigma)
logic: designated existance (we know which element fulfills condition)
programming: dependen product
homotopy theory: total space
-}

record Σ {X : Type UnivU} (Y : X -> Type UnivV) : Type (UnivU umax UnivV) where
  constructor
    _,_
  field
    x : X
    y : Y x

infixr 50 _,_

fst : {X : Type UnivU} {Y : X -> Type UnivV} -> Σ Y -> X
fst (x , y) = x

snd : {X : Type UnivU} {Y : X -> Type UnivV} -> (z : Σ Y) -> Y (fst z)
snd (x , y) = y

-- TODO how to remove this and just use sigma
-- unfortunately we use some unicode that I do not understand how this works

-Σ : (X : Type UnivU) (Y : X -> Type UnivV) -> Type (UnivU umax UnivV)
-Σ X Y = Σ Y

syntax -Σ X (\ x -> y) = Σ x ꞉ X , y

-- for property A and all z : Σ y proove that A z is enough to prove we have A(x,y) for x:X and y:Y x
-- called also: uncurry, Σ-elimination
Σ-induction : {X : Type UnivU} {Y : X -> Type UnivV} {P : Σ Y -> Type UnivW}
 -> ((x : X) (y : Y x) -> P (x , y))
 -> ((x , y) : Σ Y) -> P (x , y)
Σ-induction f (x , y) = f x y

uncurry : {X : Type UnivU} {Y : X -> Type UnivV} {P : Σ Y -> Type UnivW}
 -> ((x : X) -> (y : Y x) -> P (x , y)) -- f: x -> y -> g (x y)
 -> ((x , y) : Σ Y)                     -- (x, y)
 -> P (x , y)
uncurry f (x , y) = f x y

-- inverse of Σ-induction

curry : {X : Type UnivU} {Y : X -> Type UnivV} {A : Σ Y -> Type UnivW}
 -> (((x , y) : Σ Y) -> A (x , y))
 -> ((x : X) (y : Y x) -> A (x , y))
curry f x y = f (x , y)

_×_ : Type UnivU -> Type UnivV -> Type (UnivU umax UnivV)
X × Y = Σ x ꞉ X , Y

infixr 30 _×_

{-
type theory: dependent product type Pi(x: X),A(x)
logic: universal quantifier
programming: dependen function
homotopy theory: space of sections
-}

Π : {X : Type UnivU} (A : X -> Type UnivV) -> Type (UnivU umax UnivV)
Π {UnivU} {UnivV} {X} A = (x : X) -> A x

-- identity function
id : (X : Type UnivU) -> X -> X
id X x = x

id' : {X : Type UnivU} -> X -> X
id' x = x

-- dependent function composition (Y -> Z) -> (X -> Y) -> (X -> Z)
-- if Z y holds for all y: Y then for any given f: X -> Y we have that Z (f x) holds for all x: X
_compose_ : {X : Type UnivU} {Y : Type UnivV} {Z : Y -> Type UnivW}
  -> ((y : Y) -> Z y)
  -> (f : X -> Y)
  -> (x : X) -> Z (f x)
g compose f = \x -> g (f x)

-- TODO can I compose two dependent types and have "forgetfull" transformation: forall x. x y -> y
-- TODO can I compose two dependent types and have ... TODO

domain : {X : Type UnivU} {Y : Type UnivV} -> (X -> Y) -> Type UnivU
domain {U} {V} {X} {Y} f = X

codomain : {X : Type UnivU} {Y : Type UnivV} -> (X -> Y) -> (Type UnivV)
codomain {U} {V} {X} {Y} f = Y

type-of : {X : Type UnivU} -> X -> (Type UnivU)
type-of {U} {X} x = X
