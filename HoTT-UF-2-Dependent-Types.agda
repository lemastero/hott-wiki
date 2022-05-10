{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-2-Dependent-Types where

open import HoTT-UF-1-Types public

{-
type theory: dependent sum type (Sigma)
logic: designated existance (a bit different that logical existential quantifier)
programming: dependen product
homotopy theory: total space

formation rule:

x:A   B(x) type
----------------
Σ(x:A).B(x) type

introduction rule (?):

s:A  t: B(s)
------------------
(s,t): Σ(x:A).B(x)

elimination rules:

p: Σ(x:A).B(x)
--------------
pi1(p): A

p: Σ(x:A).B(x)
--------------
pi2(p): B(x)

equations:

pi1(s,t) ≡A s

pi2(s,t) ≡B(x) t

(pi2(p), pi2(p)) ≡Σ(x:A)B(x) t

HoTT Book https://homotopytypetheory.org/book/ A.2.5
HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmatypes
-}

record Σ {X : Type UniverseU} (Y : X -> Type UniverseV) : Type (UniverseU umax UniverseV) where
  constructor
    _,_
  field
    x : X
    y : Y x

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
Σ-induction : {X : Type UniverseU} {Y : X -> Type UniverseV} {A : Σ Y -> Type UniverseW}
 -> ((x : X) (y : Y x) -> A (x , y))
 -> ((x , y) : Σ Y)
 -> A (x , y)
Σ-induction g (x , y) = g x y

-- inverse of Σ-induction

curry : {X : Type UniverseU} {Y : X -> Type UniverseV} {A : Σ Y -> Type UniverseW}
 -> (((x , y) : Σ Y) -> A (x , y))
 -> ((x : X) (y : Y x) -> A (x , y))
curry f x y = f (x , y)

_×_ : Type UniverseU -> Type UniverseV -> Type (UniverseU umax UniverseV)
X × Y = Σ x ꞉ X , Y

{-
type theory: dependent product type Pi(x: X),A(x)
logic: universal quantifier
programming: dependen function
homotopy theory: space of sections

formation rule:

A type  x:A |- B(x) type
------------------------
 Π(x:A).B(x) type

formation rule:

x:A |- t(x):B(x)
-----------------------
\x:A.t(x) : Π(x:A).B(x)

elimination rule:

f:Π(x:A).B(x) t:A
------------------
f(t):B(t)

equations:


HoTT Book https://homotopytypetheory.org/book/ A.2.4
HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#pitypes
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

infixr 50 _,_
infixr 30 _×_
