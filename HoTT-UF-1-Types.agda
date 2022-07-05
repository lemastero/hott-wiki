{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-1-Types where

open import HoTT-UF-0-Universes public

-- empty type / void / nothing / initial object
data Zero : Type Univ0 where

Zero-induction : (P : Zero -> Type UnivU)
                          -- no base case
                          -- no inductive case
 -> (x : Zero) -> P x     -- property P holds for all elements of type Zero
Zero-induction A ()

Zero-recursion : (A : Type UnivU) -> Zero -> A
Zero-recursion A a = Zero-induction (\ _ -> A) a

not : Type UnivU -> Type UnivU
not X = X -> Zero

is-empty : Type UnivU -> Type UnivU
is-empty = not -- type is empty == there is function to the empty type

absurd : (A : Type UnivU) -> Zero -> A
absurd = Zero-recursion

-- unit type / termina object
data One : Type Univ0 where
  <> : One

-- for any property P of type One, if P(<>) it holds for <>
-- then P(x) it holds for all x: One
One-induction : (P : One -> Type UnivU)
  -> P <>               -- base case
                        -- no inductive case
  -> (x : One) -> P x   -- property P holds for every element of One
One-induction P a <> = a

-- logic: P => (True -> P)
-- const[P](P)   : Unit => P
One-recursion : (P : Type UnivU) ->
  P ->
  (One -> P)
One-recursion P a x = One-induction (\ _ -> P) a x

-- unique function from any type to One
-- logic: A => True
unit : {A : Type UnivU} -> A -> One
unit x = <>

-- binary sum type / either / coproduct / disjoint union / or
data _+_ (X : Type UnivU) (Y : Type UnivV) : Type (UnivU umax UnivV) where
 Left : X -> X + Y
 Right : Y -> X + Y

infixr 20 _+_

+-induction : {X : Type UnivU} {Y : Type UnivV} (P : X + Y -> Type UnivW)
 -> ((x : X) -> P (Left  x))   -- base case Left (bracket for easier pattern matching)
 -> ((y : Y) -> P (Right y))   -- base case Right (bracket for easier pattern matching)
                               -- no inductive case
 -> (z : X + Y) -> P z         -- property P holds for all elements of X + Y
+-induction P f _ (Left x) = f x
+-induction P _ g (Right y) = g y

+-recursion : {X : Type UnivU} {Y : Type UnivV} (P : Type UnivW)
 -> (X -> P)
 -> (Y -> P)
 -> (X + Y) -> P
+-recursion P xp yp xy = +-induction
     (\ XY -> P) -- in +-induction P is dependent type so fake it
     xp yp xy    -- could skip those

+0-right-id : {A : Type UnivU} -> A + Zero -> A
+0-right-id (Left a) = a

+0-left-id : {A : Type UnivU} -> Zero + A -> A
+0-left-id (Right a) = a

comm-+ : {A B : Type UnivU} -> A + B -> B + A
comm-+ (Left a) = Right a
comm-+ (Right b) = Left b

assocLR-+ : {A B C : Type UnivU} -> (A + B) + C -> A + (B + C)
assocLR-+ (Left (Left a)) = Left a
assocLR-+ (Left (Right b)) = Right (Left b)
assocLR-+ (Right c) = Right (Right c)

assocRL-+ : {A B C : Type UnivU} -> A + (B + C) -> (A + B) + C
assocRL-+ (Left a) = Left (Left a)
assocRL-+ (Right (Left b)) = Left (Right b)
assocRL-+ (Right (Right c)) = Right c

-- binary product / pair / tuple
record _*_ (S : Type UnivU)(T : Type UnivV) : Type (UnivU umax UnivV)  where
  constructor _,_
  field
    fst : S
    snd : T

-- TODO * induction, recursion,

right-unit-One* : {A : Type UnivU} -> (A * One) -> A
right-unit-One* (a , _) = a

left-unit-One* : {A : Type UnivU} -> One * A -> A
left-unit-One* (_ , a) = a

comm-* : {A : Type UnivU}{B : Type UnivU} -> A * B -> B * A
comm-* (a , b) = (b , a)

assocLR-* : {A B C : Set} -> (A * B) * C -> A * (B * C)
assocLR-* ((a , b) , c) = (a , (b , c))

assocRL-* : {A B C : Type UnivU} -> A * (B * C) -> (A * B) * C
assocRL-* (a , (b , c)) = ((a , b) , c)

-- 2 elements type / booleans
data Bool : Type Univ0 where
  True : Bool
  False : Bool

-- intuition we can draw truth table
--        | b | P b |
--  true  |   |     |
--  false |   |     |
Bool-induction : (A : Bool -> Type UnivU)
 -> A True             -- base case True
 -> A False            -- base case False
 -> (b : Bool) -> A b  -- property P holds for all elements b
Bool-induction A aT aF True = aT
Bool-induction A aT aF False = aF

Bool-recursion : (A : Type UnivU)
 -> A
 -> (Bool -> A -> A)
 -> Bool -> A
Bool-recursion A a f b = f b a
-- Bool-recursion A a f b = a

-- two point type (Bool) defined using binary sum and One type
2T : Type Univ0
2T = One + One

pattern Zero' = Left <>
pattern One' = Right <>

2T-induction : (P : 2T -> Type UnivU)
 -> P Zero'
 -> P One'
 -> (n : 2T) -> P n
2T-induction P p0 p1 Zero' = p0
2T-induction P p0 p1 One' = p1

2T-induction' : (P : 2T -> Type UnivU)
 -> P Zero'
 -> P One'
 -> (n : 2T) -> P n
2T-induction' P p0 p1 = +-induction
  P
  (One-induction (\ x -> P (Left x))  p0 )
  (One-induction (\ y -> P (Right y)) p1 )

2T-recursion : (P : Type UnivU)
 -> P
 -> (2T -> P -> P)
 -> 2T -> P
2T-recursion P p f t2 = 2T-induction (\ 2t -> P) p (f t2 p) t2

-- TODO proove something about 2T-recurion is equiv to Bool-recursion ?

-- 3 element type
data Three : Type Univ0 where
  yes : Three
  perhaps : Three
  no : Three

-- TODO Three induction recursion

--type of natural numbers
data Nat : Type Univ0 where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

--Induction principle == Nat elimination rule
Nat-induction' : (P : Nat -> Type UnivU)
 -> P 0                               -- base case
 -> ((n : Nat) -> P n -> P (succ n))  -- inductive case
 -> (n : Nat) -> P n                  -- property P holds for all element of N
Nat-induction' P s t = h     -- TODO Q is this something special?
  where
     h : (k : Nat) -> P k
     h 0        = s
     h (succ n) = t n (h n)

Nat-induction : (P : Nat -> Type UnivU)
 -> P 0                               -- base case
 -> ((n : Nat) -> P n -> P (succ n))  -- inductive case
 -> (n : Nat) -> P n                  -- property P holds for all element of N
--Nat-induction P P0 f 0 = P0
Nat-induction P p0 fnp 0 = p0
Nat-induction P p0 fnp (succ n) = fnp n (Nat-induction P p0 fnp n)

--Recurson principle
Nat-recursion : (P : Type UnivU)
 -> P
 -> (Nat -> P -> P)
 -> Nat -> P
Nat-recursion P p0 fnp n = Nat-induction
  (\ m -> P) -- fake dependent type P that Nat-induction want
  p0 fnp n

Nat-iteration : (P : Type UnivU)
 -> P
 -> (P -> P)
 -> Nat -> P
Nat-iteration P p0 f n = Nat-recursion P p0 (\ _n p -> f p) n

module Arithmetic where
  _+N_ : Nat -> Nat -> Nat
  x +N 0 = x
  x +N succ y = succ (x +N y)

  _*N_ : Nat -> Nat -> Nat
  x *N 0 = 0
  x *N succ y = x +N (x *N y)

  _^N_ : Nat -> Nat -> Nat
  x ^N 0 = 1
  x ^N succ y = x *N (x ^N y)

module Arithmetic' where
  _+N_ : Nat -> Nat -> Nat
  x +N y = h x y
    where
      h : Nat -> Nat -> Nat
      h x y = Nat-iteration Nat x succ y

  _*N_ : Nat -> Nat -> Nat
  x *N y = h x y
     where
       h : Nat -> Nat -> Nat
       h x y = Nat-iteration Nat 0 (\z -> x +N z) y

  {-
  _^N_ : Nat -> Nat -> Nat
  x ^N y = h x y
    where
      h : Nat -> Nat -> Nat
      h x y = {!   !} -- TODO
  -}
_<=_ : Nat -> Nat -> Set
zero <= z = One
succ x <= zero = Zero
succ x <= succ y = x <= y
