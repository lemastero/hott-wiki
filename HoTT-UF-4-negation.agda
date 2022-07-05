{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-4-negation where

open import HoTT-UF-3-Identity-Types public

-- negation (defined in part 1)
not' : Type UnivU -> Type UnivU
not' A = A -> Zero

-- double negation
not-not : Type UnivU -> Type UnivU
not-not A = not (not A) -- (A -> 0) -> 0

-- tripple negation
not-not-not : Type UnivU -> Type UnivU
not-not-not A = not (not-not A)

-- double negation introduction
-- A => ¬¬A
not-not-intro : (A : Type UnivU) -> A -> not-not A
-- A => (A => 0) => 0
-- a    absurdA
not-not-intro A a absurdA = absurdA a


-- global-choice : (A : Type UnivU) -> not-not A -> A
--                 (A => 0) => 0
-- global-choice A f = {!   !}

-- logic-choice : not-not 2T -> 2T
--             (Bool => 0) => 0
-- logic-choice f = {!   !}


-- if we have function A->B and B is empty so we have (B -> 0)
-- then A is empty
contrapositive : {A : Type UnivU} {B : Type UnivV}
                 -> (A -> B)
                 -> (not B -> not A)
contrapositive f b->0 a = b->0 (f a)

-- absurdity of absurdity of absurdity is absurdity (1) LR
not-not-not-A-imply-A : (A : Type UnivU)
                        -> not (not (not A))
                        -> not A
not-not-not-A-imply-A A nnna = contrapositive (not-not-intro A) nnna -- not (not A) -> A
{-}
not-not-not-A-imply-A A nnna = contrapositive
           (not-not-intro A) -- f: A -> not not A (B = A and A = not not A)
           nnna              -- not A
-}

-- logical equivalence
_<=>_ : Type UnivU -> Type UnivV -> Type (UnivU umax UnivV)
X <=> Y = (X -> Y) * (Y -> X)

lr-implication : {X : Type UnivU} {Y : Type UnivV} -> X <=> Y -> (X -> Y)
lr-implication (x->y , y->x) = x->y -- I don't have * defined using sigma

rl-implication : {X : Type UnivU} {Y : Type UnivV} -> (X <=> Y) -> (Y -> X)
rl-implication (x->y , y->x) = y->x

-- absurdity of absurdity of absurdity is absurdity (2) <=>
absurdity^3-is-absurdity : {A : Type UnivU}
                           -> not (not (not A)) <=> not A
absurdity^3-is-absurdity {U} {X} =
  ( firstly , secondly )
  where
   firstly : not (not (not X)) -> not X
   firstly = not-not-not-A-imply-A X
   secondly : not X -> not (not (not X))
   secondly = not-not-intro (not X) -- A = not X

_≡/_ : {X : Type UnivU} -> X -> X -> Type UnivU
X ≡/ Y = not (X ≡ Y)

-- swap
≡/-sym : {A : Type UnivU} {x y : A} -> x ≡/ y -> y ≡/ x
≡/-sym  {U} {A} {x} {y} x-no≡-y = \ y≡x -> x-no≡-y (≡-swap (y≡x)) -- (y ≡ x) -> Zero

Id->Fun : {X Y : Type UnivU} -> X ≡ Y -> X -> Y
Id->Fun (refl X) = id X

Id->Fun' : {X Y : Type UnivU} -> X ≡ Y -> X -> Y
Id->Fun' {U} = transport (id (Type U) )
-- XXX how this works?

Id->Fun-agree : {X Y : Type UnivU} (p : X ≡ Y)
                -> Id->Fun p ≡ Id->Fun' p
Id->Fun-agree (refl X) = refl (id X)

One-is-not-Zero : One ≡/ Zero
One-is-not-Zero 1=0 = Id->Fun' 1=0 <>

One'-is-not-Zero' : One' ≡/ Zero'
One'-is-not-Zero' p = One-is-not-Zero q
  where
    f : 2T -> (Type Univ0)
    f Zero' = Zero
    f One' = One
    q : One ≡ Zero
    q = ap f p


decidable : Type UnivU -> Type UnivU
decidable A = A + (not A)

has-decidable-equality : Type UnivU -> Type UnivU
has-decidable-equality X = (x y : X) -> decidable (x ≡ y)

2T-has-decidable-equality : has-decidable-equality 2T
2T-has-decidable-equality Zero' Zero' = Left (refl Zero')
2T-has-decidable-equality Zero' One' = Right (≡/-sym One'-is-not-Zero')
2T-has-decidable-equality One' Zero' = Right One'-is-not-Zero'
2T-has-decidable-equality One' One' = Left (refl One')

not-zero-is-one : (n : 2T) -> n ≡/ Zero' -> n ≡ One'
not-zero-is-one Zero' f = absurd (Zero' ≡ One') (f (refl Zero'))
not-zero-is-one One' f = refl One'

left-right-disjoint-images : {X : Type UnivU} {Y : Type UnivV} {x : X} {y : Y} -> Left x ≡/ Right y
left-right-disjoint-images {U} {V} {X} {Y} {x} {y} p = One-is-not-Zero q
  where
  f : X + Y -> Type Univ0
  f (Left x) = One
  f (Right x) = Zero
  q : One ≡ Zero
  q = ap f p

right-fails-gives-left-holds : {P : Type UnivU} {Q : Type UnivV} -> (P + Q) -> not Q -> P
right-fails-gives-left-holds (Left p) u = p
right-fails-gives-left-holds (Right q) u = absurd _ (u q)
