module cs410one where

{-
put ? and C-c C-l make goal
c-c c-l  typecheck
c-c c-,  show context
C-c C-.  show context + what you typed in hole
c-c c-c  case split
c-c c-r  constructor
c-c c-a  auto - first thing that have right type
c-c c-SPACE provide
C-c c-n normalize (give value to expression)

-- Ctrl-c Ctrl-S solve
-- Ctrol-c Ctrl-x
-}

{-
----------------------------------
-- propositions as types

types                theorems
values of the type   proofs of theorem
Zero                 false
One                  true
_+_                  exclusive or
_*_                  and
->                   implication

proof : proofs of hypothesis -> proof of conclusion

----------------------------------
-- 0 1 product coproduct types

-- ct: initial object
-- constructive logic: false
-- FP void
data Zero : Set where

-- logic: true
-- category theory: terminal object
-- FP: Unit
record One : Set where
  constructor <>

data Two : Set where
  ff : Two
  tt : Two

  -- Either[S,T]
  -- logic: and
  -- category theory: coproduct
data _+_ (S : Set)(T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

ZeroL-+ : {A : Set} -> A + Zero -> A
ZeroL-+ (inl a) = a

ZeroR-+ : {A : Set} -> Zero + A -> A
ZeroR-+ (inr a) = a

comm-+ : {A B : Set} -> A + B -> B + A
comm-+ (inl a) = inr a
comm-+ (inr b) = inl b

assocLR-+ : {A B C : Set} -> (A + B) + C -> A + (B + C)
assocLR-+ (inl (inl a)) = inl a
assocLR-+ (inl (inr b)) = inr (inl b)
assocLR-+ (inr c) = inr (inr c)

assocRL-+ : {A B C : Set} -> A + (B + C) -> (A + B) + C
assocRL-+ (inl a) = inl (inl a)
assocRL-+ (inr (inl b)) = inl (inr b)
assocRL-+ (inr (inr c)) = inr c

record _*_ (S : Set)(T : Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T

OneL-* : {A : Set} -> A * One -> A
OneL-* (fst , snd) = fst

OneR-* : {A : Set} -> One * A -> A
OneR-* (fst , snd) = snd

-- proof of commutativity but also usefull function that swaps pair
comm-* : {A : Set}{B : Set} -> A * B -> B * A
comm-* record { fst = a ; snd = b } = record { fst = b ; snd = a }

assocLR-* : {A B C : Set} -> (A * B) * C -> A * (B * C)
assocLR-* record { fst = record { fst = a ;
                                  snd = b} ;
                   snd = c } = record {
                      fst = a ;
                      snd = record { fst = b ; snd = c } }

assocRL-* : {A B C : Set} -> A * (B * C) -> (A * B) * C
assocRL-* record {
  fst = a ;
  snd = record {
    fst = b ;
    snd = c } } = record {
                    fst = record {
                      fst = a ;
                      snd = b } ;
                    snd = c }

-- unique arrow to any other type
-- FP: absurt | void
naughtE : {A : Set} -> Zero -> A
naughtE ()  -- impossible pattern

-- we have 2 functions that transforms both elems of pair so we can transform
-- at the seme time
-- infix operator used for 3 args (last could be ommited in HoF)
_$*_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
(f $* g) (a , b) = f a , g b

_$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
(f $+ g) (inl a) = inl (f a)
(f $+ g) (inr b) = inr (g b)

-- dependent function application
_$_ : forall {S : Set}{T : S -> Set}(f : (x : S) -> T x)(s : S) -> T s
f $ s = f s
infixl 2 _$_

-- compose
_<<_ : forall {X Y Z : Set} -> (Y -> Z) -> (X -> Y) -> (X -> Z)
(f << g) x = f (g x)

-- andThen
_>>_ : forall {X Y Z : Set} -> (X -> Y) -> (Y -> Z) -> (X -> Z)
(f >> g) x = g (f x)

{- ###############   SKI combinators   ############### -}

-- constant function
-- you can make value of type A depend on E
-- pure for applicative functor reading from E
combinatorK : forall {A E : Set} -> A -> (E -> A)
combinatorK = \ a e -> a

-- if you have a function depending on E and argument depending on E
-- you can do application depending on E
-- ap for applicative functor reading from E
combinatorS : forall {S T E : Set} -> (E -> (S -> T)) -> (E -> S) -> E -> T
combinatorS = \ est es e -> (est e) (es e)

-- Haskell works
-- let s = \ es e -> est (es e)
-- let k = \ a e -> a
-- let i = s k k
-- :t i

-- Haskell breaks if you put in file
-- module Foo where
-- foo = show . read

-- second arg is not used so we need to put any concrete type like One
-- first arg we say I know you can figure this out
-- combinatorI
combinatorI : forall {X : Set} -> X -> X
combinatorI = combinatorS combinatorK (combinatorK {_} {Zero} )

id : forall {X : Set} -> X -> X
id = combinatorI

{- ###############   Natural numbers   ###############

-----------
zero : Nat

 n : Nat
--------------
 suc n : Nat

-}

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

{- induction on Nat

P  is a property of natural number

-------
P zero


P n
---------
P (suc n)

-}


{- equality on natural numbers, defined inductively using +

n : Nat
-------------
zero + n == n

m,n,p : Nat   m + n == p
------------------------
(suc m) + n == suc p

-}

data Bool : Set where
  #f #t : Bool        -- Scheme 4 life

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE #t #-}
{-# BUILTIN FALSE #f #-}

-- TODO classical logic
-- TODO define A and B
-- TODO define A or B
-- TODO define A impl B
-- TODO define A <=> B
-- TODO define nand nor xor not
-- TODO define tautologies

_=N_ : Nat -> Nat -> Bool
zero =N zero   = #t
suc n =N suc m = n =N m
_ =N _ = #f

{-# BUILTIN NATEQUALS _=N_ #-}

{-

n : N
------------
0 + n = n

m,n,p : N
-------------------------
(suc m) + n = suc (m + n)

-}

_+N_ : Nat -> Nat -> Nat
0 +N n     = n
suc m +N n = suc (m +N n)

infixl 6 _+N_

{-# BUILTIN NATPLUS _+N_ #-}

{-

n : N
-----------
0 * n = 0

m,n,p : N
-------------------------
(suc n) * m = m + (n * m)

-}

_*N_ : Nat -> Nat -> Nat
0 *N y     = 0
suc x *N y = y +N (x *N y)

infixl 7 _*N_

{-# BUILTIN NATTIMES _*N_ #-}

{-

n : N
-----------
n ^ 0 = 1

m,n : N
--------------------------
n ^ (suc m) = n * (n ^ m)

-}

_^N_ : Nat -> Nat -> Nat
m ^N 0       = 1
m ^N (suc n) = m *N (m ^N n)

infixl 8 _^N_

example-+N-2-3 : Nat
example-+N-2-3 = 2 +N 3

example-*N-2-2 : Nat
example-*N-2-2 = 2 *N 3

_-N_ : Nat -> Nat -> Nat
m -N zero = m
zero -N suc n = zero
suc m -N suc n = m -N n

{-# BUILTIN NATMINUS _-N_ #-}

{- ###############   EQUALITY   ############### -}

-- we want to show evidence that tow things are equal
data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x -- relation that is only reflexive

infix 4 _==_

{-# BUILTIN EQUALITY _==_ #-}

test-+N-2-3-eq-5 : 2 +N 3 == 5
test-+N-2-3-eq-5  = refl 5

test-*N-2-3-eq-6 : 2 *N 3 == 6
test-*N-2-3-eq-6 = refl 6

test-3-monus-2-is-1 : 3 -N 2 == 1
test-3-monus-2-is-1 = refl 1

-- dependent functions application
-- if we have equal functions and equal arguments
-- then applications are equal
_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
         f == f' -> x == x' -> f x == f' x'
refl f =$= refl x = refl (f x)
infixl 2 _=$=_

-- congruence of ==
-- relation is congurence for a function if it is preserved
-- after applying that function
cong : {X Y : Set}(f : X -> Y){x y : X} -> (x == y) -> f x == f y
cong f (refl _) = refl _

sym : {X : Set}{x y : X} -> x == y -> y == x
sym (refl x) = refl x

[Proof]_ : forall {X : Set}{x y : X} -> (x == y) -> (x == y)
[Proof]_ x=y = x=y

_=[]_ : forall {X : Set}(x {y} : X) -> (x == y) -> (x == y)
x =[] x=y = x=y

_[QED] : forall {X : Set}(x : X) -> x == x
x [QED] = refl x

-- == associativity
_=[_>=_ : forall {X : Set}(x : X){y z : X} -> (x == y) -> (y == z) -> (x == z)
x =[ refl x >= x==z = x==z

-- Yoneda embedding C(B,A) iso forall x: c(a,x)-> c(b,x)
-- for equality idirect equality a == b <=> forall c: (a <= c) -> (b <= c)
_=<_]=_ : forall {X : Set}(x : X){y z : X} -> (y == x) -> (y == z) -> (x == z)
x =< refl x ]= x==z = x==z

infix 1 [Proof]_
infixr 2 _=[_>=_ _=<_]=_ _=[]_
infix 3 _[QED]

---------------------------
-- Properties of + on Nat

test2-plus-3 : (2 +N 3) == 5
test2-plus-3 = [Proof]
  2 +N 3 =[]
  suc (1 +N 3) =[]
  suc (suc (0 +N 3)) =[]
  suc (suc 3) =[] suc 4 =[] 5
  [QED]

+left-identity : forall (n : Nat) -> (0 +N n) == n
+left-identity = refl

+right-identity : forall (n : Nat) -> (n +N 0) == n
+right-identity zero = refl 0
+right-identity (suc n) = (refl suc) =$= (+right-identity n) -- refl (suc (+right-identity n))


{-
associativity of +
(x + y) + z == x + (y + z)

We proove by induction on x (for any x assuming y and z are fixed).

--------------------------
(0 + y) + z == 0 + (y + z)


(x + y) + z == x + (y + z)
--------------------------
(suc x + y) + z == suc x + (y + z)
-}
assocLR-+N-v : forall (x y z : Nat) -> ((x +N y) +N z) == (x +N (y +N z))
assocLR-+N-v zero y z = [Proof]
  (0 +N y) +N z =[]
  (y +N z) =[]
  (0 +N (y +N z))
  [QED]
assocLR-+N-v (suc x) y z = [Proof]
  ((suc x) +N y) +N z =[]
  suc (x +N y) +N z =[]
  suc ((x +N y) +N z) =[ cong suc (assocLR-+N-v x y z) >=
  suc (x +N (y +N z)) =[]
  (suc x +N (y +N z)) [QED]

assocLR-+N : (x y z : Nat) -> ((x +N y) +N z) == (x +N (y +N z))
assocLR-+N zero y z = refl (y +N z)
assocLR-+N (suc x) y z
           rewrite assocLR-+N x y z = refl (suc (x +N (y +N z)))
-- assocLR-+N (suc x) y z = refl suc =$= assocLR-+N x y z

assocRL-+N : (x y z : Nat) -> (x +N (y +N z)) == ((x +N y) +N z)
assocRL-+N zero y z  = refl (y +N z)
assocRL-+N (suc x) y z
           rewrite assocRL-+N x y z = refl (suc ((x +N y) +N z))

-- lemma
+N-suc-n : (m n : Nat) -> (m +N (suc n)) == (suc (m +N n))
+N-suc-n zero n = refl (suc n)
+N-suc-n (suc m) n
         rewrite +N-suc-n m n = refl (suc (suc (m +N n)))

-- lemma
+N-x-suc-x-is-suc : (n m : Nat) -> (n +N suc m) == (suc (n +N m))
+N-x-suc-x-is-suc zero m = refl (suc m)
+N-x-suc-x-is-suc (suc n) m
                  rewrite +N-x-suc-x-is-suc n m = refl (suc (suc (n +N m)))

-- commutativity +
comm-+N : (x y : Nat) -> (x +N y) == (y +N x)
comm-+N zero zero = refl zero
comm-+N zero (suc y) rewrite +right-identity y = (refl suc) =$= (refl y)
comm-+N (suc x) zero = refl suc =$= +right-identity x
comm-+N (suc x) (suc y)
        rewrite +N-suc-n x y
        rewrite +N-x-suc-x-is-suc y x
        rewrite comm-+N x y
        = refl (suc (suc (y +N x)))

one-*N : (n : Nat) -> (1 *N n) == n
one-*N zero = refl 0
one-*N (suc n) = refl suc =$= +right-identity n

*N-one : (n : Nat) -> (n *N 1) == n
*N-one zero = refl 0
*N-one (suc n) = refl suc =$= *N-one n

*N-zero : (n : Nat) -> (n *N 0) == 0
*N-zero zero = refl 0
*N-zero (suc n-times-0) rewrite *N-zero n-times-0 = refl 0

zero-*N : (n : Nat) -> (0 *N n) == 0
zero-*N n = refl 0

-- lemma n * (m + 1) = n * m + n
n-*N-suc-m-==-suc-n-*N-m : (n m : Nat) -> ((n *N (suc m)) == ((n *N m) +N n))
n-*N-suc-m-==-suc-n-*N-m zero m = refl 0
n-*N-suc-m-==-suc-n-*N-m (suc n) m
                         rewrite +N-suc-n (m +N (n *N m)) n
                         rewrite n-*N-suc-m-==-suc-n-*N-m n m
                         rewrite assocLR-+N m (n *N m) n
   = refl (suc (m +N ((n *N m) +N n)))

-- * commutativity
-- (x * y) = (y * x)
comm-*N : (x y : Nat) -> (x *N y) == (y *N x)
comm-*N zero y rewrite *N-zero y = refl 0
comm-*N (suc x) y
        rewrite n-*N-suc-m-==-suc-n-*N-m y x
        rewrite comm-+N y (x *N y)
        rewrite comm-*N x y
       = refl ((y *N x) +N y)

-- * distribute over + from left
-- (x + y) * z == (x * z ) + (y * z)
distr-left-*+N : (x y z : Nat) -> ((x +N y) *N z) == ((x *N z) +N (y *N z))
distr-left-*+N zero y z = refl (y *N z)
distr-left-*+N (suc x) y z
            rewrite distr-left-*+N x y z
            rewrite assocRL-+N z (x *N z) (y *N z)
            = refl ((z +N (x *N z)) +N (y *N z))

-- * distribute over + from right
-- x * (y + z) == (x * y) + (x * z)
distr-right-*+N : (x y z : Nat) -> (x *N (y +N z)) == ((x *N y) +N (x *N z))
distr-right-*+N zero y z = refl zero
distr-right-*+N (suc x) y z
            rewrite distr-right-*+N x y z
            rewrite assocRL-+N (y +N z) (x *N y) (x *N z)
            rewrite assocRL-+N (y +N (x *N y)) z (x *N z)
            rewrite assocLR-+N y (x *N y) z
            rewrite comm-+N (x *N y) z
            rewrite assocLR-+N y z (x *N y)
            = refl ((y +N (z +N (x *N y))) +N (x *N z))

assocLR-*N : (x y z : Nat) -> ((x *N y) *N z) == (x *N (y *N z))
assocLR-*N zero y z = refl 0
assocLR-*N (suc x) y z
           rewrite distr-left-*+N x y z
           rewrite distr-left-*+N y (x *N y) z
           rewrite assocLR-*N x y z
           = refl ((y *N z) +N (x *N (y *N z)))

assocRL-*N : (x y z : Nat) -> (x *N (y *N z)) == ((x *N y) *N z)
assocRL-*N zero y z = refl 0
assocRL-*N (suc x) y z
           rewrite distr-left-*+N y (x *N y) z
           rewrite assocRL-*N x y z
           = refl ((y *N z) +N ((x *N y) *N z))

test-3+4+5-assoc : ((3 +N 4) +N 5) == (3 +N (4 +N 5))
test-3+4+5-assoc = refl 12

-- TODO min

_max_ : Nat -> Nat -> Nat
zero max y = y
suc x max zero = suc x
suc x max suc y = suc (x max y)

-- TODO define 0 max monoid laws id,

_>=_ : Nat -> Nat -> Set
x >= zero = One
zero >= suc y = Zero
suc x >= suc y = x >= y

egzample-4>=2 : 4 >= 2
egzample-4>=2 = <>

egzample-5>=5 : 5 >= 5
egzample-5>=5 = <>

refl->= : (n : Nat) -> n >= n
refl->= zero = <>
refl->= (suc n) = refl->= n

trans->= : (x y z : Nat) -> x >= y -> y >= z -> x >= z
trans->= x y zero x>=y y>=z = <>
trans->= (suc x) (suc y) (suc z) x>=y y>=z = trans->= x y z x>=y y>=z

_<=_ : Nat -> Nat -> Set
zero <= z = One
suc x <= zero = Zero
suc x <= suc y = x <= y

refl-<= : (n : Nat) -> n <= n
refl-<= zero = <>
refl-<= (suc x) = refl-<= x

trans-<= : (x y z : Nat) -> x <= y -> y <= z -> x <= z
trans-<= zero y z x<=y y<=z = <>
trans-<= (suc x) (suc y) (suc z) x<=y y<=z = trans-<= x y z x<=y y<=z

egzample-2<=3 : 2 <= 3
egzample-2<=3 = <>

egzample-5<=5 : 5 <= 5
egzample-5<=5 = <>

-- sigma
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst

-- product
_*'_ : (S : Set)(T : Set) -> Set
S *' T = Sg S \ _ -> T

-- TODO write proof you can get from one to another def
product-from-sigma-is-product : {S T : Set} -> (S * T) -> (S *' T)
product-from-sigma-is-product (S , T) = record { fst = S ; snd = T }

product-is-product-from-sigma : {S T : Set} -> (S *' T) -> (S * T)
product-is-product-from-sigma (S , T) = record { fst = S ; snd = T }

-- TODO use identity type for product equivalence

difference : (m n : Nat) -> m >= n -> Sg Nat \ d -> m == (n +N d)
difference m zero p = m , refl m
difference zero (suc n) ()
difference (suc m) (suc n) p with difference m n p
difference (suc .(n +N d)) (suc n) p | d , refl .(n +N d) = d , refl (suc n +N d)
-- difference (suc m) (suc n) p | d , q rewrite q = d , refl (suc n +N d)
-- difference (suc m) (suc n) p | d , q = d , (refl suc =$= q)

-- TODO how to define division ?


tryMe      = difference 42 37
dontTryMe  = difference 37 42


-- some classic logic tautologies do not work
-- Excluded Middle
-- excluded-middle : {B : Set} -> B + (B -> Zero)
-- excluded-middle = ?
-- de-morgan : {A B : Set} -> ((A * B) -> Zero) -> (A -> Zero) + (B -> Zero)
-- de-morgan nab = ?

-- TODO would this hold when we use Bool for logic ?


{- ###############   Vectors   ############### -}


data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)

infixr 4 _,-_

vTake : (m n : Nat) -> m >= n -> {X : Set} -> Vec X m -> Vec X n
vTake m zero m>=n xs = []
vTake (suc m) (suc n) m>=n (x ,- xs) = x ,- vTake m n m>=n xs

vTakeIdFact : (n : Nat){X : Set}(xs : Vec X n) ->
              vTake n n (refl->= n) xs == xs
vTakeIdFact = {!   !}

vTakeCpFact : (m n p : Nat)(m>=n : m >= n)(n>=p : n >= p)
              {X : Set}(xs : Vec X m) ->
              vTake m p (trans->= m n p m>=n n>=p) xs ==
              vTake n p n>=p (vTake m n m>=n xs)
vTakeCpFact = {!   !}

vHead : {X : Set}{n : Nat} -> Vec X (suc n) -> X
vHead {n} (x ,- xs) = x

vTail : {X : Set}{n : Nat} -> Vec X (suc n) -> Vec X n
vTail (x ,- xs) = xs

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

-- Space Monads talk

vec : forall {n X} -> X -> Vec X n
vec {zero} x = []
vec {suc n} x = x ,- vec {n} x

_<*>_ : forall {n X Y} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
[] <*> ys = []
(f ,- fs) <*> (x ,- xs) = f x ,- (fs <*> xs)

Rect : Set
Rect = Nat * Nat -- width , height

Matrix : Set -> (Rect -> Set)
Matrix X (w , h) = Vec (Vec X w) h

-- TODO continue Space Monads talk

vChop : {X : Set}{m : Nat}{n : Nat} -> Vec X (m +N n) -> Vec X m  * Vec X n
vChop {m = 0} xs = [] , xs
vChop {X} {m = suc m1} {n} (x ,- xs) = {!    !}
  --where
  --  vChopIter = vChop {X} {m1} {n} xs
  --  vChopIter = a , b



vMap : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vMap f [] = []
vMap f (x ,- xs) = (f x) ,- vMap f xs


-- TODO vMapIdFact

-- TODO lecture 5
-- TODO lecture 6

postulate
  -- use when we want to proov that two functions are equal
  -- refl works only when they have the same implementation
  extensionality : {S : Set}{T : S -> Set}
    (f g : (x : S) -> T x) ->
    ((x : S) -> f x == g x) ->
    f == g

imp : {S : Set}{T : S -> Set}(f : (x : S) -> T x){x : S} -> T x
imp f {x} = f x

-- extensionality when functions take implicit arguments
extensionality-impl : {S : Set}{T : S -> Set}
                  {f g : {x : S} -> T x} ->
                  ((x : S) -> f {x} == g {x}) ->
                  _==_ {forall {x : S} -> T x} f g
extensionality-impl {f = f} {g = g} q =
   (refl imp) =$=
   extensionality (\ x -> f {x}) (\ x -> g {x}) q

_=$impl=_ : {S : Set}{T : S -> Set}
             {f g : {x : S} -> T x} ->
             _==_ {forall {x : S} -> T x} f g ->
             (x : S) -> f {x} == g {x}
refl f =$impl= x = refl (f {x})

infixl 2 _=$impl=_

{- ###############   Category   ############### -}

-- example railways and train stations
record Category : Set where
  field
    -- types
    Obj : Set                -- objects
    _~>_ : Obj -> Obj -> Set -- homeObj morphisms between source and target

    -- operations
    id~> : {T : Obj} -> T ~> T                                 -- identity
    _>~>_ : {R S T : Obj} -> (R ~> S) -> (S ~> T) -> (R ~> T)  -- composition
    -- diagramatic composition (like Scala andThen)

    -- laws
    law-id~>>~> : {S T : Obj} (f : S ~> T) -> (id~> >~> f) == f
    law->~>id~> : {S T : Obj} (f : S ~> T) -> (f >~> id~>) == f
    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) ->
                    ((f >~> g) >~> h) == (f >~> (g >~> h))

  infixr 3 _>~>_

    -- TODO 10 -24:18 assocn

-- category of sets and functions
SET : Category
SET = record
  { Obj = Set
  ; _~>_ = \ S T -> S -> T
  ; id~> = id
  ; _>~>_ = _>>_
  ; law-id~>>~> = \ f -> refl f
  ; law->~>id~> = \ f -> refl f
  ; law->~>>~> = \ f g h -> refl (\ x -> h (g (f x)))
  }


unique-ge-proofs : (m n : Nat)(p q : m >= n) -> p == q
unique-ge-proofs m zero p q = refl <>
unique-ge-proofs (suc m) (suc n) p q = unique-ge-proofs m n p q

-- category
-- objects: natural numbers
-- morphism exists if n >= m (so there is 0 or 1)
-- in general any preorder will do TODO express that
NAT->= : Category
NAT->= = record
  { Obj = Nat
  ; _~>_ = _>=_
  ; id~> = \ {n} -> refl->= n
  ; _>~>_ = \ {m}{n}{p} m>=n n>=p -> trans->= m n p m>=n n>=p
  ; law-id~>>~> = \ {s} {t} f -> unique-ge-proofs s t (trans->= s s t (refl->= s) f) f
  ; law->~>id~> = \ {s} {t} f -> unique-ge-proofs s t (trans->= s t t f (refl->= t)) f
  ; law->~>>~> = \ {Q R S T} f g h ->
                      unique-ge-proofs Q T
                      (trans->= Q S T (trans->= Q R S f g) h)
                      (trans->= Q R T f (trans->= R S T g h))
  }


-- category
-- objects: natural numbers
-- morphism exists if n >= m
NAT-<= : Category
NAT-<= = record
  { Obj = Nat
  ; _~>_ = _<=_
  ; id~> = \ {n} -> refl-<= n
  ; _>~>_ = \ {n m p} n<=m m<=p -> trans-<= n m p n<=m m<=p
  ; law-id~>>~> = \ {s} {t} f -> unique s t (trans-<= s s t (refl-<= s) f) f
  ; law->~>id~> = \ {s} {t} f -> unique s t (trans-<= s t t f (refl-<= t)) f
  ; law->~>>~> = \ {Q R S T} f g h ->
                      unique Q T
                      (trans-<= Q S T (trans-<= Q R S f g) h)
                      (trans-<= Q R T f (trans-<= R S T g h))
  } where
  unique : (m n : Nat)(p q : m <= n) -> p == q
  unique zero n p q = refl <>
  unique (suc m) (suc n) p q = unique m n p q

-- MONOID as Category
-- single object
-- morphisms are the values
-- TODO express this in general case not Nat
ONE-Nat : Category
ONE-Nat = record
  { Obj = One
  ; _~>_ = \ _ _ -> Nat
  ; id~> = 0
  ; _>~>_ = _+N_
  ; law-id~>>~> = +left-identity
  ; law->~>id~> = +right-identity
  ; law->~>>~> = assocLR-+N
  }

ONE-Nat* : Category
ONE-Nat* = record
  { Obj = One
  ; _~>_ = \ _ _ -> Nat
  ; id~> = 1
  ; _>~>_ = _*N_
  ; law-id~>>~> = one-*N
  ; law->~>id~> = *N-one
  ; law->~>>~> = assocLR-*N
  }

-- TODO this is cheating required to define discreate category
unique-equality-proofs : {X : Set}{x y : X}(p q : x == y) -> p == q
unique-equality-proofs (refl x) (refl .x) = refl (refl x)

-- discreate category
DISCRETE : (X : Set) -> Category
DISCRETE X = record {
  Obj = X ;
  _~>_ = _==_ ;
  id~> = \ {x} -> refl x ;
  _>~>_ = \ { (refl x) (refl .x) -> refl x } ; -- pattern matchin inside lambda
  law-id~>>~> = \ {s} {t} f ->  unique-equality-proofs _ f ;
  law->~>id~> = \ {s} {t} f -> unique-equality-proofs _ f ;
  law->~>>~> = \ {q} {r} {s} {t} f g h -> unique-equality-proofs _ _ }

{- ###############   Functor   ############### -}

module FUNCTOR where
  open Category
  record _=>_ (C D : Category) : Set where
    field
      F-Obj : Obj C -> Obj D
      F-map : {S T : Obj C} -> _~>_ C S T -> _~>_ D (F-Obj S) (F-Obj T)
      -- laws
      F-map-id~> : {T : Obj C} -> F-map (id~> C {T}) == id~> D {F-Obj T}
      F-map->~> : {R S T : Obj C}(f : _~>_ C R S)(g : _~>_ C S T) ->
                    F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)

open FUNCTOR public

-- TODO remove this postulate vmap and use vMap
postulate vmap : {n : Nat}{S T : Set} -> (S -> T) -> Vec S n -> Vec T n

hw : {A : Set} -> A
hw {A} = {!   !}

VEC : Nat -> SET => SET
VEC n = record {
  F-Obj = \ X -> Vec X n ;
  F-map = vmap ;
  F-map-id~> = extensionality _ _ \ x -> {!    !} ; -- TODO hw
  F-map->~> = {!    !} } -- TODO hw

VTAKE : Set -> NAT->= => SET
VTAKE X = record { F-Obj = Vec X -- Nat -> Set
                 ; F-map = \ {m} {n} m>=n xs -> vTake m n m>=n xs
                 ; F-map-id~> = \ {n} -> extensionality _ _ (vTakeIdFact n)
                 ; F-map->~> = \ {m}{n}{p} m>=n n>=p -> extensionality _ _ (vTakeCpFact m n p m>=n n>=p)
                 }

{- TODO there is no C+C C+H to create helper function -}

ADD : Nat -> NAT->= => NAT->=
ADD d = record
         { F-Obj = d +N_ -- operator section
         ; F-map = \{m}{n} -> help d m n
         ; F-map-id~> = \ {n} -> unique-ge-proofs (d +N n) (d +N n) _ _
         ; F-map->~> = \ {m}{n}{p} x y -> unique-ge-proofs (d +N m) (d +N p) _ _
         } where
         help : forall d m n -> m >= n -> (d +N m) >= (d +N n)
         help zero m n m>=n = m>=n
         help (suc d) m n m>=n = help d m n m>=n

-- Category of categories
CATEGORY : Category
CATEGORY = record
  { Obj = Category
  ; _~>_ = _=>_
  ; id~> = record
    { F-Obj = id
    ; F-map = id
    ; F-map-id~> = refl _
    ; F-map->~> = \ f g -> refl _
    }
  ; _>~>_ = \ {R}{S}{T} F G -> record
                            { F-Obj = F-Obj F >> F-Obj G
                            ; F-map = F-map F >> F-map G
                            ; F-map-id~> = F-map G (F-map F (Category.id~> R))
                                             =[ refl (F-map G) =$= F-map-id~> F >=
                                           F-map G (Category.id~> S)
                                             =[ F-map-id~> G >=
                                           Category.id~> T
                                            [QED]
                            ; F-map->~> = {!   !}
                            }
  ; law-id~>>~> = {!   !}
  ; law->~>id~> = {!   !}
  ; law->~>>~> = {!   !}
  } where open _=>_

-- category where objects are Functors

-- lecture 9

data Maybe (X : Set) : Set where
  yes : (x : X) -> Maybe X
  no : Maybe X

map-maybe : {S T : Set} -> (S -> T) -> Maybe S -> Maybe T
map-maybe f (yes x) = yes (f x)
map-maybe f no = no

-- Maybe Functor
MAYBE : SET => SET
MAYBE = record { F-Obj = Maybe
               ; F-map = map-maybe
               ; F-map-id~> = extensionality _ _ \ {
                   (yes x) → refl (yes x) ;
                   no → refl no }
               ; F-map->~> = \ f g -> extensionality _ _ \ { (yes x) -> refl (yes (g (f x)))
                                                           ; no -> refl no }
               }

module MAYBE-CAT where
  open Category SET
  open _=>_ MAYBE

  joinMaybe : {T : Set} -> Maybe (Maybe T) -> Maybe T
  joinMaybe (yes x) = x
  joinMaybe no = no

  MAYBE-CAT : Category
  MAYBE-CAT = record
    { Obj = Set
    ; _~>_ = \ X Y -> X -> Maybe Y
    ; id~> = yes
    ; _>~>_ = \ f g -> f >> ( F-map g >> joinMaybe )
    ; law-id~>>~> = \ f -> refl f
    ; law->~>id~> = \ f -> extensionality _ _ \ x -> help-id f x
    ; law->~>>~> = \ f g h -> extensionality _ _ \ x -> help-compose f g h x
    } where
    help-id : forall {S T} (f : S -> Maybe T) (x : S) ->
      joinMaybe (map-maybe yes (f x)) == f x
    help-id f x with f x
    help-id f x | yes t = refl (yes t)
    help-id f x | no = refl no
    help-compose : forall {Q R S T}
      (f : Q -> Maybe R) (g : R -> Maybe S) (h : S -> Maybe T)
      (x : Q) ->
      joinMaybe (map-maybe h (joinMaybe (map-maybe g (f x)))) ==
      joinMaybe (map-maybe (\ y -> joinMaybe (map-maybe h (g y))) (f x))
    help-compose f g h x with f x
    help-compose f g h x | yes y = refl (joinMaybe (map-maybe h (g y)))
    help-compose f g h x | no = refl no


open MAYBE-CAT

-- TODO
-- https://github.com/pigworker/CS410-17/blob/master/lectures/Lec4.agda#L77

-- TODO 21:36 List LIST Video 09

-- TODO
-- data BitProcess (X ; Set) : Set where
--  stop : (x : X) -> BitProcess X
--  send : (b : Two)(k : BitProcess x) ->

-- identity functor
ID : {C : Category} -> C => C
ID = record
     { F-Obj = id
     ; F-map = id
     ; F-map-id~> = refl _
     ; F-map->~> = \ f g -> refl _
     }
-- ID : SET => SET
-- ID = id~> where open Category CATEGORY

-- composition of functors (composition of actions on objects and arrows)
-- TODO did I miss some infixl infixr ?

module FUNCTOR-CP {C D E : Category} where
 open _=>_
 open Category

 _>=>_ : C => D -> D => E -> C => E

 F-Obj (F >=> G) = F-Obj F >> F-Obj G
 F-map (F >=> G) = F-map F >> F-map G

 F-map-id~> (F >=> G) =
   F-map G (F-map F (id~> C))
     =[ refl (F-map G) =$= F-map-id~> F >=
   F-map G (id~> D)
     =[ F-map-id~> G >=
  id~> E
     [QED]

{-
 F-map->~> (F >=> G) f g =
  F-map G (F-map F (_>~>_ C f g))
    =[ refl (F-map G) =$= F-map->~> F f g >=
  F-map G (_>~>_ D (F-map F f) (F-map F g))
    =[ F-map->~> G (F-map F f) (F-map F g) >=
  _>~>_ E (F-map G 9F-map F f)) (F-map G 9F-map F g))
    [QED]
-}

-- _>F>_ : (SET => SET) -> (SET => SET) -> (SET => SET)
-- F >F> G = F >~> G where open Category CATEGORY

open FUNCTOR-CP public

{-
module NATURAL-TRANSFORMATION {C D : Category} where
  open Category
  open _=>_

  record _~~>_ (F G : C => D) : Set where
    field
      -- operation
      xf : {X : Obj C} -> _~>_ D (F-Obj F X) (F-Obj G X)
      -- law
      naturality : {X Y : Obj C}(f : _~>_ C X Y} ->
                   _>~>_ D (F-map F f) (xf {Y})
                   ==
                   _>~>_ D (xf {X}) (F-map G f)
-}
