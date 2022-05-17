{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-0-Universes where

open import Agda.Primitive public
 renaming (  Level to Universe
          ; lzero to Universe0
          ; lsuc to UNext       -- next universe
          ; _⊔_ to _umax_       -- Least upper bound of two universes, e.g. Universe1 ⊔ Universe0 is Universe1
          )

Type = \ u -> Set u

{- Type universes

Usages of universes:
- define properties of elements X as families of types indexed by a this type X -> U
- define mathematical structures: monoids, groups, topological spaces, categories

We cannot assume that given universe is in intself U : U to avoid Russell's Paradox.
If we do we would have losse soundness - could proove every type
even empty type is inhabitad.
We need hierarchy of universes U0, U1, .... defined by UNext

Each universe is contained in the next

G ctx
----------------- U-Intro
G |- U : UNext U

Universes are cummulative -
any type A in U is also in Unext U

G |- A : U
----------------- U-Cumul
G |- A : UNext U

If groups lives in one universe then type of groups live in bigger universe
Given category in one universe the presheaf category lives in larger universe

U0 is a type in U1
U1 is a type in U2

We have 2 operations on universes:
- successor (UNext)
- least upper bound (umax)

Resources:
 HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universes
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/blob/master/agda/Universes.agda
 HoTT Book https://homotopytypetheory.org/book/ A.2.3
-}
Universe1 = UNext Universe0
Universe2 = UNext Universe1
Universe3 = UNext Universe2

-- declare variables (placeholder) for Universes
variable UniverseU UniverseV UniverseW UniverseX : Universe
