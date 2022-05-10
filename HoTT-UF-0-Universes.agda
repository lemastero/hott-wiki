{-# OPTIONS --without-K --exact-split --safe #-}

-- no unicode, smaller version of
-- https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/blob/master/agda/Universes.agda
-- see https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html

module HoTT-UF-0-Universes where

open import Agda.Primitive public
 renaming (  Level to Universe
          ; lzero to Universe0
          ; lsuc to UNext       -- next universe
          ; _⊔_ to _umax_       -- Least upper bound of two universes, e.g. Universe1 ⊔ Universe0 is Universe1
          )

Type = \ u -> Set u

{-
we cannot assume that given universe is in intself to avoid Russell's Paradox


HoTT-UF M. Escardo https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universes
HoTT Book https://homotopytypetheory.org/book/ A.2.3
-}
Universe1 = UNext Universe0
Universe2 = UNext Universe1
Universe3 = UNext Universe2

variable UniverseU UniverseV UniverseW UniverseX : Universe
