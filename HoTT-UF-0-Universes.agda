{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-0-Universes where

open import Agda.Primitive public
 renaming (  Level to Universe
          ; lzero to Universe0
          ; lsuc to UNext     -- next universe
          ; _⊔_ to _umax_     -- Least upper bound of two universes, e.g. Universe1 ⊔ Universe0 is Universe1
          )

Type = \ u -> Set u

Universe1 = UNext Universe0
Universe2 = UNext Universe1
Universe3 = UNext Universe2

-- declare variables (placeholder) for Universes
variable UniverseU UniverseV UniverseW UniverseX : Universe
