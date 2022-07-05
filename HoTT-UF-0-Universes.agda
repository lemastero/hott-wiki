{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-0-Universes where

open import Agda.Primitive public
 renaming (  Level to Universe
          ; lzero to Univ0
          ; lsuc to UNext     -- next universe
          ; _⊔_ to _umax_     -- Least upper bound of two universes, e.g. Univ1 ⊔ Univ0 is Univ1
          )

Type = \ u -> Set u

Univ1 = UNext Univ0
Univ2 = UNext Univ1
Univ3 = UNext Univ2

-- declare variables (placeholder) for Universes
variable UnivU UnivV UnivW UnivX : Universe
