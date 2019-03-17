module Operators where

open import Prelude

_⟨_ : Nat → Nat → Bool
_     ⟨ zero  = false
zero  ⟨ suc _ = true
suc n ⟨ suc m = n ⟨ m

_≣_ : Nat → Nat → Bool
zero  ≣ zero  = true
suc n ≣ suc m = n ≣ m
_     ≣ _     = false

_<=_ : Nat → Nat → Bool
_<=_ a b = (a ⟨ b) || (a ≣ b)
