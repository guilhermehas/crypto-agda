module blockchain where

open import Prelude

record Transaction : Set where
  field
    sender : Nat
    receiver : Nat
    amount : Nat

record SimpleBlock : Set where
  field
    transactions : List Transaction

data Block : Nat → Set where
  block : (n : Nat) → SimpleBlock → Block n

data Blockchain : Nat → Set where
  gen : {n : Nat} → Block n → Blockchain n
  cons : {n m : Nat} → Block n → Blockchain m → Blockchain n
