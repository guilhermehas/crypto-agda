module Ledger where

open import Prelude
open import Operators
open import Utils
open import Cripto
open import Transactions
open import TXTree

ledger : ∀ (outputs : List TXFieldWithId) (addr : Address)
  → Amount
ledger [] addr = zero
ledger (output ∷ outputs) addr with TXFieldWithId.address output ≡?addr addr
... | yes _ = TXFieldWithId.amount output + ledger outputs addr
... | no  _ = ledger outputs addr
