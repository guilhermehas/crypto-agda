module Blockchain where

open import Prelude
open import Operators
open import Utils
open import Transactions
open import BlockTransactions

record SimpleBlock : Set where
  field
    idb : Id
    size : Fin 10
    transactions : Vec BlockTransaction (finToNat size)
    timestamp : Nat

lenBlock : SimpleBlock → Nat
lenBlock sb = finToNat size
  where open SimpleBlock sb

countCoinBase : ∀ {n : Nat} → Vec BlockTransaction n → Nat
countCoinBase [] = 0
countCoinBase (txCoinBase tx x ∷ vec) = suc $ countCoinBase vec
countCoinBase (txNormal tx x ∷ vec) =  countCoinBase vec

blockId : SimpleBlock → Id
blockId sb = hash $ finToNat size +msg nat timestamp
  where open SimpleBlock sb

data Block : Set where
  block : (block : SimpleBlock) → countCoinBase (SimpleBlock.transactions block) ≡ 1 → Block

data Blockchain : Set where
  blocks : ∀ {n : Nat} → (vbt : Vec BlockTransaction n) → rightTxs vbt → Blockchain
