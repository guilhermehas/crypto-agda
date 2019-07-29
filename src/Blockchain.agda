module Blockchain where

open import Prelude
open import Operators
open import Utils
open import Transactions

mutual
  data TXTree : (time : Nat) (block : Nat) (outputs : List TXFieldWithId) → Set where
    genesisTree : TXTree 0 0 []
    txtree      : ∀ {time block : Nat} {inputs : List TXFieldWithId} {outputTX : ListOutput time}
      → (tree : TXTree time block inputs) → (tx : TX {time} {block} {inputs} tree outputTX)
      → TXTree (suc time) (suc block) []

  data TX {time : Nat} {block : Nat} {inputs : List TXFieldWithId}
    : (tr : TXTree time block inputs) (outputs : ListOutput time) → Set where
    normalTX : (tr : TXTree time block inputs) → (SubInputs : SubList inputs)
      → (outputs : ListOutput time) → TX tr outputs
    coinbase : (tr : TXTree time block inputs) → (outputs : ListOutput time) → TX tr outputs

record Block : Set where
  field
    coinbaseTX : TXUnsigned
    TXs : List normalTXrec

data TXOutputs : List TXField → Set where
  [] : TXOutputs []
  consCoinBase : {outs : List TXField} → (coinTX : TXField) → TXOutputs outs
    → TXOutputs (coinTX ∷ outs)
  consNormalTX : {outs : List TXField}
    → (inps : SubList outs) → (newOuts : List TXField)
    → TXOutputs outs
    → tx2Sign (sub→list inps) outs
    → TXOutputs (newOuts ++ (list-sub inps))

countCoinBase : {txs : List TXField} → TXOutputs txs → Nat
countCoinBase [] = zero
countCoinBase (consCoinBase coinTX txs) = suc $ countCoinBase txs
countCoinBase (consNormalTX inps newOuts txs x) = countCoinBase txs

data Blockchain : (xs : List TXField) → TXOutputs xs → Set where
  [] : Blockchain [] []
  -- cons : {outs : List TXField} → (txsOuts : TXOutputs outs)
  --   → (txs : normalTXrec) → (coinbase : TXField)
