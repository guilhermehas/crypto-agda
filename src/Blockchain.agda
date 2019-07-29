module Blockchain where

open import Prelude
open import Operators
open import Utils
open import Cripto
open import Transactions

mutual
  data TXTree : (time : Time) (block : Nat) (outputs : List TXFieldWithId) → Set where
    genesisTree : TXTree (nat zero) zero []
    txtree      : ∀ {block : Nat} {time : Time}
      {inputs : List TXFieldWithId}
      {outputTX : ListOutput time}
      → (tree : TXTree time block inputs) → (tx : TX {time} {block} {inputs} tree outputTX)
      → TXTree (sucTime time) (nextBlock tx) (inputsTX tx ++ ListOutput→List outputTX)

  data TX {time : Time} {block : Nat} {inputs : List TXFieldWithId}
    : (tr : TXTree time block inputs) (outputs : ListOutput time) → Set where
    normalTX : (tr : TXTree time block inputs)
      → (SubInputs : SubList inputs)
      → (outputs : ListOutput time)
      → TXSigned (sub→list SubInputs) (ListOutput→List outputs)
      → TX tr outputs
    coinbase : (tr : TXTree time block inputs) → (outputs : ListOutput time) → TX tr outputs

  nextBlock : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId}
    {tr : TXTree time block inputs} {outputs : ListOutput time}
    → (tx : TX {time} {block} {inputs} tr outputs) → Nat
  nextBlock {block} (normalTX _ _ _ _) = block
  nextBlock {block} (coinbase _ _) = suc block

  inputsTX : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId}
    {tr : TXTree time block inputs} {outputs : ListOutput time}
    → (tx : TX {time} {block} {inputs} tr outputs) → List TXFieldWithId
  inputsTX (normalTX _ SubInputs _ _) = list-sub SubInputs
  inputsTX {_} {_} {inputs} (coinbase _ _) = inputs


-- record Block : Set where
--   field
--     coinbaseTX : TXUnsigned
--     TXs : List normalTXrec

-- data TXOutputs : List TXField → Set where
--   [] : TXOutputs []
--   consCoinBase : {outs : List TXField} → (coinTX : TXField) → TXOutputs outs
--     → TXOutputs (coinTX ∷ outs)
--   consNormalTX : {outs : List TXField}
--     → (inps : SubList outs) → (newOuts : List TXField)
--     → TXOutputs outs
--     → tx2Sign (sub→list inps) outs
--     → TXOutputs (newOuts ++ (list-sub inps))

-- countCoinBase : {txs : List TXField} → TXOutputs txs → Nat
-- countCoinBase [] = zero
-- countCoinBase (consCoinBase coinTX txs) = suc $ countCoinBase txs
-- countCoinBase (consNormalTX inps newOuts txs x) = countCoinBase txs

-- data Blockchain : (xs : List TXField) → TXOutputs xs → Set where
--   [] : Blockchain [] []
  -- cons : {outs : List TXField} → (txsOuts : TXOutputs outs)
  --   → (txs : normalTXrec) → (coinbase : TXField)
