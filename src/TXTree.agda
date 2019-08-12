module TXTree where

open import Prelude
open import Operators
open import Utils
open import Cripto
open import Transactions

mutual
  data TXTree : (time : Time) (block : Nat) (outputs : List TXFieldWithId) → Set where
    genesisTree : TXTree (nat zero) zero []
    txtree      : ∀ {block : Nat} {time : Time} {outSize : Nat}
      {inputs : List TXFieldWithId}
      {outputTX : VectorOutput time outSize}
      → (tree : TXTree time block inputs) → (tx : TX {time} {block} {inputs} outSize tree outputTX)
      → TXTree (sucTime time) (nextBlock tx) (inputsTX tx ++ VectorOutput→List outputTX)

  data TX {time : Time} {block : Nat} {inputs : List TXFieldWithId}
    : (outSize : Nat) (tr : TXTree time block inputs) (outputs : VectorOutput time outSize) → Set where
    normalTX : {outSizePred : Nat}
      → (tr : TXTree time block inputs)
      → (SubInputs : SubList inputs)
      → (outputs : VectorOutput time outSizePred)
      → (miner : TXField)
      → (txSigned : TXSigned (sub→list SubInputs) $ VectorOutput→List outputs)
      → (proofMinerMoney : verifyMinerMoneyNormalTX block txSigned miner)
      → TX (suc outSizePred) tr (addOutput outputs miner)
    coinbase : (tr : TXTree time block inputs) (miner : TXField)
      (proofMinerMoney : verifyMineyMoneyCoinbase block miner)
      → TX 1 tr (addFirstOutput time miner)

  nextBlock : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId} {outSize : Nat}
    {tr : TXTree time block inputs} {outputs : VectorOutput time outSize}
    → (tx : TX {time} {block} {inputs} outSize tr outputs) → Nat
  nextBlock {block} (normalTX _ _ _ _ _ _) = block
  nextBlock {block} (coinbase _ _ _) = suc block

  inputsTX : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId} {outSize : Nat}
    {tr : TXTree time block inputs} {outputs : VectorOutput time outSize}
    → (tx : TX {time} {block} {inputs} outSize tr outputs) → List TXFieldWithId
  inputsTX (normalTX _ SubInputs _ _ _ _) = list-sub SubInputs
  inputsTX {_} {_} {inputs} (coinbase _ _ _) = inputs

record RawTXTree : Set where
  field
    time    : Time
    block   : Nat
    outputs : List TXFieldWithId
    txTree  : TXTree time block outputs

addTransactionTree : (txTree : RawTXTree) (tx : RawTX) (miner : TXField) → Maybe RawTXTree
addTransactionTree record { time = time ; block = block ; outputs = outputs ; txTree = txTree }
  (coinbase record { outputs = outputsCoinbase }) miner = {!!}
addTransactionTree record { time = time ; block = block ; outputs = outputs ; txTree = txTree }
  (normalTX record { inputs = inputs ; outputs = outputsTX ; tx = tx }) miner = {!!}
