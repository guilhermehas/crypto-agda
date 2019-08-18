module TXTree where

open import Prelude
open import Utils
open import Cripto
open import Transactions

mutual
  data TXTree : (time : Time) (block : Nat) (outputs : List TXFieldWithId) → Set where
    genesisTree : TXTree (nat zero) zero []
    txtree      : ∀ {block : Nat} {time : Time} {outSize : Nat}
      {inputs : List TXFieldWithId}
      {outputTX : VectorOutput time outSize}
      → (tree : TXTree time block inputs) → (tx : TX {time} {block} {inputs} {outSize} tree outputTX)
      → TXTree (sucTime time) (nextBlock tx) (inputsTX tx ++ VectorOutput→List outputTX)

  data TX {time : Time} {block : Nat} {inputs : List TXFieldWithId} {outSize : Nat}
    : (tr : TXTree time block inputs) (outputs : VectorOutput time outSize) → Set where
    normalTX : (tr : TXTree time block inputs)
      → (SubInputs : SubList inputs)
      → (outputs : VectorOutput time outSize)
      → (txSigned : TXSigned (sub→list SubInputs) (VectorOutput→List outputs))
      → TX tr outputs
    coinbase : (tr : TXTree time block inputs) → (outputs : VectorOutput time outSize) → TX tr outputs

  nextBlock : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId} {outSize : Nat}
    {tr : TXTree time block inputs} {outputs : VectorOutput time outSize}
    → (tx : TX {time} {block} {inputs} {outSize} tr outputs) → Nat
  nextBlock {block} (normalTX _ _ _ _) = block
  nextBlock {block} (coinbase _ _) = suc block

  inputsTX : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId} {outSize : Nat}
    {tr : TXTree time block inputs} {outputs : VectorOutput time outSize}
    → (tx : TX {time} {block} {inputs} {outSize} tr outputs) → List TXFieldWithId
  inputsTX (normalTX _ SubInputs _ _) = list-sub SubInputs
  inputsTX {_} {_} {inputs} (coinbase _ _) = inputs

record RawTXTree : Set where
  field
    time    : Time
    block   : Nat
    outputs : List TXFieldWithId
    txTree  : TXTree time block outputs

addTransactionTree : (txTree : RawTXTree) → (tx : RawTX) → Maybe RawTXTree
addTransactionTree record { time = time ; block = block ; outputs = outputs ; txTree = txTree }
  (coinbase record { outputs = outputsTX }) with listTXField→VecOut outputs
... | nothing     = nothing
... | just record { time = timeOut ; outSize = outSize ; vecOut = vecOut }
  with time == timeOut
...   | no _     = nothing
...   | yes refl = just $
  record { time = sucTime time ; block = suc block ;
  outputs = outputs ++ VectorOutput→List vecOut ; txTree = txtree txTree tx }
  where
    tx : TX txTree vecOut
    tx = coinbase txTree vecOut

addTransactionTree record { time = time ; block = block ; outputs = outputs ; txTree = txTree }
  (normalTX record { inputs = inputsTX ; outputs = outputsTX })
  with raw→TXSigned time record { inputs = inputsTX ; outputs = outputsTX }
... | nothing    = nothing
... | just txSig = {!!}
