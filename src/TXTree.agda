module TXTree where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import RawTransactions

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
  nextBlock {block} (coinbase _ _)     = suc block

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
... | just txSig with rawTXSigned→TXSigAll time outputs txSig
...   | nothing    = nothing
...   | just record { outSize = outSize ; sub = sub ; outputs = outs ; signed = signed } =
  just $ record { time = sucTime time ; block = block ;
  outputs = list-sub sub ++ VectorOutput→List outs ;
  txTree = txtree txTree (normalTX txTree sub outs signed) }

_out≤time_ : (out : TXFieldWithId) (time : Time) → Set
out out≤time time = timeToNat (TXFieldWithId.time out) < timeToNat time

outputsTimeLess : {time : Time} {block : Nat} {outputs : List TXFieldWithId}
  (txTree : TXTree time block outputs)
  → All (λ output → output out≤time time) outputs
outputsTimeLess genesisTree = []
outputsTimeLess (txtree {block} {time} {outSize} {outputs} {outVec} txTree tx) =
  allJoin (inputsTX tx) (VectorOutput→List outVec) (inputs≤→inputsTX tx $ outputsTimeLess txTree)
  $ vecOutTimeLess outVec
  where
    vecOutTimeLess : ∀ {time : Time} {outSize : Nat} (vecOut : VectorOutput time outSize)
      → All (λ output → output out≤time (sucTime time)) (VectorOutput→List vecOut)
    vecOutTimeLess (el tx refl elStart) = (diff zero (timeToNatSuc {TXFieldWithId.time tx})) ∷ []
    vecOutTimeLess (cons {time} vecOut tx refl elStart) =
      (diff zero (timeToNatSuc {time})) ∷ (vecOutTimeLess vecOut)

    ≤timeSuc : {t1 : TXFieldWithId} {t2 : Time} (pt : t1 out≤time t2) → t1 out≤time (sucTime t2)
    ≤timeSuc {record { time = time ; position = position ; amount = amount ; address = address }}
      {nat .(suc (k + timeToNat time))} (diff! k) = diff! (suc k)

    inputs≤→inputsTX : {inputs : List TXFieldWithId}
      {tree : TXTree time block inputs}
      (tx : TX tree outVec)
      (allInps : All (λ output → output out≤time time) inputs)
      → All (λ input → input out≤time sucTime time) (inputsTX tx)
    inputs≤→inputsTX {[]} (normalTX tr [] outVec txSigned) [] = []
    inputs≤→inputsTX {[]} (coinbase tr outputs) [] = []
    inputs≤→inputsTX {input ∷ inputs} (normalTX tr (input ¬∷ SubInputs) outVec txSigned) (pt ∷ allInps) =
      ≤timeSuc {input} {time} pt ∷ allProofFG (λ y pf → ≤timeSuc {y} {time} pf)
      (allList→allSub SubInputs allInps)
    inputs≤→inputsTX {input ∷ inputs} (normalTX tr (input ∷ SubInputs) outVec txSigned) (x ∷ allInps) =
      allProofFG (λ y pf → ≤timeSuc {y} {time} pf) (allList→allSub SubInputs allInps)
    inputs≤→inputsTX {input ∷ inputs} (coinbase tr outVec) (pt ∷ allInps) = ≤timeSuc {input} {time} pt
      ∷ allProofFG (λ y pf → ≤timeSuc {y} {time} pf) allInps

uniqueOutputs : {time : Time} {block : Nat} {outputs : List TXFieldWithId}
  (txTree : TXTree time block outputs) → Distinct outputs
uniqueOutputs genesisTree = []
uniqueOutputs (txtree {block} {time} {outSize} {inputs} {outVec} tree tx) = {!!}
  where
    distInputs : {time : Time} {block : Nat} {inputs : List TXFieldWithId} {outSize : Nat}
      {outVec : VectorOutput time outSize} {tree : TXTree time block inputs}
      (tx : TX tree outVec) → Distinct $ inputsTX tx
    distInputs (normalTX genesisTree SubInputs outputs txSigned) = {!!}
    distInputs (normalTX (txtree tr tx) SubInputs outputs txSigned) = {!!}
    distInputs (coinbase genesisTree outVec) = []
    distInputs (coinbase (txtree tr tx) outVec) = {!distInputs tx!}

