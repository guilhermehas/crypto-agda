\begin{code}
module TXTree where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import RawTransactions

tQtTxs : Set
tQtTxs = Fin 10

mutual
  data TXTree : (time : Time) (block : Nat)
    (outputs : List TXFieldWithId) (totalFees : Nat) (qtTransactions : tQtTxs) → Set where
    genesisTree : TXTree (nat zero) zero [] zero zero
    txtree      :
      {block : Nat} {time : Time} {outSize : Nat}
      {inputs : List TXFieldWithId}
      {outputTX : VectorOutput time outSize}
      {totalFees : Nat} {qtTransactions : tQtTxs}
      (tree : TXTree time block inputs totalFees qtTransactions)
      (tx : TX {time} {block} {inputs} {outSize} tree outputTX)
      → TXTree (sucTime time) (nextBlock tx) (inputsTX tx ++ VectorOutput→List outputTX) zero qtTransactions

  data TX {time : Time} {block : Nat} {inputs : List TXFieldWithId} {outSize : Nat}
       {totalFees : Nat} {qtTransactions : tQtTxs}
    : (tr : TXTree time block inputs totalFees qtTransactions) (outputs : VectorOutput time outSize) → Set where
    normalTX :
      (tr : TXTree time block inputs totalFees qtTransactions)
      (SubInputs : SubList inputs)
      (outputs : VectorOutput time outSize)
      (txSigned : TXSigned (sub→list SubInputs) (VectorOutput→List outputs))
      → TX tr outputs
    coinbase :
      (tr : TXTree time block inputs totalFees qtTransactions)
      (outputs : VectorOutput time outSize)
      → TX tr outputs

  nextBlock : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId} {outSize : Nat}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize}
    → (tx : TX {time} {block} {inputs} {outSize} tr outputs) → Nat
  nextBlock {block} (normalTX _ _ _ _) = block
  nextBlock {block} (coinbase _ _)     = suc block

  inputsTX : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId} {outSize : Nat}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize}
    → (tx : TX {time} {block} {inputs} {outSize} tr outputs) → List TXFieldWithId
  inputsTX (normalTX _ SubInputs _ _) = list-sub SubInputs
  inputsTX {_} {_} {inputs} (coinbase _ _) = inputs

record RawTXTree : Set where
  field
    time    : Time
    block   : Nat
    outputs : List TXFieldWithId
    totalFees : Nat
    qtTransactions : tQtTxs
    txTree  : TXTree time block outputs totalFees qtTransactions

addTransactionTree : (txTree : RawTXTree) → (tx : RawTX) → Maybe RawTXTree
addTransactionTree record { time = time ; block = block ; outputs = outputs ; txTree = txTree }
  (coinbase record { outputs = outputsTX }) with listTXField→VecOut outputsTX
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

addMaybeTransTree : (txTree : Maybe RawTXTree) → (tx : RawTX) → Maybe RawTXTree
addMaybeTransTree nothing tx = nothing
addMaybeTransTree (just tree) tx = addTransactionTree tree tx
\end{code}
