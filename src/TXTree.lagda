\begin{code}
module TXTree where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import RawTransactions

totalQtSub1 : Nat
totalQtSub1 = 9

totalQt : Nat
totalQt = suc totalQtSub1

tQtTxs : Set
tQtTxs = Fin $ totalQt

mutual
  data TXTree : (time : Time) (block : Nat)
    (outputs : List TXFieldWithId) (totalFees : Amount) (qtTransactions : tQtTxs) → Set where
    genesisTree : TXTree (nat zero) zero [] zero zero
    txtree      :
      {block : Nat} {time : Time}
      {outSize : Nat} {amount : Amount}
      {inputs : List TXFieldWithId}
      {outputTX : VectorOutput time outSize amount}
      {totalFees : Nat} {qtTransactions : tQtTxs}
      (tree : TXTree time block inputs totalFees qtTransactions)
      (proofLessQtTX : IsTrue (lessNat (finToNat qtTransactions) totalQtSub1))
      (tx : TX {time} {block} {inputs} {outSize} tree outputTX)
      → TXTree (sucTime time) (nextBlock tx) (inputsTX tx ++ VectorOutput→List outputTX)
        (incFees tx) (incQtTx tx proofLessQtTX)

  data TX {time : Time} {block : Nat} {inputs : List TXFieldWithId}
       {outSize : Nat} {outAmount : Amount}
       {totalFees : Nat} {qtTransactions : tQtTxs}
    : (tr : TXTree time block inputs totalFees qtTransactions)
      (outputs : VectorOutput time outSize outAmount) → Set where
    normalTX :
      (tr : TXTree time block inputs totalFees qtTransactions)
      (SubInputs : SubList inputs)
      (outputs : VectorOutput time outSize outAmount)
      (txSigned : TXSigned (sub→list SubInputs) (VectorOutput→List outputs))
      → TX tr outputs
    coinbase :
      (tr : TXTree time block inputs totalFees qtTransactions)
      (outputs : VectorOutput time outSize outAmount)
      → TX tr outputs

  nextBlock : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize amount}
    → (tx : TX {time} {block} {inputs} {outSize} tr outputs) → Nat
  nextBlock {block} (normalTX _ _ _ _) = block
  nextBlock {block} (coinbase _ _)     = suc block

  inputsTX : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize amount}
    → (tx : TX {time} {block} {inputs} {outSize} tr outputs) → List TXFieldWithId
  inputsTX (normalTX _ SubInputs _ _) = list-sub SubInputs
  inputsTX {_} {_} {inputs} (coinbase _ _) = inputs

  incQtTx : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    (proofLessQtTX : IsTrue (lessNat (finToNat qtTransactions) totalQtSub1))
    → tQtTxs
  incQtTx {_} {_} {_} {_} {_} {_} {qt} (normalTX _ _ _ _) pLess = natToFin (suc (finToNat qt)) {{pLess}}
  incQtTx (coinbase _ _)  _   = zero

  incFees : ∀ {block : Nat} {time : Time} {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → Amount
  incFees {_} {_} {_} {_} {totalFees} (normalTX tr SubInputs outputs _) =
    txFieldList→TotalAmount (VectorOutput→List outputs)
    - txFieldList→TotalAmount (sub→list SubInputs)
    + totalFees
  incFees (coinbase tr outputs) = zero

dec< : (m n : Nat) → Dec $ IsTrue $ lessNat m n
dec< zero zero = no (λ ())
dec< zero (suc n) = yes true
dec< (suc m) zero = no (λ ())
dec< (suc m) (suc n) = dec< m n

record RawTXTree : Set where
  field
    time           : Time
    block          : Nat
    outputs        : List TXFieldWithId
    totalFees      : Amount
    qtTransactions : tQtTxs
    txTree         : TXTree time block outputs totalFees qtTransactions

addTransactionTree : (txTree : RawTXTree) → (tx : RawTX) → Maybe RawTXTree
addTransactionTree record { time = time ; block = block ; outputs = outputs ;
  qtTransactions = qtTransactions ; txTree = txTree }
  (coinbase record { outputs = outputsTX }) with listTXField→VecOut outputsTX
... | nothing     = nothing
... | just record { time = timeOut ; outSize = outSize ; vecOut = vecOut }
  with dec< (finToNat qtTransactions) totalQtSub1
...   | no _  = nothing
...   | yes pLess
  with time == timeOut
...     | no _     = nothing
...     | yes refl = just $
  record { time = sucTime time ; block = suc block ;
  outputs = outputs ++ VectorOutput→List vecOut ; txTree = txtree txTree pLess tx }
  where
    tx : TX txTree vecOut
    tx = coinbase txTree vecOut

addTransactionTree record { time = time ; block = block ; outputs = outputs ;
  qtTransactions = qtTransactions ; txTree = txTree }
  (normalTX record { inputs = inputsTX ; outputs = outputsTX })
  with dec< (finToNat qtTransactions) totalQtSub1
... | no _ = nothing
... | yes pLess
  with raw→TXSigned time record { inputs = inputsTX ; outputs = outputsTX }
...   | nothing    = nothing
...   | just txSig with rawTXSigned→TXSigAll time outputs txSig
...     | nothing    = nothing
...     | just record { outSize = outSize ; sub = sub ; outputs = outs ; signed = signed } =
  just $ record { time = sucTime time ; block = block ;
  outputs = list-sub sub ++ VectorOutput→List outs ;
  txTree = txtree txTree pLess (normalTX txTree sub outs signed) }

addMaybeTransTree : (txTree : Maybe RawTXTree) → (tx : RawTX) → Maybe RawTXTree
addMaybeTransTree nothing tx = nothing
addMaybeTransTree (just tree) tx = addTransactionTree tree tx
\end{code}
