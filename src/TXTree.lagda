\begin{code}
module TXTree where

open import Prelude
open import Utils
open import Cripto
open import Transactions

totalQtSub1 : Nat
totalQtSub1 = 9

totalQt : Nat
totalQt = suc totalQtSub1

tQtTxs : Set
tQtTxs = Fin $ totalQt

blockReward : Nat
blockReward = 100

mutual
  data TXTree : (time : Time) (block : Nat)
    (outputs : List TXFieldWithId) (totalFees : Amount) (qtTransactions : tQtTxs) → Set where
    genesisTree : TXTree (nat zero) zero [] zero zero
    txtree      :
      {block : Nat} {time : Time}
      {outSize : Nat} {amount : Amount}
      {inputs : List TXFieldWithId}
      {outputTX : VectorOutput time outSize amount}
      {totalFees : Amount} {qtTransactions : tQtTxs}
      (tree : TXTree time block inputs totalFees qtTransactions)
      (proofLessQtTX : IsTrue (lessNat (finToNat qtTransactions) totalQtSub1))
      (tx : TX {time} {block} {inputs} {outSize} tree outputTX)
      (pCoinBaseFee : coinbase≡TotalFee+Reward totalFees tx)
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
      (txSigned : TXSigned (sub→list SubInputs) outputs)
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
    {totalFees : Amount} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions} {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → Amount
  incFees {_} {_} {_} {_} {amount} {totalFees} (normalTX tr SubInputs outputs _) =
      amount
    - txFieldList→TotalAmount (sub→list SubInputs)
    + totalFees
  incFees (coinbase tr outputs) = zero

  coinbase≡TotalFee+Reward :
    {amount : Amount}
    {block : Nat} {time : Time}
    {inputs : List TXFieldWithId}
    {outSize : Nat}
    {outputs : VectorOutput time outSize amount}
    {qtTransactions : Fin totalQt}
    {totalFees : Amount}
    {tr : TXTree time block inputs totalFees qtTransactions}
    (fees : Amount)
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → Set
  coinbase≡TotalFee+Reward fees (normalTX tr SubInputs outputs txSigned) = ⊤
  coinbase≡TotalFee+Reward {amount} fees (coinbase tr outputs) = amount ≡ fees + blockReward
\end{code}
