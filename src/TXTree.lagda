\begin{code}
module TXTree where

open import Prelude
open import Utils
open import Crypto
open import Transactions

totalQtSub1 : Nat
totalQtSub1 = 9

totalQt : Nat
totalQt = suc totalQtSub1

tQtTxs : Set
tQtTxs = Fin $ totalQt

blockReward : Nat → Nat
blockReward _ = 100
\end{code}

%<*TXTree>
\begin{code}
mutual
  data TXTree : (time : Time) (block : Nat)
    (outputs : List TXFieldWithId)
    (totalFees : Amount)
    (qtTransactions : tQtTxs) → Set where

    genesisTree : TXTree (nat zero) zero [] zero zero
    txtree      :
      {block : Nat} {time : Time}
      {outSize : Nat} {amount : Amount}
      {inputs : List TXFieldWithId}
      {outputTX : VectorOutput time outSize amount}
      {totalFees : Amount} {qtTransactions : tQtTxs}
      (tree : TXTree time block inputs totalFees qtTransactions)
      (tx : TX {time} {block} {inputs} {outSize} tree outputTX)
      (proofLessQtTX :
        Either
          (IsTrue (lessNat (finToNat qtTransactions) totalQtSub1))
          (isCoinbase tx))
      → TXTree (sucTime time)
        (nextBlock tx)
        (inputsTX tx ++ VectorOutput→List outputTX)
        (incFees tx) (incQtTx tx proofLessQtTX)
\end{code}
%</TXTree>

%<*TX>
\begin{code}
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
      (pAmountFee : outAmount out≡Fee totalFees +RewardBlock block)
      → TX tr outputs
\end{code}
%</TX>

%<*isCoinBase>
\begin{code}
  isCoinbase : ∀ {block : Nat} {time : Time}
    {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions}
    {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → Set
  isCoinbase (normalTX _ _ _ _) = ⊥
  isCoinbase (coinbase _ _ _)     = ⊤
\end{code}
%</isCoinBase>

%<*nextBlock>
\begin{code}
  nextBlock : ∀ {block : Nat} {time : Time}
    {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions}
    {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → Nat
  nextBlock (normalTX genesisTree _ _ _) = zero
  nextBlock {block} (normalTX (txtree _ (normalTX _ _ _ _) _) _ _ _) = block
  nextBlock {block} (normalTX (txtree _ (coinbase _ _ _) _) _ _ _) = suc block
  nextBlock (coinbase genesisTree _ _) = zero
  nextBlock {block} (coinbase (txtree _ (normalTX _ _ _ _) _) _ _) = block
  nextBlock {block} (coinbase (txtree _ (coinbase _ _ _) _) _ _) = suc block
\end{code}
%</nextBlock>

%<*inputsTX>
\begin{code}
  inputsTX : ∀ {block : Nat} {time : Time}
    {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions}
    {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → List TXFieldWithId
  inputsTX (normalTX _ SubInputs _ _) = list-sub SubInputs
  inputsTX {_} {_} {inputs} (coinbase _ _ _) = inputs
\end{code}
%</inputsTX>

%<*incQtTx>
\begin{code}
  incQtTx : ∀ {qtTransactions : tQtTxs}
    {block : Nat} {time : Time}
    {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Nat}
    {tr : TXTree time block inputs totalFees qtTransactions}
    {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    (proofLessQtTX :
      Either
        (IsTrue (lessNat (finToNat qtTransactions) totalQtSub1))
        (isCoinbase tx))
    → tQtTxs
  incQtTx {qt} (normalTX _ _ _ _) (left pLess) =
    natToFin (suc (finToNat qt)) {{pLess}}
  incQtTx {qt} (normalTX _ _ _ _) (right ())
  incQtTx (coinbase _ _ _)  _   = zero
\end{code}
%</incQtTx>

%<*incFees>
\begin{code}
  incFees : ∀ {block : Nat} {time : Time}
    {inputs : List TXFieldWithId}
    {outSize : Nat} {amount : Amount}
    {totalFees : Amount} {qtTransactions : tQtTxs}
    {tr : TXTree time block inputs totalFees qtTransactions}
    {outputs : VectorOutput time outSize amount}
    (tx : TX {time} {block} {inputs} {outSize} tr outputs)
    → Amount
  incFees {_} {_} {_} {_} {amount} {totalFees}
    (normalTX _ SubInputs _ (txsig _ _ in≥out)) =
    txFieldList→TotalAmount (sub→list SubInputs)
    - amount p≥ in≥out
    + totalFees
  incFees (coinbase tr outputs _) = zero
\end{code}
%</incFees>

%<*outFee>
\begin{code}
  _out≡Fee_+RewardBlock_ : (amount : Amount)
    (totalFees : Amount)
    (block : Nat) → Set
  amount out≡Fee totalFees +RewardBlock block =
    amount ≡ totalFees + blockReward block
\end{code}
%</outFee>
