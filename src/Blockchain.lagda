\begin{code}
module Blockchain where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import TXTree

data nextTXTree :
  {block₁ : Nat}
  {time₁ : Time}
  {outputs₁ : List TXFieldWithId}
  {totalFees₁ : Amount}
  {qtTransactions₁ : tQtTxs}
  (txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁)

  {block₂ : Nat}
  {time₂ : Time}
  {outputs₂ : List TXFieldWithId}
  {totalFees₂ : Amount}
  {qtTransactions₂ : tQtTxs}
  (txTree₂ : TXTree time₂ block₂ outputs₂ totalFees₂ qtTransactions₂)
  → Set where

  firstTX :
    {block : Nat}
    {time : Time}
    {outputs : List TXFieldWithId}
    {totalFees : Amount}
    {qtTransactions : tQtTxs}
    (txTree : TXTree time block outputs totalFees qtTransactions)
    → nextTXTree txTree txTree
  nextTX :
    {block₁ : Nat}
    {time₁ : Time}
    {outputs₁ : List TXFieldWithId}
    {totalFees₁ : Amount}
    {qtTransactions₁ : tQtTxs}
    (txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁)

    {block₂ : Nat}
    {time₂ : Time}
    {outputs₂ : List TXFieldWithId}
    {totalFees₂ : Amount}
    {qtTransactions₂ : tQtTxs}
    (txTree₂ : TXTree time₂ block₂ outputs₂ totalFees₂ qtTransactions₂)

    (nxTree : nextTXTree txTree₁ txTree₂)

    {outSize : Nat} {amount : Amount}
    {outputTX : VectorOutput time₂ outSize amount}
    {totalFees : Amount}
    (tx : TX {time₂} {block₂} {outputs₂} {outSize} txTree₂ outputTX)
    (proofLessQtTX :
      Either
        (IsTrue (lessNat (finToNat qtTransactions₂) totalQtSub1))
        (isCoinbase tx))
    → nextTXTree txTree₁ (txtree txTree₂ tx proofLessQtTX)

firstTreesInBlock :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Set
firstTreesInBlock genesisTree = ⊤
firstTreesInBlock (txtree genesisTree (normalTX .genesisTree _ _ _) _) = ⊥
firstTreesInBlock (txtree (txtree _ (normalTX _ _ _ _) _) (normalTX _ _ _ _) _) = ⊥
firstTreesInBlock (txtree (txtree _ (coinbase _ _ _) _) (normalTX _ _ _ _) _) = ⊤
firstTreesInBlock (txtree genesisTree (coinbase _ _ _) _) = ⊥
firstTreesInBlock (txtree (txtree _ (normalTX _ _ _ _) _) (coinbase _ _ _) _) = ⊥
firstTreesInBlock (txtree (txtree _ (coinbase _ _ _) _) (coinbase _ _ _) _) = ⊤

coinbaseTree :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Set
coinbaseTree genesisTree = ⊥
coinbaseTree (txtree _ (normalTX _ _ _ _) _) = ⊥
coinbaseTree (txtree _ (coinbase _ _ _) _) = ⊤
\end{code}

%<*block>
\begin{code}
record Block
  {block₁ : Nat}
  {time₁ : Time}
  {outputs₁ : List TXFieldWithId}
  {totalFees₁ : Amount}
  {qtTransactions₁ : tQtTxs}
  (txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁)

  {time₂ : Time}
  {outputs₂ : List TXFieldWithId}
  {totalFees₂ : Amount}
  {qtTransactions₂ : tQtTxs}
  (txTree₂ : TXTree time₂ block₁ outputs₂ totalFees₂ qtTransactions₂)
  : Set where
  constructor block
  field
    nxTree           : nextTXTree txTree₁ txTree₂
    fstBlock         : firstTreesInBlock txTree₁
    sndBlockCoinbase : coinbaseTree txTree₂
\end{code}
%</block>

%<*blockchain>
\begin{code}
data Blockchain :
  {block₁ : Nat}
  {time₁ : Time}
  {outputs₁ : List TXFieldWithId}
  {totalFees₁ : Amount}
  {qtTransactions₁ : tQtTxs}
  {txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁}

  {time₂ : Time}
  {outputs₂ : List TXFieldWithId}
  {totalFees₂ : Amount}
  {qtTransactions₂ : tQtTxs}
  {txTree₂ : TXTree time₂ block₁ outputs₂ totalFees₂ qtTransactions₂}
  (block : Block txTree₁ txTree₂)
  → Set where
    fstBlock :
      {block₁ : Nat}
      {time₁ : Time}
      {outputs₁ : List TXFieldWithId}
      {totalFees₁ : Amount}
      {qtTransactions₁ : tQtTxs}
      {txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁}

      {time₂ : Time}
      {outputs₂ : List TXFieldWithId}
      {totalFees₂ : Amount}
      {qtTransactions₂ : tQtTxs}
      {txTree₂ : TXTree time₂ block₁ outputs₂ totalFees₂ qtTransactions₂}
      (block : Block txTree₁ txTree₂)
      → Blockchain block

    addBlock :
      {block-p₁ : Nat}
      {time-p₁ : Time}
      {outputs-p₁ : List TXFieldWithId}
      {totalFees-p₁ : Amount}
      {qtTransactions-p₁ : tQtTxs}
      {txTree-p₁ : TXTree time-p₁ block-p₁ outputs-p₁ totalFees-p₁ qtTransactions-p₁}

      {time-p₂ : Time}
      {outputs-p₂ : List TXFieldWithId}
      {totalFees-p₂ : Amount}
      {qtTransactions-p₂ : tQtTxs}
      {txTree-p₂ : TXTree time-p₂ block-p₁ outputs-p₂ totalFees-p₂ qtTransactions-p₂}
      {block-p : Block txTree-p₁ txTree-p₂}
      (blockchain : Blockchain block-p)

      {outputs : List TXFieldWithId}
      {outSize : Nat}
      {amount : Amount}
      {outputTX : VectorOutput time-p₂ outSize amount}
      {totalFees : Amount} {qtTransactions : tQtTxs}
      {tx : TX {time-p₂} {block-p₁} {outputs-p₂} {outSize} txTree-p₂ outputTX}
      {proofLessQtTX :
        Either
          (IsTrue (lessNat (finToNat qtTransactions-p₂) totalQtSub1))
          (isCoinbase tx)}

      {time₂ : Time}
      {outputs₂ : List TXFieldWithId}
      {totalFees₂ : Amount}
      {qtTransactions₂ : tQtTxs}
      {txTree₂ : TXTree time₂ (nextBlock tx) outputs₂ totalFees₂ qtTransactions₂}

      (block : Block (txtree txTree-p₂ tx proofLessQtTX) txTree₂)
      → Blockchain block
\end{code}
%</blockchain>
