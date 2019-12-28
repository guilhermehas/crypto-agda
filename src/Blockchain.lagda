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
  (txTree₂ : TXTree time₂ (suc block₁) outputs₂ totalFees₂ qtTransactions₂)
  : Set where
  constructor block
  field
    nxTree : nextTXTree txTree₁ txTree₂
\end{code}
