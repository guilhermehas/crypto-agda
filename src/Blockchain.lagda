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
firstTreesInBlock (txtree genesisTree _ _) = ⊥
firstTreesInBlock (txtree (txtree _ (normalTX _ _ _ _) _) _ _) = ⊥
firstTreesInBlock (txtree (txtree _ (coinbase _ _ _) _) _ _) = ⊤

isFirstTreeInBlock :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Dec (firstTreesInBlock tree)
isFirstTreeInBlock genesisTree = yes tt
isFirstTreeInBlock (txtree genesisTree (normalTX _ _ _ _) _) = no λ x → x
isFirstTreeInBlock (txtree genesisTree (coinbase _ _ _) _) = no λ x → x
isFirstTreeInBlock (txtree (txtree _ (normalTX _ _ _ _) _) _ _) = no λ x → x
isFirstTreeInBlock (txtree (txtree _ (coinbase _ _ _) _) _ _) = yes tt

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
  constructor blockc
  field
    nxTree           : nextTXTree txTree₁ txTree₂
    fstBlock         : firstTreesInBlock txTree₁
    sndBlockCoinbase : coinbaseTree txTree₂
\end{code}
%</block>

%<*blockpchain>
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

\begin{code}
record RawBlock
  {block : Nat}
  {time₂ : Time}
  {outputs₂ : List TXFieldWithId}
  {totalFees₂ : Amount}
  {qtTransactions₂ : tQtTxs}
  (tree₂ : TXTree time₂ block outputs₂ totalFees₂ qtTransactions₂)
  : Set where
  constructor rawBlockc
  field
    {time}           : Time
    {outputs}        : List TXFieldWithId
    {totalFees}      : Amount
    {qtTransactions} : tQtTxs
    tree             : TXTree time block outputs totalFees qtTransactions
    rawBlock         : Block tree tree₂

isCoinbaseTree :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Dec (coinbaseTree tree)
isCoinbaseTree genesisTree = no λ x → x
isCoinbaseTree (txtree _ (normalTX _ _ _ _) _) = no λ x → x
isCoinbaseTree (txtree _ (coinbase _ _ _) _) = yes tt

record fstTree
  {block : Nat}
  {time₂ : Time}
  {outputs₂ : List TXFieldWithId}
  {totalFees₂ : Amount}
  {qtTransactions₂ : tQtTxs}
  (txTree₂ : TXTree time₂ block outputs₂ totalFees₂ qtTransactions₂)
  : Set where
  constructor fstTreec
  field
    {time}               : Time
    {outputs}            : List TXFieldWithId
    {totalFees}          : Amount
    {qtTransactions}     : tQtTxs
    {tree}               : TXTree time block outputs totalFees qtTransactions
    nxTree               : nextTXTree tree txTree₂
    fstBlockc            : firstTreesInBlock tree

fstTreeBlock :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  {tree : TXTree time block outputs totalFees qtTransactions}
  (fstTree : fstTree tree)
  → Nat
fstTreeBlock {block} _ = block


firstTree¬ :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  (¬fstInBlock : ¬ (firstTreesInBlock tree))
  → Dec (fstTree tree)
firstTree¬ genesisTree ¬fstInBlock = no λ x → ¬fstInBlock tt
firstTree¬ (txtree genesisTree (normalTX _ SubInputs outputs txSigned) proofLessQtTX) ¬fstInBlock = yes {!!}
firstTree¬ (txtree genesisTree (coinbase _ outputs pAmountFee) proofLessQtTX) ¬fstInBlock = yes {!!}
firstTree¬ (txtree (txtree tree (normalTX _ SubInputs outputs txSigned) proofLessQtTX₁) tx proofLessQtTX) ¬fstInBlock = yes {!!}
firstTree¬ (txtree (txtree _ (coinbase _ _ _) _) _ _) ¬fstInBlock = no λ x → ¬fstInBlock tt


firstTree :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → fstTree tree
firstTree {_} {time} {outputs} {totalFees} {qtTransactions} genesisTree =
  fstTreec (firstTX genesisTree) unit
firstTree (txtree genesisTree (normalTX _ SubInputs outputs txSigned) proofLessQtTX) =
  let sameTX = normalTX genesisTree SubInputs outputs txSigned
  in fstTreec (nextTX genesisTree genesisTree (firstTX genesisTree) sameTX proofLessQtTX) unit
firstTree (txtree genesisTree (coinbase _ outputs pAmountFee) proofLessQtTX) =
  let sameTX = coinbase genesisTree outputs pAmountFee
  in fstTreec (nextTX genesisTree genesisTree (firstTX genesisTree) sameTX proofLessQtTX) unit
firstTree (txtree (txtree {block} tree (normalTX _ SubInputs outputs txSigned) proofLessQtTX₁) tx proofLessQtTX) =
  let fstTreeRec = firstTree (txtree tree (normalTX _ SubInputs outputs txSigned) proofLessQtTX₁)
      fstTree = fstTree.tree fstTreeRec
  in fstTreec {{!fstTreeBlock fstTreeRec!}} {_} {_} {_} {_} {_} {_} {_} {_} {_} {{!fstTree!}}  {!!} {!!}
firstTree {_} {time} {outs} {totalFees} {qtTransactions}
  (txtree (txtree tree (coinbase _ outputs pAmountFee) proofLessQtTX₁) tx proofLessQtTX) =
  let sameTree = (txtree (txtree tree (coinbase tree outputs pAmountFee) proofLessQtTX₁) tx proofLessQtTX)
  in fstTreec (firstTX sameTree) unit


txTree→Block :
  {block : Nat}
  {time : Time}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Dec (RawBlock tree)
txTree→Block genesisTree = no λ{(rawBlockc _ (blockc _ _ sndBlockCoinbase)) → sndBlockCoinbase}
txTree→Block (txtree tree tx proofLessQtTX) with isCoinbaseTree (txtree tree tx proofLessQtTX)
... | no ¬p = no λ{ (rawBlockc _ (blockc _ _ coinbaseTree)) → ¬p coinbaseTree}
... | yes p = {!!}

\end{code}
