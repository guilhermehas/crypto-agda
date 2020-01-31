\begin{code}
module Blockchain where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import TXTree
\end{code}

%<*nexttree>
\begin{code}
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

  firstTX : ∀ {block time outputs totalFees qtTransactions}
    (txTree : TXTree time block outputs totalFees qtTransactions)
    → nextTXTree txTree txTree
  nextTX : ∀ {block₁ time₁ outputs₁ totalFees₁ qtTransactions₁}
    {txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁}

    {block₂ time₂ outputs₂ totalFees₂ qtTransactions₂}
    {txTree₂ : TXTree time₂ block₂ outputs₂ totalFees₂ qtTransactions₂}

    (nxTree : nextTXTree txTree₁ txTree₂)

    {outSize amount}
    {outputTX : VectorOutput time₂ outSize amount}
    (tx : TX txTree₂ outputTX)
    (proofLessQtTX :
      Either
        (IsTrue (lessNat (finToNat qtTransactions₂) totalQtSub1))
        (isCoinbase tx))
    → nextTXTree txTree₁ (txtree txTree₂ tx proofLessQtTX)
\end{code}
%</nexttree>

%<*firsttreeinblock>
\begin{code}
firstTreesInBlock : ∀
  {block time outputs totalFees qtTransactions}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Set
firstTreesInBlock genesisTree = ⊤
firstTreesInBlock (txtree genesisTree _ _) = ⊥
firstTreesInBlock (txtree (txtree _ (normalTX _ _ _ _) _) _ _) = ⊥
firstTreesInBlock (txtree (txtree _ (coinbase _ _ _) _) _ _) = ⊤
\end{code}
%</firsttreeinblock>

%<*isfirsttreeinblock>
\begin{code}
isFirstTreeInBlock : ∀
  {block time outputs totalFees qtTransactions}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Dec (firstTreesInBlock tree)
isFirstTreeInBlock genesisTree = yes tt
isFirstTreeInBlock (txtree genesisTree (normalTX _ _ _ _) _) = no λ x → x
isFirstTreeInBlock (txtree genesisTree (coinbase _ _ _) _) = no λ x → x
isFirstTreeInBlock (txtree (txtree _ (normalTX _ _ _ _) _) _ _) = no λ x → x
isFirstTreeInBlock (txtree (txtree _ (coinbase _ _ _) _) _ _) = yes tt
\end{code}
%</isfirsttreeinblock>

%<*coinbasetree>
\begin{code}
coinbaseTree : ∀
  {block time outputs totalFees qtTransactions}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Set
coinbaseTree genesisTree = ⊥
coinbaseTree (txtree _ (normalTX _ _ _ _) _) = ⊥
coinbaseTree (txtree _ (coinbase _ _ _) _) = ⊤
\end{code}
%</coinbasetree>

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
\begin{code}

fstTree→coinbase : ∀
  {block time outputs totalFees qtTransactions}
  {tree : TXTree time block outputs totalFees qtTransactions}
  {outSize amount}
  {outputTX : VectorOutput time outSize amount}
  {tx : TX tree outputTX}
  {proofLessQtTX :
    Either
      (IsTrue (lessNat (finToNat qtTransactions) totalQtSub1))
      (isCoinbase tx)}
  (fstTree : firstTreesInBlock (txtree tree tx proofLessQtTX))
  → coinbaseTree tree
fstTree→coinbase {_} {_} {_} {_} {_} {genesisTree} ()
fstTree→coinbase {_} {_} {_} {_} {_} {txtree _ (normalTX _ _ _ _) _} ()
fstTree→coinbase {_} {_} {_} {_} {_} {txtree _ (coinbase _ _ _) _} _ = unit

\end{code}
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

      {outSize : Nat}
      {amount : Amount}
      {outputTX : VectorOutput time-p₂ outSize amount}
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

%<*rawblock>
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
    {tree}           : TXTree time block outputs totalFees qtTransactions
    rawBlock         : Block tree tree₂
\end{code}
%</rawblock>

%<*iscoinbase>
\begin{code}
isCoinbaseTree : ∀
  {block time outputs totalFees qtTransactions}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Dec (coinbaseTree tree)
isCoinbaseTree genesisTree = no λ x → x
isCoinbaseTree (txtree _ (normalTX _ _ _ _) _) = no λ x → x
isCoinbaseTree (txtree _ (coinbase _ _ _) _) = yes tt
\end{code}
%</iscoinbase>

%<*fsttree>
\begin{code}
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
\end{code}
%</fsttree>

\begin{code}
record fstTree₂
  {block : Nat}
  {time₂ : Time}
  {outputs₂ : List TXFieldWithId}
  {totalFees₂ : Amount}
  {qtTransactions₂ : tQtTxs}
  (txTree₂ : TXTree time₂ block outputs₂ totalFees₂ qtTransactions₂)
  : Set where
  constructor fstTreec₂
  field
    {block₂}              : Nat
    {time}               : Time
    {outputs}            : List TXFieldWithId
    {totalFees}          : Amount
    {qtTransactions}     : tQtTxs
    {tree}               : TXTree time block₂ outputs totalFees qtTransactions
    eq                   : block ≡ block₂
    nxTree               : nextTXTree tree txTree₂
    fstBlockc            : firstTreesInBlock tree

fstTree₂→fstTree : ∀
  {block time₂ outputs₂ totalFees₂ qtTransactions₂}
  {txTree₂ : TXTree time₂ block outputs₂ totalFees₂ qtTransactions₂}
  (fTree₂ : fstTree₂ txTree₂)
  → fstTree txTree₂
fstTree₂→fstTree (fstTreec₂ refl nxTree fstBlockc) = fstTreec nxTree fstBlockc

record fstTreeChange
  (block : Nat)
  (time : Time)
  (outputs : List TXFieldWithId)
  (totalFees : Amount)
  (qtTransactions : tQtTxs)
  : Set where
  constructor fstTreeChangedc
  field
    {tree}      : TXTree time block outputs totalFees qtTransactions
    ftree       : fstTree tree

changeBlockType : ∀
  {block block₂ time outputs totalFees qtTransactions}
  {tree : TXTree time block outputs totalFees qtTransactions}
  {txTree : TXTree time block outputs totalFees qtTransactions}
  (fstTree : fstTree tree)
  (eq : block ≡ block₂)
  → fstTreeChange block₂ time outputs totalFees qtTransactions
changeBlockType fstTree refl = fstTreeChangedc fstTree

record TXChange
  {block : Nat}
  {outSize : Nat}
  {amount : Nat}
  {time : Time}
  {block : Nat}
  {outputs : List TXFieldWithId}
  {outputTX : VectorOutput time outSize amount}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (tree : TXTree time block outputs totalFees qtTransactions)
  (tx : TX tree outputTX)
  (proofLess : Either (IsTrue (lessNat (finToNat qtTransactions) totalQtSub1)) (isCoinbase tx))
  : Set where
  constructor TXChangedc
  field
    fTree                 : fstTree (txtree tree tx proofLess)


changeTXType : ∀
  {block time₁ time₂ totalFees₁ totalFees₂ outputs₁ outputs₂ qtTransactions₁ qtTransactions₂
   outSize amount}
  {outputTX : VectorOutput time₂ outSize amount}
  {tree : TXTree time₁ block outputs₁ totalFees₁ qtTransactions₁}
  {tree₂ : TXTree time₂ block outputs₂ totalFees₂ qtTransactions₂}
  (nxTree : nextTXTree tree tree₂)
  (fstBlockc : firstTreesInBlock tree)
  (tx : TX tree₂ outputTX)
  (proofLess : Either (IsTrue (lessNat (finToNat qtTransactions₂) totalQtSub1)) (isCoinbase tx))
  (eq : nextBlock tx ≡ block)
  → TXChange {block} tree₂ tx proofLess
changeTXType nxTree fblock tx proof eq =
  let nxTX = nextTX nxTree tx proof
      ftree = fstTree₂→fstTree (fstTreec₂ eq nxTX fblock)
  in TXChangedc ftree


fstTreeBlock : ∀
  {block time outputs totalFees qtTransactions}
  {tree : TXTree time block outputs totalFees qtTransactions}
  (fstTree : fstTree tree)
  → Nat
fstTreeBlock {block} _ = block
\end{code}

%<*firsttree>
\begin{code}
firstTree : ∀
  {block time outputs totalFees qtTransactions}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → fstTree tree
firstTree genesisTree = fstTreec (firstTX genesisTree) unit
firstTree {block₂} (txtree {block₁} tree tx proofLessQtTX)
  with isFirstTreeInBlock (txtree tree tx proofLessQtTX)
... | yes isFirst = fstTreec (firstTX (txtree tree tx proofLessQtTX)) isFirst
... | no ¬first with let fstTree = firstTree tree in block₂ == block₁
...   | yes eq = let ftree = firstTree tree
                     nxTree = fstTree.nxTree ftree
                     fstBlock = fstTree.fstBlockc ftree
                     chgType = changeTXType nxTree fstBlock tx proofLessQtTX eq
                 in TXChange.fTree chgType
...   | no ¬eq = ⊥-elim impossible
          where postulate impossible : ⊥
\end{code}
%</firsttree>

%<*treeblock>
\begin{code}
txTree→Block : ∀
  {block time outputs totalFees qtTransactions}
  (tree : TXTree time block outputs totalFees qtTransactions)
  → Dec (RawBlock tree)
txTree→Block genesisTree =
  no λ{(rawBlockc (blockc _ _ sndBlockCoinbase)) → sndBlockCoinbase}
txTree→Block (txtree tree tx proofLessQtTX)
  with isCoinbaseTree (txtree tree tx proofLessQtTX)
... | no ¬isCoinbase =
         no λ{ (rawBlockc (blockc _ _ coinbaseTree)) → ¬isCoinbase coinbaseTree}
... | yes isCoinbase = let fTree = firstTree (txtree tree tx proofLessQtTX)
                           nxTree = fstTree.nxTree fTree
                           fBlock = fstTree.fstBlockc fTree
                       in yes (rawBlockc (blockc nxTree fBlock isCoinbase))
\end{code}
%</treeblock>


\begin{code}
{-# TERMINATING #-}
\end{code}

%<*blockblockchain>
\begin{code}
block→blockchain : ∀
  {block₁ time₁ outputs₁ totalFees₁ qtTransactions₁}
  {txTree₁ : TXTree time₁ block₁ outputs₁ totalFees₁ qtTransactions₁}
  {time₂ outputs₂ totalFees₂ qtTransactions₂}
  {txTree₂ : TXTree time₂ block₁ outputs₂ totalFees₂ qtTransactions₂}
  (block : Block txTree₁ txTree₂)
  → Blockchain block
block→blockchain {_} {_} {_} {_} {_} {genesisTree}
  (blockc nxTree fstBlock₁ sndBlockCoinbase) =
  fstBlock (blockc nxTree unit sndBlockCoinbase)
block→blockchain {_} {_} {_} {_} {_} {txtree tree tx proofLessQtTX}
  (blockc nxTree fstBlock₁ sndBlockCoinbase)
  with firstTree tree
... | fstTreec nxTree₁ fstBlockc = addBlock
  (block→blockchain (blockc nxTree₁ fstBlockc (fstTree→coinbase fstBlock₁)))
  (blockc nxTree fstBlock₁ sndBlockCoinbase)
\end{code}
%</blockblockchain>
