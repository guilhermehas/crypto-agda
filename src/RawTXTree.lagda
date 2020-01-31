\begin{code}
module RawTXTree where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import RawTransactions
open import TXTree

dec< : (m n : Nat) → Dec $ IsTrue $ lessNat m n
dec< zero zero = no (λ ())
dec< zero (suc n) = yes true
dec< (suc m) zero = no (λ ())
dec< (suc m) (suc n) = dec< m n
\end{code}

%<*rawtxtree>
\begin{code}
record RawTXTree : Set where
  field
    time           : Time
    block          : Nat
    outputs        : List TXFieldWithId
    totalFees      : Amount
    qtTransactions : tQtTxs
    txTree         : TXTree time block outputs totalFees qtTransactions
\end{code}
%</rawtxtree>

\begin{code}
vecOut→Amount : {amount : Amount}
  {timeOut : Time} {outSize : Nat}
  (vecOut : VectorOutput timeOut outSize amount)
  → Amount
vecOut→Amount {amount} _ = amount
\end{code}

%<*addtxtree>
\begin{code}
addTransactionTree : (txTree : RawTXTree) (tx : RawTX) → Maybe RawTXTree
addTransactionTree record { time = time ; block = block ; outputs = outputs ;
  qtTransactions = qtTransactions ; totalFees = totalFees ; txTree = txTree }
  (coinbase record { outputs = outputsTX }) with listTXField→VecOut outputsTX
... | nothing     = nothing
... | just record { time = timeOut ; outSize = outSize ; vecOut = vecOut }
  with vecOut→Amount vecOut == totalFees + blockReward block
...   | no _ = nothing
...   | yes eqBlockReward
  with time == timeOut
...     | no _     = nothing
...     | yes refl = just $
  record { time = sucTime time ;
  block = nextBlock (coinbase txTree vecOut eqBlockReward) ;
  outputs = outputs ++ VectorOutput→List vecOut ;
  txTree = txtree txTree tx (right unit) }
  where
    tx : TX txTree vecOut
    tx = coinbase txTree vecOut eqBlockReward

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
...     | just record { outSize = outSize ; sub = sub ;
               outputs = outs ; signed = signed } =
  just $ record { time = sucTime time ;
         block = nextBlock (normalTX txTree sub outs signed) ;
  outputs = list-sub sub ++ VectorOutput→List outs ;
  txTree = txtree txTree (normalTX txTree sub outs signed) (left pLess) }
\end{code}
%</addtxtree>

\begin{code}
addMaybeTransTree : (txTree : Maybe RawTXTree) (tx : RawTX) → Maybe RawTXTree
addMaybeTransTree nothing tx = nothing
addMaybeTransTree (just tree) tx = addTransactionTree tree tx
\end{code}
