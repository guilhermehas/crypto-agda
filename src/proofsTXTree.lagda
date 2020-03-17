\begin{code}
module proofsTXTree where

open import Prelude
open import Prelude.Nat.Properties
open import Utils
open import Crypto
open import Transactions
open import TXTree

_out<time_ : (out : TXFieldWithId) (time : Time) → Set
out out<time time = timeToNat (TXFieldWithId.time out) < timeToNat time
\end{code}

%<*outtimeless>
\begin{code}
outputsTimeLess :
  {time : Time}
  {block : Nat}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (txTree : TXTree time block outputs totalFees qtTransactions )
  → All (λ output → output out<time time) outputs
outputsTimeLess genesisTree = []
outputsTimeLess {_} {_} {_} {totalFees} {qtTransactions}
  (txtree {block} {time} {amount} {outSize} {outputs} {outVec} txTree tx _) =
  allJoin (inputsTX tx) (VectorOutput→List outVec)
  (inputsTree→inputsTXtx tx $ outputsTimeLess txTree)
  $ vecOutTimeLess outVec
  where
    vecOutTimeLess : {time : Time}
      {outSize : Nat}
      {amount : Amount}
      (vecOut : VectorOutput time outSize amount)
      → All (λ output → output out<time (sucTime time))
      (VectorOutput→List vecOut)
    vecOutTimeLess (el tx refl elStart) =
      (diff zero (timeToNatSuc {TXFieldWithId.time tx})) ∷ []
    vecOutTimeLess (cons {time} vecOut tx refl elStart) =
      (diff zero (timeToNatSuc {time})) ∷ (vecOutTimeLess vecOut)

    ≤timeSuc : {t1 : TXFieldWithId} {t2 : Time} (pt : t1 out<time t2)
      → t1 out<time (sucTime t2)
    ≤timeSuc {txfieldid time position amount address} {t2}
      (diff k eq) = diff (suc k) (trans (eqTimeNat {t2}) eqsuc)
      where
        eqsuc : _≡_ {_} {Nat} (suc (timeToNat t2))
          (suc (suc (k + timeToNat time)))
        eqsuc = cong suc eq

        eqTimeNat : {t2 : Time} → timeToNat (sucTime t2) ≡ suc (timeToNat t2)
        eqTimeNat {nat zero} = refl
        eqTimeNat {nat (suc x)} = refl

    inputsTree→inputsTXtx : {inputs : List TXFieldWithId}
      {totalFees : Amount}
      {qtTransactions : Fin totalQt}
      {tree : TXTree time block inputs totalFees qtTransactions}
      (tx : TX tree outVec)
      (allInps : All (λ output → output out<time time) inputs)
      → All (λ input → input out<time sucTime time) (inputsTX tx)
    inputsTree→inputsTXtx {[]} (normalTX tr [] outVec txSigned) [] = []
    inputsTree→inputsTXtx {[]} (coinbase tr outputs _) [] = []
    inputsTree→inputsTXtx {input ∷ inputs} (normalTX tr (input ¬∷ SubInputs)
      outVec txSigned) (pt ∷ allInps) =
      ≤timeSuc {input} {time} pt ∷ allProofFG (λ y pf → ≤timeSuc {y} {time} pf)
      (allList→allSub SubInputs allInps)
    inputsTree→inputsTXtx {input ∷ inputs} (normalTX tr (input ∷ SubInputs)
      outVec txSigned) (x ∷ allInps) =
      allProofFG (λ y pf → ≤timeSuc {y} {time} pf)
      (allList→allSub SubInputs allInps)
    inputsTree→inputsTXtx {input ∷ inputs} (coinbase tr outVec _)
      (pt ∷ allInps) = ≤timeSuc {input} {time} pt
      ∷ allProofFG (λ y pf → ≤timeSuc {y} {time} pf) allInps
\end{code}
%</outtimeless>

%<*inptimeless>
\begin{code}
inputsTimeLess : {time : Time}
  {block : Nat}
  {inputs : List TXFieldWithId}
  {outSize : Nat}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  {outAmount : Amount}
  {tr : TXTree time block inputs totalFees qtTransactions}
  {outputs : VectorOutput time outSize outAmount}
  (tx : TX tr outputs)
  → All (λ tx → tx out<time time) $ inputs
inputsTimeLess (normalTX tr SubInputs outputs txSigned) = outputsTimeLess tr
inputsTimeLess (coinbase tr outputs pAmountFee) = outputsTimeLess tr
\end{code}
%</inptimeless>

%<*inptxtimeless>
\begin{code}
inputsTXTimeLess : {time : Time}
  {block : Nat}
  {inputs : List TXFieldWithId}
  {outSize : Nat}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  {outAmount : Amount}
  {tr : TXTree time block inputs totalFees qtTransactions}
  {outputs : VectorOutput time outSize outAmount}
  (tx : TX tr outputs)
  → All (λ tx → tx out<time time) $ inputsTX tx
inputsTXTimeLess {time} {_} {inputs} (normalTX tr SubInputs outputs txSigned) =
  let proofInput = inputsTimeLess (normalTX tr SubInputs outputs txSigned) in
    allList→allSub SubInputs proofInput
inputsTXTimeLess {time} {_} {inputs} (coinbase tr outputs pAmountFee) =
  inputsTimeLess $ coinbase tr outputs pAmountFee
\end{code}
%</inptxtimeless>

%<*allvecoutsametime>
\begin{code}
allVecOutSameTime : {time : Time}
  {size : Nat}
  {outAmount : Amount}
  (vecOut : VectorOutput time size outAmount) →
  All (λ tx → TXFieldWithId.time tx ≡ time) (VectorOutput→List vecOut)
allVecOutSameTime (el tx sameId elStart) = sameId ∷ []
allVecOutSameTime (cons vecOut tx sameId elStart) =
  sameId ∷ allVecOutSameTime vecOut
\end{code}
%</allvecoutsametime>

%<*alldists>
\begin{code}
allDistincts : {time : Time} {vec< vec≡ : List TXFieldWithId}
  (all< : All (λ tx → tx out<time time) vec<)
  (all≡ : All (λ tx → TXFieldWithId.time tx ≡ time) vec≡)
  → twoListDistinct vec< vec≡
allDistincts {time} {.[]} {vec≡} [] all≡ = unit
allDistincts {time} {(x ∷ _)} {vec≡} (p< ∷ all<) all≡ =
  distinctLess all≡ , allDistincts all< all≡
  where
    sucRemove : ∀ {m n : Nat} (suc≡ : _≡_ {_} {Nat}
      (suc m) (suc n)) → m ≡ n
    sucRemove refl = refl

    ¬n≡suck+n : (k n : Nat) → ¬ (n ≡ suc k + n)
    ¬n≡suck+n k zero ()
    ¬n≡suck+n k (suc n) eqs = ¬n≡suck+n k n let eq = sucRemove eqs in
      trans eq (add-suc-r k n)

    ¬n<n : {n : Nat} → ¬ (n < n)
    ¬n<n {n} (diff k eq) = ¬n≡suck+n k n eq

    distinctLess : {vec≡ : List TXFieldWithId}
      (all≡ : All (λ tx → TXFieldWithId.time tx ≡ time) vec≡)
      → isDistinct x vec≡
    distinctLess [] = unit
    distinctLess (refl ∷ all≡) = (λ{ refl → ¬n<n p<}) , (distinctLess all≡)
\end{code}
%</alldists>

%<*distinps>
\begin{code}
distInputs : {time : Time}
  {block : Nat}
  {inputs : List TXFieldWithId}
  {outSize : Nat}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  {outAmount : Amount}
  {tree : TXTree time block inputs totalFees qtTransactions}
  {outVec : VectorOutput time outSize outAmount}
  (tx : TX tree outVec)
  → Distinct $ inputsTX tx
distInputs (normalTX genesisTree [] outputs txSigned) = []
distInputs (normalTX (txtree {_} {_} {_} {_} {_} {vecOut} tr tx _)
  SubInputs outputs txSigned) =
  distList→distSub {_} {_} {SubInputs} (unionDistinct {_} {inputsTX tx}
  (distInputs tx) (vecOutDist vecOut)
  (allDistincts (inputsTXTimeLess tx) (allVecOutSameTime vecOut)))
distInputs (coinbase genesisTree outVec _) = []
distInputs (coinbase
  (txtree {_} {_} {_} {_} {_} {vecOut} tr tx _) outVec _) =
  unionDistinct {_} {inputsTX tx} (distInputs tx)
  (vecOutDist vecOut)
  (allDistincts (inputsTXTimeLess tx) (allVecOutSameTime vecOut) )
\end{code}
%</distinps>

%<*uniqueouts>
\begin{code}
uniqueOutputs : {time : Time}
  {block : Nat}
  {outputs : List TXFieldWithId}
  {totalFees : Amount}
  {qtTransactions : tQtTxs}
  (txTree : TXTree time block outputs totalFees qtTransactions)
  → Distinct outputs
uniqueOutputs genesisTree = []
uniqueOutputs (txtree {block} {time} {outSize} {inputs} {_} {vecOut} tree tx _) =
  unionDistinct {_} {inputsTX tx} {VectorOutput→List vecOut}
  (distInputs tx) (vecOutDist vecOut)
  (allDistincts (inputsTXTimeLess tx) (allVecOutSameTime vecOut))
\end{code}
%</uniqueouts>
