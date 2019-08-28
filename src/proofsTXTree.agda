module proofsTXTree where

open import Prelude
open import Prelude.Nat.Properties
open import Utils
open import Cripto
open import Transactions
open import TXTree

_out<time_ : (out : TXFieldWithId) (time : Time) → Set
out out<time time = timeToNat (TXFieldWithId.time out) < timeToNat time

outputsTimeLess : {time : Time} {block : Nat} {outputs : List TXFieldWithId}
  (txTree : TXTree time block outputs)
  → All (λ output → output out<time time) outputs
outputsTimeLess genesisTree = []
outputsTimeLess (txtree {block} {time} {outSize} {outputs} {outVec} txTree tx) =
  allJoin (inputsTX tx) (VectorOutput→List outVec) (inputs≤→inputsTX tx $ outputsTimeLess txTree)
  $ vecOutTimeLess outVec
  where
    vecOutTimeLess : ∀ {time : Time} {outSize : Nat} (vecOut : VectorOutput time outSize)
      → All (λ output → output out<time (sucTime time)) (VectorOutput→List vecOut)
    vecOutTimeLess (el tx refl elStart) = (diff zero (timeToNatSuc {TXFieldWithId.time tx})) ∷ []
    vecOutTimeLess (cons {time} vecOut tx refl elStart) =
      (diff zero (timeToNatSuc {time})) ∷ (vecOutTimeLess vecOut)

    ≤timeSuc : {t1 : TXFieldWithId} {t2 : Time} (pt : t1 out<time t2) → t1 out<time (sucTime t2)
    ≤timeSuc {record { time = time ; position = position ; amount = amount ; address = address }}
      {nat .(suc (k + timeToNat time))} (diff! k) = diff! (suc k)

    inputs≤→inputsTX : {inputs : List TXFieldWithId}
      {tree : TXTree time block inputs}
      (tx : TX tree outVec)
      (allInps : All (λ output → output out<time time) inputs)
      → All (λ input → input out<time sucTime time) (inputsTX tx)
    inputs≤→inputsTX {[]} (normalTX tr [] outVec txSigned) [] = []
    inputs≤→inputsTX {[]} (coinbase tr outputs) [] = []
    inputs≤→inputsTX {input ∷ inputs} (normalTX tr (input ¬∷ SubInputs) outVec txSigned) (pt ∷ allInps) =
      ≤timeSuc {input} {time} pt ∷ allProofFG (λ y pf → ≤timeSuc {y} {time} pf)
      (allList→allSub SubInputs allInps)
    inputs≤→inputsTX {input ∷ inputs} (normalTX tr (input ∷ SubInputs) outVec txSigned) (x ∷ allInps) =
      allProofFG (λ y pf → ≤timeSuc {y} {time} pf) (allList→allSub SubInputs allInps)
    inputs≤→inputsTX {input ∷ inputs} (coinbase tr outVec) (pt ∷ allInps) = ≤timeSuc {input} {time} pt
      ∷ allProofFG (λ y pf → ≤timeSuc {y} {time} pf) allInps

inputsTimeLess : {time : Time} {block : Nat} {inputs : List TXFieldWithId} {outSize : Nat}
  {tr : TXTree time block inputs} {outputs : VectorOutput time outSize} (tx : TX tr outputs)
  → All (λ tx → tx out<time time) $ inputs
inputsTimeLess (normalTX tr SubInputs outputs txSigned) = outputsTimeLess tr
inputsTimeLess (coinbase tr outputs) = outputsTimeLess tr

inputsTXTimeLess : {time : Time} {block : Nat} {inputs : List TXFieldWithId} {outSize : Nat}
  {tr : TXTree time block inputs} {outputs : VectorOutput time outSize} (tx : TX tr outputs)
  → All (λ tx → tx out<time time) $ inputsTX tx
inputsTXTimeLess {time} {_} {inputs} (normalTX tr SubInputs outputs txSigned) =
  let proofInput = inputsTimeLess (normalTX tr SubInputs outputs txSigned) in
    allList→allSub SubInputs proofInput
inputsTXTimeLess {time} {_} {inputs} (coinbase tr outputs) = inputsTimeLess $ coinbase tr outputs

allVecOutSameTime : {time : Time} {size : Nat}
  (vecOut : VectorOutput time size) →
  All (λ tx → TXFieldWithId.time tx ≡ time) (VectorOutput→List vecOut)
allVecOutSameTime (el tx sameId elStart) = sameId ∷ []
allVecOutSameTime (cons vecOut tx sameId elStart) = sameId ∷ allVecOutSameTime vecOut

allDistincts : {time : Time} {vec< vec≡ : List TXFieldWithId}
  (all< : All (λ tx → tx out<time time) vec<)
  (all≡ : All (λ tx → TXFieldWithId.time tx ≡ time) vec≡)
  → twoListDistinct vec< vec≡
allDistincts {time} {.[]} {vec≡} [] all≡ = unit
allDistincts {time} {(x ∷ _)} {vec≡} (p< ∷ all<) all≡ = distinctLess all≡ , allDistincts all< all≡
  where
    sucRemove : ∀ {m n : Nat} (suc≡ : _≡_ {_} {Nat} (suc m) (suc n)) → m ≡ n
    sucRemove refl = refl

    ⊥-k+ : (k n : Nat) → ¬ (n ≡ suc k + n)
    ⊥-k+ k zero ()
    ⊥-k+ k (suc n) eqs = ⊥-k+ k n let eq = sucRemove eqs in trans eq (add-suc-r k n)

    ⊥-< : {n : Nat} → ¬ (n < n)
    ⊥-< {n} (diff k eq) = ⊥-k+ k n eq

    distinctLess : {vec≡ : List TXFieldWithId}
      (all≡ : All (λ tx → TXFieldWithId.time tx ≡ time) vec≡)
      → isDistinct x vec≡
    distinctLess [] = unit
    distinctLess (refl ∷ all≡) = (λ{ refl → ⊥-< p<}) , (distinctLess all≡)

mutual
  uniqueOutputs : {time : Time} {block : Nat} {outputs : List TXFieldWithId}
    (txTree : TXTree time block outputs) → Distinct outputs
  uniqueOutputs genesisTree = []
  uniqueOutputs (txtree {block} {time} {outSize} {inputs} {outVec} tree tx) = {!!}
    where
      distInputsOutVec : twoListDistinct (inputsTX tx) (VectorOutput→List outVec)
      distInputsOutVec = let inputsTimeLess = inputsTXTimeLess tx in allDistincts inputsTimeLess $
        allVecOutSameTime outVec

  distInputs : {time : Time} {block : Nat} {inputs : List TXFieldWithId} {outSize : Nat}
    {outVec : VectorOutput time outSize} {tree : TXTree time block inputs}
    (tx : TX tree outVec) → Distinct $ inputsTX tx
  distInputs (normalTX genesisTree [] outputs txSigned) = []
  distInputs (normalTX (txtree {_} {_} {_} {_} {vecOut} tr tx) SubInputs outputs txSigned) =
    distList→distSub {_} {_} {SubInputs} (unionDistinct {_} {inputsTX tx} {VectorOutput→List vecOut}
    (distInputs tx) (vecOutDist vecOut)
    (allDistincts (inputsTXTimeLess tx) (allVecOutSameTime vecOut)))
  distInputs (coinbase genesisTree outVec) = []
  distInputs (coinbase (txtree {_} {_} {_} {_} {vecOut} tr tx) outVec) =
    unionDistinct {_} {inputsTX tx} {VectorOutput→List vecOut} (distInputs tx)
    (vecOutDist vecOut) (allDistincts (inputsTXTimeLess tx) (allVecOutSameTime vecOut) )
