module Transactions where

open import Prelude
open import Prelude.Nat.Properties
open import Utils
open import Cripto

record TXField : Set where
  field
    amount : Amount
    address : Address

record TXFieldWithId : Set where
    field
      time     : Time
      position : Nat
      amount   : Amount
      address  : Address

private
  _≡txFieldWithId_ : (tx1 tx2 : TXFieldWithId) → Dec $ tx1 ≡ tx2
  record { time = time1 ; position = position1 ; amount = amount1 ; address = address1 }
    ≡txFieldWithId
    record { time = time2 ; position = position2 ; amount = amount2 ; address = address2 }
    with time1 == time2
  ... | no ¬eq = no λ {refl  → ¬eq refl}
  ... | yes refl with position1 == position2
  ... | no ¬eq   = no λ{ refl → ¬eq refl}
  ... | yes refl with amount1 == amount2
  ... | no ¬eq   = no λ{ refl → ¬eq refl}
  ... | yes refl with address1 == address2
  ... | no ¬eq   = no λ{ refl → ¬eq refl}
  ... | yes refl = yes refl

instance
  EqTXFieldWithId : Eq TXFieldWithId
  EqTXFieldWithId = record { _==_ = _≡txFieldWithId_ }

removeId : TXFieldWithId → TXField
removeId record { time = time ; position = position ; amount = amount ; address = address }
  = record { amount = amount ; address = address }

addId : (position : Nat) (time : Time) (txs : List TXField) → List TXFieldWithId
addId position time [] = []
addId position time (record { amount = amount ; address = address } ∷ txs)
  = record { time = time ; position = position ; amount = amount ; address = address }
  ∷ addId (suc position) time txs

sameIdList : (time : Time) → (txs : NonEmptyList TXFieldWithId) → Set
sameIdList time (el tx)    = TXFieldWithId.time tx ≡ time
sameIdList time (tx ∷ txs) = TXFieldWithId.time tx ≡ time × sameIdList time txs

incrementList : (order : Nat) → (txs : NonEmptyList TXFieldWithId) → Set
incrementList order (el tx) =  TXFieldWithId.position tx ≡ order
incrementList order (tx ∷ txs) =  TXFieldWithId.position tx ≡ order × incrementList (suc order) txs

data VectorOutput : (time : Time) (size : Nat) → Set where
  el : ∀ {time : Time} → (tx : TXFieldWithId) → (sameId : TXFieldWithId.time tx ≡ time)
    → (elStart : TXFieldWithId.position tx ≡ zero) → VectorOutput time 1
  cons : ∀ {time : Time} {size : Nat} → (listOutput : VectorOutput time size) → (tx : TXFieldWithId)
    → (sameId : TXFieldWithId.time tx ≡ time) → (elStart : TXFieldWithId.position tx ≡ (suc size))
    → VectorOutput time (suc size)

vecOutTime : ∀ {time : Time} {size : Nat} → (vecOut : VectorOutput time size) → Time
vecOutTime {time} _ = time

VectorOutput→List : ∀ {time : Time} {size : Nat} → (outs : VectorOutput time size)
  → List TXFieldWithId
VectorOutput→List (el tx sameId elStart) = tx ∷ []
VectorOutput→List (cons outs tx sameId elStart) = tx ∷ VectorOutput→List outs

vecOutDist : {time : Time} {size : Nat} (vecOut : VectorOutput time size)
  → Distinct $ VectorOutput→List vecOut
vecOutDist (el tx sameId elStart) = cons tx [] unit
vecOutDist {time} (cons {_} {size} vecOut tx sameId elStart)
  = cons tx (vecOutDist vecOut) (isDistSizeBelow size (diff! zero) vecOut)
  where
    zero≢sucSize : ¬ (_≡_ {lzero} {Nat} zero (suc size))
    zero≢sucSize ()

    removeSuc≡ : ∀ {a b : Nat} → _≡_ {lzero} {Nat} (suc a) (suc b) → a ≡ b
    removeSuc≡ refl = refl

    removeSuc< : ∀ {a b : Nat} → _<_ {lzero} {Nat} (suc a) (suc b) → a < b
    removeSuc< {a} (diff! k) = diff k (add-suc-r k a)

    ineqAux : {a b : Nat} → _<_ {lzero} {Nat} (suc a) (suc b) → a < suc b
    ineqAux {a} (diff! k) = diff (suc k) (cong suc (add-suc-r k a))

    isDistSizeBelow : (lenVecOut : Nat) (lessThan : lenVecOut < suc size)
      (vOut : VectorOutput time lenVecOut) → isDistinct tx (VectorOutput→List vOut)
    isDistSizeBelow .1 lessThan (el txOut sameId elStart2) =
      (λ { refl → zero≢sucSize (trans (sym elStart2) elStart)}) , unit
    isDistSizeBelow (suc sizeVec) lessThan (cons vOut txOut sameId elStart2) =
      (λ { refl → ineq≢eq (removeSuc≡ (trans (sym elStart2) elStart)) (removeSuc< lessThan)}) ,
      isDistSizeBelow sizeVec (ineqAux lessThan) vOut
      where
        absurdEq : {a b : Nat} → ¬ (a ≡ suc (b + a))
        absurdEq {zero} ()
        absurdEq {suc a} {b} eq = absurdEq let neq = removeSuc≡ eq in trans neq (add-suc-r b a)

        ineq≢eq : {a b : Nat} → (a ≡ b) → (a < b) → ⊥
        ineq≢eq eq (diff! k) = absurdEq eq


addOutput : ∀ {time : Time} {size : Nat}
  → (listOutput : VectorOutput time size) → (tx : TXField) → VectorOutput time (suc size)
addOutput {time} {size} listOutput txOut = cons listOutput
  (record { time = time ; position = suc size ; amount = amount ; address = address })
  refl refl
  where open TXField txOut

TX→Msg : (tx : TXField) → Msg
TX→Msg record { amount = amount ; address = (nat address) } = nat amount +msg nat address

TXId→Msg : (tx : TXFieldWithId) → Msg
TXId→Msg record { time = (nat time) ; position = position ; amount = amount ; address = (nat address) }
  = nat time +msg nat position +msg nat amount +msg nat address

txInput→Msg : (input : TXFieldWithId) → (outputs : List TXField)
  → NonNil outputs → Msg
txInput→Msg input [] ()
txInput→Msg input (output ∷ outputs) _ with NonNil? outputs
... | yes nonNil =  TXId→Msg input +msg TX→Msg output +msg txInput→Msg input outputs nonNil
... | no nil = TXId→Msg input +msg TX→Msg output


txEls→Msg : ∀ {inputs : List TXFieldWithId}
  → (input : TXFieldWithId) → (outputs : List TXFieldWithId)
  → NonNil inputs × NonNil outputs → Msg
txEls→Msg input [] (_ , ())
txEls→Msg input (output ∷ outputs) _ = txInput→Msg input (map removeId (output ∷ outputs)) unit

txFieldList→TotalAmount : (txs : List TXFieldWithId) → Amount
txFieldList→TotalAmount txs = sum $ map amount txs
  where open TXFieldWithId

record TXSigned (inputs : List TXFieldWithId) (outputs : List TXFieldWithId) : Set where
  field
    nonEmpty : NonNil inputs × NonNil outputs
    signed   : All
      (λ input → SignedWithSigPbk (txEls→Msg input outputs nonEmpty) (TXFieldWithId.address input))
       inputs
    in≥out : txFieldList→TotalAmount inputs ≥n txFieldList→TotalAmount outputs

txSigInput : ∀ {inputs : List TXFieldWithId} {outputs : List TXFieldWithId}
  (tx : TXSigned inputs outputs) → List TXFieldWithId
txSigInput {inputs} _ = inputs
