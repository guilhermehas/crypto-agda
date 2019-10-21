\begin{code}
module Transactions where

open import Prelude
open import Prelude.Nat.Properties
open import Utils
open import Cripto
\end{code}

%<*TXField>
\begin{code}
record TXField : Set where
  field
    amount  : Amount
    address : Address

record TXFieldWithId : Set where
    field
      time     : Time
      position : Nat
      amount   : Amount
      address  : Address
\end{code}
%</TXField>

\begin{code}
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
\end{code}

%<*VectorOutput>
\begin{code}
data VectorOutput : (time : Time) (size : Nat) (amount : Amount) → Set where
  el : ∀ {time : Time}
    (tx : TXFieldWithId)
    (sameId : TXFieldWithId.time tx ≡ time)
    (elStart : TXFieldWithId.position tx ≡ zero)
    → VectorOutput time 1 (TXFieldWithId.amount tx)

  cons : ∀ {time : Time} {size : Nat} {amount : Amount}
    (listOutput : VectorOutput time size amount)
    (tx : TXFieldWithId)
    (sameId : TXFieldWithId.time tx ≡ time)
    (elStart : TXFieldWithId.position tx ≡ size)
    → VectorOutput time (suc size) (amount + TXFieldWithId.amount tx)
\end{code}
%</VectorOutput>

\begin{code}
vecOutTime : ∀ {time : Time} {size : Nat} {amount : Amount}
  (vecOut : VectorOutput time size amount)
  → Time
vecOutTime {time} _ = time

VectorOutput→List : ∀ {time : Time} {size : Nat} {amount : Amount}
  (outs : VectorOutput time size amount)
  → List TXFieldWithId
VectorOutput→List (el tx sameId elStart) = tx ∷ []
VectorOutput→List (cons outs tx sameId elStart) = tx ∷ VectorOutput→List outs

nonNilVecOut : {time : Time} {size : Nat} {amount : Amount}
  (vecOut : VectorOutput time size amount)
  → NonNil (VectorOutput→List vecOut)
nonNilVecOut (el tx sameId elStart) = unit
nonNilVecOut (cons vecOut tx sameId elStart) = unit

vecOutDist : {time : Time} {size : Nat} {amount : Amount}
  (vecOut : VectorOutput time size amount)
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

    absurdEq : {a b : Nat} → ¬ (a ≡ suc (b + a))
    absurdEq {zero} ()
    absurdEq {suc a} {b} eq = absurdEq let neq = removeSuc≡ eq in trans neq (add-suc-r b a)

    ineq≢eq : {a b : Nat} → (a ≡ b) → (a < b) → ⊥
    ineq≢eq eq (diff! k) = absurdEq eq

    isDistSizeBelow : {amount : Amount}
      (lenVecOut : Nat)
      (lessThan : lenVecOut < suc size)
      (vOut : VectorOutput time lenVecOut amount)
      → isDistinct tx (VectorOutput→List vOut)
    isDistSizeBelow _ lessThan (el txOut sameId elStart2) =
      (λ { refl → ineq≢eq (trans (sym elStart2) elStart) (removeSuc< lessThan) }) , unit
    isDistSizeBelow (suc sizeVec) lessThan (cons vOut txOut sameId elStart2) =
      (λ { refl → ineq≢eq (trans (sym elStart2) elStart) (removeSuc< lessThan)}) ,
      isDistSizeBelow sizeVec (ineqAux lessThan) vOut


addOutput : ∀ {time : Time} {size : Nat} {amountOut : Amount}
  (listOutput : VectorOutput time size amountOut)
  (tx : TXField)
  → VectorOutput time (suc size) (amountOut + TXField.amount tx)
addOutput {time} {size} {amountOut} listOutput txOut = cons listOutput
  (record { time = time ; position = size ; amount = amount ; address = address })
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
txInput→Msg input [ output ] _ = TX→Msg output +msg TXId→Msg input
txInput→Msg input (output ∷ out2 ∷ outputs) _ = TX→Msg output +msg txInput→Msg input (out2 ∷ outputs) unit

txEls→Msg : ∀ {inputs : List TXFieldWithId}
  → (input : TXFieldWithId) → (outputs : List TXFieldWithId)
  → NonNil inputs × NonNil outputs → Msg
txEls→Msg input [] (_ , ())
txEls→Msg input (output ∷ outputs) _ = txInput→Msg input (map removeId (output ∷ outputs)) unit

txEls→MsgVecOut :
  {time      : Time}
  {outSize   : Nat}
  {outAmount : Amount}
  (input     : TXFieldWithId)
  (outputs   : VectorOutput time outSize outAmount)
   → Msg
txEls→MsgVecOut input (el tx sameId elStart) = TX→Msg (removeId tx) +msg TXId→Msg input
txEls→MsgVecOut input (cons outputs tx sameId elStart) =
  TX→Msg (removeId tx) +msg txEls→MsgVecOut input outputs

txFieldList→TotalAmount : (txs : List TXFieldWithId) → Amount
txFieldList→TotalAmount [] = zero
txFieldList→TotalAmount (x ∷ txs) = txFieldList→TotalAmount txs + amount x
  where open TXFieldWithId
\end{code}

%<*TXSigned>
\begin{code}
record TXSigned
  {time      : Time}
  {outSize   : Nat}
  {outAmount : Amount}
  (inputs    : List TXFieldWithId)
  (outputs   : VectorOutput time outSize outAmount) : Set where
  field
    nonEmpty : NonNil inputs
    signed   : All
      (λ input →
      SignedWithSigPbk (txEls→MsgVecOut input outputs)
                       (TXFieldWithId.address input))
                       inputs
    in≥out : txFieldList→TotalAmount inputs ≥n outAmount
\end{code}
%</TXSigned>

\begin{code}

record TXSignedRawOutput
  (inputs : List TXFieldWithId)
  (outputs : List TXFieldWithId) : Set where
  field
    nonEmpty : NonNil inputs × NonNil outputs
    signed   : All
      (λ input →
      SignedWithSigPbk (txEls→Msg input outputs nonEmpty)
                       (TXFieldWithId.address input))
                       inputs
    in≥out : txFieldList→TotalAmount inputs ≥n txFieldList→TotalAmount outputs

txSigInput : {inputs : List TXFieldWithId}
  {outputs : List TXFieldWithId}
  (tx : TXSignedRawOutput inputs outputs)
  → List TXFieldWithId
txSigInput {inputs} _ = inputs
\end{code}
