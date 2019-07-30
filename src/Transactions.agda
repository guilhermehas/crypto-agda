module Transactions where

open import Prelude
open import Operators
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

removeId : TXFieldWithId → TXField
removeId record { time = time ; position = position ; amount = amount ; address = address }
  = record { amount = amount ; address = address }

sameIdList : (time : Time) → (txs : NonEmptyList TXFieldWithId) → Set
sameIdList time (el tx)    =  TXFieldWithId.time tx ≡ time
sameIdList time (tx ∷ txs) = TXFieldWithId.time tx ≡ time × sameIdList time txs

incrementList : (order : Nat) → (txs : NonEmptyList TXFieldWithId) → Set
incrementList order (el tx) =  TXFieldWithId.position tx ≡ order
incrementList order (tx ∷ txs) =  TXFieldWithId.position tx ≡ order × incrementList (suc order) txs

data ListOutput : (time : Time) → Set where
  listOut : (time : Time) → (out : NonEmptyList TXFieldWithId)
    → sameIdList time out → incrementList zero out
    → ListOutput time

ListOutput→List : ∀ {time : Time} → (outs : ListOutput time) → List TXFieldWithId
ListOutput→List (listOut _ outs _ _) =  NonEmptyToList outs


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
    in≥out : txFieldList→TotalAmount inputs ≥ txFieldList→TotalAmount outputs
