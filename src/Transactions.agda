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
      address  : Amount

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

record TXSigned (inputs : List TXFieldWithId) (output : List TXFieldWithId) : Set where
  field
    val : Nat

open TXField

txFieldList2TotalAmount : (inp : NonEmptyList TXField) → Amount
txFieldList2TotalAmount inp = sum $ map amount $ NonEmptyToList inp

record TXUnsigned : Set where
  field
    inputs  : NonEmptyList TXField
    outputs : NonEmptyList TXField

open TXUnsigned

-- txField2Msg : (inp : TXField) → Msg
-- txField2Msg record { amount = amount ; address = (nat addr) } =
--   nat amount +msg nat addr

-- txFieldList2Msg : (inps : List TXField) → Msg
-- txFieldList2Msg [] = ept
-- txFieldList2Msg (inp ∷ inps) = txField2Msg inp +msg txFieldList2Msg inps

-- txFieldList2MsgN : (inps : NonEmptyList TXField) → Msg
-- txFieldList2MsgN (el record { amount = amount ; address = (nat addr) }) =
--   nat amount +msg nat addr
-- txFieldList2MsgN (record { amount = amount ; address = nat addr } ∷ inps) =
--   nat amount +msg nat addr +msg txFieldList2MsgN inps

-- txInput2Msg : (inp : TXField) (outp : List TXField) → Msg
-- txInput2Msg inp outp = txField2Msg inp +msg txFieldList2Msg outp

-- txInput2MsgN : (inp : TXField) (outp : NonEmptyList TXField) → Msg
-- txInput2MsgN inp outp = txField2Msg inp +msg txFieldList2MsgN outp

-- tx2Sign : List TXField → List TXField → Set
-- tx2Sign inputs outputs = All signedInput $ inputs
--   where
--     signedInput : TXField → Set
--     signedInput inp = SignedWithSigPbk (txInput2Msg inp outputs) (address inp)

-- tx2SignN : TXUnsigned → Set
-- tx2SignN tx = All signedInput $ NonEmptyToList $ inputs tx
--   where
--     signedInput : TXField → Set
--     signedInput inp = SignedWithSigPbk (txInput2MsgN inp (outputs tx)) (address inp)

-- record normalTXrec : Set where
--   field
--     tx : TXUnsigned
--     in≥out : txFieldList2TotalAmount (inputs tx) ≥ txFieldList2TotalAmount (outputs tx)
--     sig : tx2SignN tx

-- data TX : Set where
--   normalTX : normalTXrec → TX
--   coinbase : TXField → TX
