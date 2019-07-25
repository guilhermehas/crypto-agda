module Transactions where

open import Prelude
open import Operators
open import Utils
open import Cripto

record TXField : Set where
  field
    amount : Amount
    address : Address

open TXField

txFieldList2TotalAmount : (inp : NonEmptyList TXField) → Amount
txFieldList2TotalAmount inp = sum $ map amount $ NonEmptyToList inp

record TXUnsigned : Set where
  field
    inputs  : NonEmptyList TXField
    outputs : NonEmptyList TXField

open TXUnsigned

txField2Msg : (inp : TXField) → Msg
txField2Msg record { amount = amount ; address = (nat addr) } =
  nat amount +msg nat addr

txFieldList2Msg : (inps : NonEmptyList TXField) → Msg
txFieldList2Msg (el record { amount = amount ; address = (nat addr) }) =
  nat amount +msg nat addr
txFieldList2Msg (record { amount = amount ; address = nat addr } ∷ inps) =
  nat amount +msg nat addr +msg txFieldList2Msg inps

txInput2Msg : (inp : TXField) (outp : NonEmptyList TXField) → Msg
txInput2Msg inp outp = txField2Msg inp +msg txFieldList2Msg outp

tx2Sign : TXUnsigned → Set
tx2Sign tx = All signedInput $ NonEmptyToList $ inputs tx
  where
    signedInput : TXField → Set
    signedInput inp = SignedWithSigPbk (txInput2Msg inp (outputs tx)) (address inp)

record TX : Set where
  field
    tx : TXUnsigned
    in≥out : txFieldList2TotalAmount (inputs tx) ≥ txFieldList2TotalAmount (outputs tx)
    sig : tx2Sign tx
