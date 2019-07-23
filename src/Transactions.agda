module Transactions where

open import Prelude
open import Operators
open import Utils

record Transaction : Set where
  field
    idTrans : Nat
    sender : PubKey
    n : Nat
    receivers : Vec PubKey n
    amount : Nat
    recAmounts : +Vec amount n

record RawTransaction : Set where
  field
    idTrans : Nat
    sender : PubKey
    receivers : List PubKey
    pubAmounts : List PubKey
    amounts : List Nat

data JoinedLists : Set where
  joined : {n : Nat} → Vec PubKey n → Vec PubKey n → Vec Nat n → JoinedLists
  nothing : JoinedLists

toJoined : List PubKey → List PubKey → List Nat → JoinedLists
toJoined [] [] (x ∷ v3) = nothing
toJoined [] (x ∷ v2) v3 = nothing
toJoined (x ∷ v1) [] v3 = nothing
toJoined (x ∷ v1) (x₁ ∷ v2) [] = nothing
toJoined [] [] [] = joined [] [] []
toJoined (x ∷ v1) (y ∷ v2) (z ∷ v3) with toJoined v1 v2 v3
... | joined va vb vc = joined (x ∷ va) (y ∷ vb) (z ∷ vc)
... | nothing = nothing

len : ∀ {a} {A : Set a} {n} → Vec A n → Nat
len {n = n} _ = n

toValidTransaction : RawTransaction → Maybe Transaction
toValidTransaction trans = toTrans
  where
    open RawTransaction trans
    toTrans : Maybe Transaction
    toTrans with toJoined receivers pubAmounts amounts
    ... | joined [] [] [] = just (record
                                      { idTrans = idTrans
                                      ; sender = sender
                                      ; n = 0
                                      ; receivers = []
                                      ; amount = 0
                                      ; recAmounts = []
                                      })
    ... | joined (r ∷ rec) (pam ∷ pubAmounts) (am ∷ amounts) with Vec→+Vec (am ∷ amounts)
    toTrans | joined (r ∷ rec) (pam ∷ pubAmounts) (am ∷ amounts) | +vec (_ ∷ vam) =
      just (record
              { idTrans =  idTrans
              ; sender = sender
              ; n = suc (len rec)
              ; receivers = r ∷ rec
              ; amount = am + +vecSum vam
              ; recAmounts = am ∷ vam
              })
    toTrans | nothing = nothing
