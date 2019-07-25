module Blockchain where

open import Prelude
open import Operators
open import Utils
open import Transactions


data SubList {A : Set} : List A → Set where
  []   : SubList []
  _¬∷_ : {xs : List A} → (x : A) → SubList xs → SubList (x ∷ xs)
  _∷_  : {xs : List A} → (x : A) → SubList xs → SubList (x ∷ xs)

sub→list : {A : Set} {xs : List A} → SubList xs → List A
sub→list [] = []
sub→list (x ¬∷ xs) = sub→list xs
sub→list (x ∷ xs) = x ∷ sub→list xs

list-sub : {A : Set} {xs : List A} → SubList xs → List A
list-sub [] = []
list-sub (x ¬∷ xs) = x ∷ list-sub xs
list-sub (x ∷ xs) = list-sub xs

record Block : Set where
  field
    coinbaseTX : TXUnsigned
    TXs : List normalTXrec

data TXOutputs : List TXField → Set where
  [] : TXOutputs []
  consCoinBase : {outs : List TXField} → (coinTX : TXField) → (txsOuts : TXOutputs outs)
    → TXOutputs (coinTX ∷ outs)
  consNormalTX : {outs : List TXField} → (inps : SubList outs) → (txsOuts : TXOutputs outs)
    → TXOutputs (list-sub inps)

data Blockchain : (xs : List TXField) → TXOutputs xs → Set where
  [] : Blockchain [] []
  -- cons : {outs : List TXField} → (txsOuts : TXOutputs outs)
  --   → (txs : normalTXrec) → (coinbase : TXField)
