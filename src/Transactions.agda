module Transactions where

open import Prelude
open import Operators

hash : Nat → Nat
hash n = n

record Transaction : Set where
  field
    sender : Nat
    receiver : Nat
    amount : Nat

hashTransaction : Transaction → Nat
hashTransaction trans = hash $ hash (Transaction.sender trans) + hash (Transaction.receiver trans) + hash (Transaction.amount trans)

hashList : List Nat → Nat
hashList [] = 0
hashList (x ∷ xs) = hash $ hash x + hashList xs

record AccountMoney : Set where
  field
    account : Nat
    money : Nat

getNewListAccount  : Transaction → List AccountMoney → List AccountMoney
getNewListAccount trans [] = []
getNewListAccount trans (account' ∷ laccount) = {!(updateSender $ updateReceiver account') ∷ getNewListAccount trans laccount!}
  where
  updateSender : AccountMoney → AccountMoney
  updateSender account = 
    if Transaction.sender trans ≣ AccountMoney.account account
      then record account {money = AccountMoney.money account - Transaction.amount trans}
      else account

  updateReceiver : AccountMoney → AccountMoney
  updateReceiver account =
    if Transaction.receiver trans ≣ AccountMoney.account account
      then record account {money = AccountMoney.money account + Transaction.amount trans}
      else account

inTheMoney : Transaction → List AccountMoney → Set
inTheMoney trans [] = Transaction.amount trans ≡ 0
inTheMoney trans (account ∷ laccount) =
  if Transaction.sender trans ≣ AccountMoney.account account
    then
      Transaction.amount trans ≤ AccountMoney.money account
    else
      inTheMoney trans laccount

data ListTransactions : List AccountMoney → Set where
  emptyTrans : ListTransactions []
  consTrans : {laccount : List AccountMoney} → ListTransactions laccount → (trans : Transaction) → inTheMoney trans laccount → ListTransactions (getNewListAccount trans laccount)

validTransaction : List AccountMoney → Transaction → Bool
validTransaction [] transaction = false
validTransaction (acc ∷ xs) transaction =
     Transaction.sender transaction ≣ AccountMoney.account acc
  && Transaction.amount transaction <= AccountMoney.money acc
