module Blockchain where

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

record SimpleBlock : Set where
  field
    transactions : List Transaction

hashBlock : SimpleBlock → Nat
hashBlock block = hash $ sum $ map hashTransaction $ SimpleBlock.transactions block

data GenesisBlock : Nat → Set where
  block : (n : Nat) → (sb : SimpleBlock) → n ≡ hashBlock sb → GenesisBlock n

data Block : Nat → Nat → Set where
  block : (n : Nat) → (m : Nat) → (sb : SimpleBlock) → m ≡ hashBlock sb → Block n m

data Blockchain : Nat → Set where
  gen : {n : Nat} → GenesisBlock n → Blockchain n
  cons : {n m : Nat} → Block n m → Blockchain n → Blockchain m

validBlock : {n : Nat} → Blockchain n → SimpleBlock → Bool
validBlock _ _ = true

addBlock : {n : Nat} → (sb : SimpleBlock) → Blockchain n → Either (Blockchain n) (Blockchain (hashBlock sb))
addBlock {n} simpleBlock blockchain =
  let blockHash = hashBlock simpleBlock in
    if validBlock blockchain simpleBlock
      then
        (let newBlock = block n blockHash simpleBlock refl in Either.right $ cons newBlock blockchain)
      else
        Either.left blockchain

record AccountMoney : Set where
  field
    account : Nat
    money : Nat

validTransaction : List AccountMoney → Transaction → Bool
validTransaction [] transaction = false
validTransaction (acc ∷ xs) transaction =
     Transaction.sender transaction ≣ AccountMoney.account acc
  && Transaction.amount transaction <= AccountMoney.money acc
