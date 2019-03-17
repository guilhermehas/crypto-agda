module blockchain where

open import Prelude

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
hashList (x ∷ xs) = {!hash $ hash x + hashList xs!}

record SimpleBlock : Set where
  field
    transactions : List Transaction

hashBlock : SimpleBlock → Nat
hashBlock _ = 1

validBlock : SimpleBlock → Bool
validBlock _ = true

data GenesisBlock : Nat → Set where
  block : (n : Nat) → (sb : SimpleBlock) → n ≡ hashBlock sb → GenesisBlock n

data Block : Nat → Nat → Set where
  block : (n : Nat) → (m : Nat) → (sb : SimpleBlock) → m ≡ hashBlock sb → Block n m

data Blockchain : Nat → Set where
  gen : {n : Nat} → GenesisBlock n → Blockchain n
  cons : {n m : Nat} → Block n m → Blockchain n → Blockchain m

addBlock : {n : Nat} → (sb : SimpleBlock) → Blockchain n → Either (Blockchain n) (Blockchain (hashBlock sb))
addBlock {n} simpleBlock blockchain =
  let blockHash = hashBlock simpleBlock in
    if validBlock simpleBlock
      then
        (let newBlock = block n blockHash simpleBlock refl in Either.right $ cons newBlock blockchain)
      else
        Either.left blockchain
