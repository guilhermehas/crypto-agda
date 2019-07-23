module Utils where

open import Prelude
open import Data.Unit using (⊤; tt)
open import Operators

mutual
  data DistinctList (A : Set) : (A → A → Set) → Set where
      emptyDL : {b : A → A → Set} → DistinctList A b
      consDL : {b : A → A → Set} → (dl : DistinctList A b) → (el : A) → distinctElement b dl el → DistinctList A b

  distinctElement : {A : Set} → (b : A → A → Set) → DistinctList A b → A → Set
  distinctElement f emptyDL el = ⊤
  distinctElement f (consDL lista el' _) el = ¬ (f el' el) ∧ distinctElement f lista el

data PubKey : Set where
  nat : (n : Nat) → PubKey

data +Vec : (s : Nat) (n : Nat) → Set where
  [] : +Vec 0 0
  _∷_ : {s : Nat} {n : Nat} → (el : Nat) → +Vec s n → +Vec (el + s) (suc n)

+vecSum : ∀ {s n : Nat} → +Vec s n → Nat
+vecSum {s} _ = s

data +VecHid : Nat → Set where
  +vec : ∀ {s n : Nat} → +Vec s n → +VecHid n

Vec→+Vec : {n : Nat} → Vec Nat n → +VecHid n
Vec→+Vec [] = +vec []
Vec→+Vec (x ∷ v) with Vec→+Vec v
... | +vec +v = +vec (x ∷ +v)

data Msg : Set where
  nat : (n : Nat) → Msg
  _+msg_ : (n : Nat) → Msg

infixl 5 _⊕_

_⊕_ : Nat → Nat → Nat
n ⊕ m = ⊥-elim impossible
  where postulate impossible : ⊥

hash : Nat → Nat
hash n = n

hash-inj : ∀ m n → hash n ≡ hash m → n ≡ m
hash-inj n m = λ z → z

postulate hash-sum-inj : ∀ m m' n n' → hash m ⊕ hash n ≡ hash m' ⊕  hash n' → m ≡ m' × n ≡ n'

hashVec : {n : Nat} → Vec Nat n → Nat
hashVec [] = hash 0
hashVec (x ∷ vec) = hash x ⊕ hashVec vec

hashPub : PubKey → Nat
hashPub (nat n) = hash n

hashVecPub : {n : Nat} → Vec PubKey n → Nat
hashVecPub vec = hashVec (fmap (λ{ (nat n) → n}) vec)
