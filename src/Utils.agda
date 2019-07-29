module Utils where

open import Prelude
open import Data.Unit using (⊤; tt)
open import Operators

vmap : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → Vec A n → Vec B n
vmap f []       = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

++vec++ : ∀ {m n : Nat} {A : Set} → Vec (Vec A m) n → Vec A (n * m)
++vec++ [] = []
++vec++ (x ∷ xs) = x v++ ++vec++ xs

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

Amount = Nat

NonNil : ∀ {A : Set} → List A → Set
NonNil [] = ⊥
NonNil (_ ∷ _) = ⊤

data All {A : Set} : (P : A → Set) → List A → Set where
  [] : {P : A → Set} → All P []
  _∷_ : {x : A} {xs : List A} {P : A → Set} → P x → All P xs → All P (x ∷ xs)

data NonEmptyList : Set → Set where
  el : {A : Set} → A → NonEmptyList A
  _∷_ : {A : Set} → A → NonEmptyList A → NonEmptyList A

NonEmptyToList : {A : Set} → NonEmptyList A → List A
NonEmptyToList (el x) = x ∷ []
NonEmptyToList (x ∷ xs) = x ∷ NonEmptyToList xs

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
