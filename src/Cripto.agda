module Cripto where

open import Prelude

data Time : Set where
  nat : Nat → Time

data PublicKey : Set where
  nat : Nat → PublicKey

data Address : Set where
  nat : Nat → Address

data PrivateKey : Set where
  nat : Nat → PrivateKey

data Signature : Set where
  nat : Nat → Signature

data Hashed : Set where
  nat : Nat → Hashed

data Msg : Set where
  nat : (n : Nat) → Msg
  _+msg_ : (m : Msg) (n : Msg) → Msg

infixr 5 _+msg_

postulate _priv≡pub_ : PrivateKey → PublicKey → Set
postulate publicKey2Address : PublicKey → Address
postulate Signed : Msg → PublicKey → Signature → Set
postulate hashMsg : Msg → Hashed
postulate hash-inj : ∀ m n → hashMsg m ≡ hashMsg n → m ≡ n

record SignedWithSigPbk (msg : Msg)(address : Address) : Set where
  field
    publicKey   :  PublicKey
    pbkCorrect  :  publicKey2Address publicKey ≡ address
    signature   :  Signature
    signed      :  Signed msg publicKey signature
