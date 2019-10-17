\begin{code}
module Cripto where

open import Prelude
open import Utils

data Time : Set where
  nat : Nat → Time

sucTime : Time → Time
sucTime (nat time) = nat (suc time)

timeToNat : Time → Nat
timeToNat (nat x) = x

timeToNatSuc : {time : Time} → timeToNat (sucTime time) ≡ suc (timeToNat time)
timeToNatSuc {nat x} = refl

ID = Nat

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
  _+msg_ : (m n : Msg) → Msg

infixr 5 _+msg_
\end{code}

%<*criptoPostulates>
\begin{code}
postulate _priv≡pub_ : PrivateKey → PublicKey → Set
postulate publicKey2Address : PublicKey → Address
postulate Signed : Msg → PublicKey → Signature → Set
postulate Signed? : (msg : Msg) (pk : PublicKey) (sig : Signature)
           → Dec $ Signed msg pk sig
postulate hashMsg : Msg → Hashed
postulate hash-inj : ∀ m n → hashMsg m ≡ hashMsg n → m ≡ n
\end{code}
%</criptoPostulates>

\begin{code}
record SignedWithSigPbk (msg : Msg)(address : Address) : Set where
  field
    publicKey   :  PublicKey
    pbkCorrect  :  publicKey2Address publicKey ≡ address
    signature   :  Signature
    signed      :  Signed msg publicKey signature


private
  _≡?addr_ : ∀ (a b : Address) → Dec $ a ≡ b
  nat zero ≡?addr nat zero = yes refl
  nat zero ≡?addr nat (suc b) = no (λ ())
  nat (suc a) ≡?addr nat zero = no (λ ())
  nat (suc a) ≡?addr nat (suc b) with nat a ≡?addr nat b
  ... | no ¬p = no λ{ refl → ¬p refl }
  ... | yes refl = yes refl

  _≟t_ : (a b : Time) → Dec $ a ≡ b
  nat a ≟t nat b with a == b
  ... | yes refl = yes refl
  ... | no ¬p    = no λ{ refl → ¬p refl }

instance
  eqTime : Eq Time
  _==_ {{eqTime}} = _≟t_

  eqAddress : Eq Address
  _==_ {{eqAddress}} = _≡?addr_
\end{code}
