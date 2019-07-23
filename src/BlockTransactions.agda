module BlockTransactions where

open import Prelude
open import Operators
open import Utils
open import Transactions

data _≠_ : ∀ {A : Set} → (x y : A) → Set where
  neq : ∀ {A : Set} {x y : A} → ¬ (x ≡ y) → x ≠ y

data isRegularTrans : Transaction → Set where
  reg : (idt prevId : Id) (sender : PubKey) (n : Nat)
    (receivers : Vec PubKey n) (amount : Nat) (recAmounts : +Vec amount n)
    → isRegularTrans (record {
        idTrans = idt
        ; prevId = just prevId
        ; sender = sender
        ; n = n
        ; receivers = receivers
        ; amount = amount
        ; recAmounts = recAmounts })

data BlockTransaction : Set where
  txCoinBase : (tx : Transaction) → ¬ (isRegularTrans tx) → BlockTransaction
  txNormal : (tx : Transaction) → isRegularTrans tx → BlockTransaction

tx→blockTx : (tx : Transaction) → BlockTransaction
tx→blockTx tx@(record { idTrans = idTrans ; prevId = nothing ; sender = sender ; n = n ; receivers = receivers ; amount = amount ; recAmounts = recAmounts }) = txCoinBase tx λ ()
tx→blockTx tx@(record { idTrans = idTrans ; prevId = (just x) ; sender = sender ; n = n ; receivers = receivers ; amount = amount ; recAmounts = recAmounts }) = txNormal tx (reg idTrans x sender n receivers amount recAmounts)

vtx→vblockTx : ∀ {n : Nat} → Vec Transaction n → Vec BlockTransaction n
vtx→vblockTx v = vmap tx→blockTx v

data isCoinBase : BlockTransaction → Set where
  coinBase : (tx : Transaction) (¬p : ¬ (isRegularTrans tx)) → isCoinBase (txCoinBase tx ¬p)

data distinct-params-trans : Transaction → Transaction → Set where
  dist-par-normal : ∀ {t t' : Transaction}
    → (isRegularTrans t) → (isRegularTrans t')
    → Transaction.idTrans t ≠ Transaction.idTrans t'
    → Transaction.prevId t ≠ Transaction.prevId t'
    → distinct-params-trans t t'
  dist-par-coinbase : ∀ {t t' : Transaction}
    → ¬ (isRegularTrans t)
    → Transaction.prevId t ≠ Transaction.prevId t'
    → distinct-params-trans t t'

data distinct-id : {n : Nat} → (el : Transaction) → Vec Transaction n → Set where
  distEmpty : (el : Transaction) → distinct-id el []
  distVec : {n : Nat} {x : Transaction} {xs : Vec Transaction n}
    → (el : Transaction) → distinct-params-trans el x
    → distinct-id el xs → distinct-id el (x ∷ xs)

data trans-uniq-ids : {n : Nat} → Vec BlockTransaction n → Set where
  [] : trans-uniq-ids []
  uniqv : ∀ {n : Nat} → (x : Transaction) → (xs : Vec Transaction n)
    → distinct-id x xs → trans-uniq-ids (vtx→vblockTx xs) → trans-uniq-ids (vtx→vblockTx (x ∷ xs))

prevId-regTrans : (tx : Transaction) (p : isRegularTrans tx) → Id
prevId-regTrans _ (reg idt prevId sender n receivers amount recAmounts) = prevId

data transIdBefore : ∀ {n : Nat} → BlockTransaction → Vec BlockTransaction n → Set where
  block : ∀ {n : Nat} {tx : BlockTransaction} {txs : Vec BlockTransaction n}
    → isCoinBase tx
    → transIdBefore tx txs
  here : ∀ {n : Nat} {tx tx' : Transaction}  {txs : Vec Transaction n}
    → (p : isRegularTrans tx)
    → prevId-regTrans tx p ≡ Transaction.idTrans tx'
    → transIdBefore (txNormal tx p) (vtx→vblockTx (tx' ∷ txs))
  there : ∀ {n : Nat} {tx tx' : Transaction}  {txs : Vec Transaction n}
    → (p : isRegularTrans tx)
    → transIdBefore (txNormal tx p) (vtx→vblockTx txs)
    → transIdBefore (txNormal tx p) (vtx→vblockTx (tx' ∷ txs))

data allTransIdsBefore : ∀ {n : Nat} → Vec BlockTransaction n → Set where
  [] : allTransIdsBefore []
  alltbef : {n : Nat}
    → (trans : BlockTransaction)
    → (vtrans : Vec BlockTransaction n)
    → allTransIdsBefore vtrans
    → transIdBefore trans vtrans
    → allTransIdsBefore (trans ∷ vtrans)

data rightTxs : ∀ {n : Nat} → Vec BlockTransaction n → Set where
  rtxs : ∀ {n : Nat} {txs : Vec BlockTransaction n}
    → trans-uniq-ids txs
    → allTransIdsBefore txs
    → rightTxs txs
