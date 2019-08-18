module Transactions where

open import Prelude
open import Utils
open import Cripto

record TXField : Set where
  field
    amount : Amount
    address : Address

record TXFieldWithId : Set where
    field
      time     : Time
      position : Nat
      amount   : Amount
      address  : Address

private
  _≡txFieldWithId_ : (tx1 tx2 : TXFieldWithId) → Dec $ tx1 ≡ tx2
  record { time = time1 ; position = position1 ; amount = amount1 ; address = address1 }
    ≡txFieldWithId
    record { time = time2 ; position = position2 ; amount = amount2 ; address = address2 }
    with time1 == time2
  ... | no ¬eq = no λ {refl  → ¬eq refl}
  ... | yes refl with position1 == position2
  ... | no ¬eq   = no λ{ refl → ¬eq refl}
  ... | yes refl with amount1 == amount2
  ... | no ¬eq   = no λ{ refl → ¬eq refl}
  ... | yes refl with address1 == address2
  ... | no ¬eq   = no λ{ refl → ¬eq refl}
  ... | yes refl = yes refl

instance
  EqTXFieldWithId : Eq TXFieldWithId
  EqTXFieldWithId = record { _==_ = _≡txFieldWithId_ }

removeId : TXFieldWithId → TXField
removeId record { time = time ; position = position ; amount = amount ; address = address }
  = record { amount = amount ; address = address }

addId : (position : Nat) (time : Time) (txs : List TXField) → List TXFieldWithId
addId position time [] = []
addId position time (record { amount = amount ; address = address } ∷ txs)
  = record { time = time ; position = position ; amount = amount ; address = address } ∷ addId (suc position) time txs

sameIdList : (time : Time) → (txs : NonEmptyList TXFieldWithId) → Set
sameIdList time (el tx)    = TXFieldWithId.time tx ≡ time
sameIdList time (tx ∷ txs) = TXFieldWithId.time tx ≡ time × sameIdList time txs

incrementList : (order : Nat) → (txs : NonEmptyList TXFieldWithId) → Set
incrementList order (el tx) =  TXFieldWithId.position tx ≡ order
incrementList order (tx ∷ txs) =  TXFieldWithId.position tx ≡ order × incrementList (suc order) txs

data VectorOutput : (time : Time) (size : Nat) → Set where
  el : ∀ {time : Time} → (tx : TXFieldWithId) → (sameId : TXFieldWithId.time tx ≡ time)
    → (elStart : TXFieldWithId.position tx ≡ zero) → VectorOutput time 1
  cons : ∀ {time : Time} {size : Nat} → (listOutput : VectorOutput time size) → (tx : TXFieldWithId)
    → (sameId : TXFieldWithId.time tx ≡ time) → (elStart : TXFieldWithId.position tx ≡ (suc size))
    → VectorOutput time (suc size)

VectorOutput→List : ∀ {time : Time} {size : Nat} → (outs : VectorOutput time size)
  → List TXFieldWithId
VectorOutput→List (el tx sameId elStart) = tx ∷ []
VectorOutput→List (cons outs tx sameId elStart) = tx ∷ VectorOutput→List outs

addOutput : ∀ {time : Time} {size : Nat}
  → (listOutput : VectorOutput time size) → (tx : TXField) → VectorOutput time (suc size)
addOutput {time} {size} listOutput txOut = cons listOutput
  (record { time = time ; position = suc size ; amount = amount ; address = address })
  refl refl
  where open TXField txOut

TX→Msg : (tx : TXField) → Msg
TX→Msg record { amount = amount ; address = (nat address) } = nat amount +msg nat address

TXId→Msg : (tx : TXFieldWithId) → Msg
TXId→Msg record { time = (nat time) ; position = position ; amount = amount ; address = (nat address) }
  = nat time +msg nat position +msg nat amount +msg nat address

txInput→Msg : (input : TXFieldWithId) → (outputs : List TXField)
  → NonNil outputs → Msg
txInput→Msg input [] ()
txInput→Msg input (output ∷ outputs) _ with NonNil? outputs
... | yes nonNil =  TXId→Msg input +msg TX→Msg output +msg txInput→Msg input outputs nonNil
... | no nil = TXId→Msg input +msg TX→Msg output


txEls→Msg : ∀ {inputs : List TXFieldWithId}
  → (input : TXFieldWithId) → (outputs : List TXFieldWithId)
  → NonNil inputs × NonNil outputs → Msg
txEls→Msg input [] (_ , ())
txEls→Msg input (output ∷ outputs) _ = txInput→Msg input (map removeId (output ∷ outputs)) unit

txFieldList→TotalAmount : (txs : List TXFieldWithId) → Amount
txFieldList→TotalAmount txs = sum $ map amount txs
  where open TXFieldWithId

record TXSigned (inputs : List TXFieldWithId) (outputs : List TXFieldWithId) : Set where
  field
    nonEmpty : NonNil inputs × NonNil outputs
    signed   : All
      (λ input → SignedWithSigPbk (txEls→Msg input outputs nonEmpty) (TXFieldWithId.address input))
       inputs
    in≥out : txFieldList→TotalAmount inputs ≥n txFieldList→TotalAmount outputs

record RawTXSigned : Set where
  field
    inputs   : List TXFieldWithId
    outputs  : List TXFieldWithId
    txSig    : TXSigned inputs outputs

record RawInput : Set where
  field
    time      : Time
    position  : Nat
    amount    : Amount
    msg       : Msg
    signature : Signature
    publicKey : PublicKey

record RawTransaction : Set where
  field
    inputs   : List RawInput
    outputs  : List TXField

sigInput : (input : RawInput) → (outputs : List TXFieldWithId)
  → Maybe $ SignedWithSigPbk (RawInput.msg input) $ publicKey2Address $ RawInput.publicKey input
sigInput record { time = time ; position = position ; amount = amount ;
  msg = msg ; signature = signature ; publicKey = publicKey }
  outputs with Signed? msg publicKey signature
... | yes signed = just $ record
         { publicKey = publicKey ; pbkCorrect = refl ; signature = signature ; signed = signed }
... | no _ = nothing

raw→TXField : (input : RawInput) → TXFieldWithId
raw→TXField record { time = time ; position = position ; amount = amount ;
  msg = msg ; signature = signature ; publicKey = publicKey }
   = record { time = time ; position = position ; amount = amount ;
   address = publicKey2Address publicKey }

raw→TXSigned : ∀ (time : Time) → (ftx : RawTransaction)
  → Maybe RawTXSigned
raw→TXSigned time record { inputs = inputs ; outputs = outputs } with NonNil? inputs
... | no _ = nothing
... | yes nonNilInp with NonNil? outputs
...    | no _ = nothing
...    | yes nonNilOut = ans
  where
    inpsField : List TXFieldWithId
    inpsField = map raw→TXField inputs

    outsField : List TXFieldWithId
    outsField = addId zero time outputs

    nonNilMap : ∀ {A B : Set} {f : A → B} → (lista : List A) → NonNil lista → NonNil (map f lista)
    nonNilMap [] ()
    nonNilMap (_ ∷ _) nla = unit

    nonNilImpTX : NonNil inpsField
    nonNilImpTX = nonNilMap inputs nonNilInp

    nonNilAddId : {time : Time} (outputs : List TXField) (nonNilOut : NonNil outputs)
      → NonNil (addId zero time outputs)
    nonNilAddId [] ()
    nonNilAddId (_ ∷ outputs) nonNil = nonNil

    nonNilOutTX : NonNil outsField
    nonNilOutTX = nonNilAddId outputs nonNilOut

    nonEmpty : NonNil inpsField × NonNil outsField
    nonEmpty = nonNilImpTX , nonNilOutTX

    All?Signed : (inputs : List RawInput) →
        Maybe (All (λ input → SignedWithSigPbk (txEls→Msg input outsField nonEmpty)
        (TXFieldWithId.address input)) (map raw→TXField inputs))
    All?Signed [] = just []
    All?Signed (input ∷ inputs)
      with Signed? (txEls→Msg (raw→TXField input) outsField nonEmpty)
      (RawInput.publicKey input) (RawInput.signature input)
    ... | no _ = nothing
    ... | yes signed with All?Signed inputs
    ...    | nothing = nothing
    ...    | just allInputs = just $ (record
                                        { publicKey = RawInput.publicKey input
                                        ; pbkCorrect = refl
                                        ; signature = RawInput.signature input
                                        ; signed = signed
                                        }) ∷ allInputs

    in≥out : Dec $ txFieldList→TotalAmount inpsField ≥n txFieldList→TotalAmount outsField
    in≥out =  txFieldList→TotalAmount inpsField ≥n? txFieldList→TotalAmount outsField

    ans : Maybe RawTXSigned
    ans with All?Signed inputs
    ... | nothing = nothing
    ... | just signed with in≥out
    ...    | no _       = nothing
    ...    | yes in>out = just $ record { inputs = inpsField ; outputs = outsField ;
      txSig = record { nonEmpty = nonEmpty ; signed = signed ; in≥out = in>out } }

record RawTXCoinbase : Set where
  field
    outputs : List TXFieldWithId

data RawTX : Set where
  coinbase : (tx : RawTXCoinbase) → RawTX
  normalTX : (tx : RawTransaction)   → RawTX

record RawVecOutput (outputs : List TXFieldWithId) : Set where
  field
    time    : Time
    outSize : Nat
    vecOut  : VectorOutput time outSize
    proof   : VectorOutput→List vecOut ≡ outputs

listTXField→VecOut : (txs : List TXFieldWithId) → Maybe $ RawVecOutput txs
listTXField→VecOut [] = nothing
listTXField→VecOut (tx ∷ txs) = {!!}
  where
    addElementInVectorOut : {time : Time} {outSize : Nat} (tx : TXFieldWithId)
      (vecOut : VectorOutput time outSize) → Maybe $ VectorOutput time $ suc outSize
    addElementInVectorOut {time} {outSize} tx vecOut with TXFieldWithId.time tx == time
    ... | no  ¬p   = nothing
    ... | yes refl with TXFieldWithId.position tx == suc outSize
    ...   | no    ¬p = nothing
    ...   | yes refl = just $ cons vecOut tx refl refl

    createVecOutsize : (tx : TXFieldWithId) → Maybe $ RawVecOutput (tx ∷ [])
    createVecOutsize tx with TXFieldWithId.position tx == zero
    ... | no ¬p    = nothing
    ... | yes refl = just $ {!!}
      where open TXFieldWithId tx

    addElementRawVec : (tx : TXFieldWithId) (outs : List TXFieldWithId) (vecOut : RawVecOutput outs) → Maybe $ RawVecOutput outs
    addElementRawVec tx outs record { time = time ; outSize = outSize ; vecOut = vecOut }
      with addElementInVectorOut tx vecOut
    ... | nothing  = nothing
    ... | just vec = just $ {!!}

    addMaybeVec : (tx : TXFieldWithId) (outs : List TXFieldWithId) (vecOut : Maybe $ RawVecOutput outs) → Maybe $ RawVecOutput outs
    addMaybeVec tx outs nothing       = nothing
    addMaybeVec tx outs (just vecOut) = {!!}

record TXSigAll : Set where
  field
    time     : Time
    outSize  : Nat
    inputs   : List TXFieldWithId
    sub      : SubList inputs
    outputs  : VectorOutput time outSize
    signed   : TXSigned (sub→list sub) (VectorOutput→List outputs)

rawTXSigned→TXSigAll : (allInputs : List TXFieldWithId) (rawTXSigned : RawTXSigned) → Maybe TXSigAll
rawTXSigned→TXSigAll allInputs record { inputs = inputs ; outputs = outputs ; txSig = txSig }
  with listTXField→VecOut outputs
... | nothing     = nothing
... | just record { time = time ; outSize = outSize ; vecOut = vecOut ;
  proof = proofVecOut } with list→subProof allInputs inputs
...   | nothing  = nothing
...   | just record { sub = sub ; listSub = listSub ; proof = proofSub } = just $
  record
    { time = time
    ; outSize = outSize
    ; inputs = allInputs
    ; sub = sub
    ; outputs = vecOut
    ; signed = txSigRes
    }
    where
      txSigRes : TXSigned (sub→list sub) (VectorOutput→List vecOut)
      txSigRes rewrite proofSub = txAux
        where
          txAux : TXSigned listSub (VectorOutput→List vecOut)
          txAux rewrite proofVecOut = {!!}
