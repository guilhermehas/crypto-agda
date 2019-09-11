\begin{code}
module RawTransactions where

open import Prelude
open import Utils
open import Cripto
open import Transactions


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


createVecOutsize : (tx : TXFieldWithId) → Maybe $ RawVecOutput (tx ∷ [])
createVecOutsize tx with TXFieldWithId.position tx == zero
... | no ¬p    = nothing
... | yes refl = just $ record { time = time ; outSize = 1 ;
  vecOut = el tx refl refl ; proof = refl }
  where open TXFieldWithId tx

listTXField→VecOut : (txs : List TXFieldWithId) → Maybe $ RawVecOutput txs
listTXField→VecOut [] = nothing
listTXField→VecOut (tx ∷ txs) with listTXField→VecOut txs
... | just vouts = addElementRawVec tx txs vouts
  where
    addElementInVectorOut : {time : Time} {outSize : Nat} (tx : TXFieldWithId)
      (vecOut : VectorOutput time outSize) → Maybe $ VectorOutput time $ suc outSize
    addElementInVectorOut {time} {outSize} tx vecOut with TXFieldWithId.time tx == time
    ... | no  ¬p   = nothing
    ... | yes refl with TXFieldWithId.position tx == suc outSize
    ...   | no    ¬p = nothing
    ...   | yes refl = just $ cons vecOut tx refl refl

    addElementRawVec : (tx : TXFieldWithId) (outs : List TXFieldWithId) (vecOut : RawVecOutput outs)
      → Maybe $ RawVecOutput (tx ∷ outs)
    addElementRawVec tx outs record { time = time ; outSize = outSize ; vecOut = vecOut ; proof = proof }
      with addElementInVectorOut tx vecOut
    ... | nothing  = nothing
    ... | just vec with TXFieldWithId.time tx == time
    ...   | no _     = nothing
    ...   | yes refl with TXFieldWithId.position tx == suc outSize
    ...     | no _     = nothing
    ...     | yes refl = just $ record { time = time ; outSize = suc outSize
      ; vecOut = cons vecOut tx refl refl ; proof = cong (_∷_ tx) proof }
... | nothing with txs == []
...   | no  _ = nothing
...   | yes p rewrite p = createVecOutsize tx

record TXSigAll (time : Time) (allInputs : List TXFieldWithId) : Set where
  field
    inputs   : List TXFieldWithId
    outSize  : Nat
    sub      : SubList allInputs
    outputs  : VectorOutput time outSize
    signed   : TXSigned (sub→list sub) (VectorOutput→List outputs)

rawTXSigned→TXSigAll : (time : Time) (allInputs : List TXFieldWithId)
  (rawTXSigned : RawTXSigned) → Maybe $ TXSigAll time allInputs
rawTXSigned→TXSigAll time allInputs record { outputs = outputs ; txSig = txSig }
  with listTXField→VecOut outputs
... | nothing     = nothing
... | just record { outSize = outSize ; vecOut = vecOut ;
  proof = proofVecOut } with list→subProof allInputs (txSigInput txSig)
...   | nothing  = nothing
...   | just record { sub = sub ; proof = proofSub } with vecOutTime vecOut == time
...     | no  _    = nothing
...     | yes refl   = just $ record
  { inputs = txSigInput txSig ; outSize = outSize ; sub = sub ; outputs = vecOut ; signed = txSigRes }
    where
      txSigRes : TXSigned (sub→list sub) (VectorOutput→List vecOut)
      txSigRes rewrite proofSub = txAux
        where
          txAux : TXSigned (txSigInput txSig) (VectorOutput→List vecOut)
          txAux rewrite proofVecOut = txSig
\end{code}
