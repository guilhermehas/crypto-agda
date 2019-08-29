module examples where

open import Prelude
open import Utils
open import Cripto
open import RawTransactions
open import Transactions
open import TXTree

txTree : RawTXTree
txTree = record
           { time = nat zero
           ; block = zero
           ; outputs = []
           ; txTree = genesisTree
           }

tx0 : RawTX
tx0 = coinbase (record { outputs = record
                                     { time = nat zero
                                     ; position = zero
                                     ; amount = 100
                                     ; address = nat zero
                                     } ∷ [] })


getOuts : (tx : RawTX) → List TXFieldWithId
getOuts (coinbase record { outputs = outputs }) = outputs
getOuts (normalTX record { inputs = inputs ; outputs = outputs }) = []

listOuts : TypeEl $ listTXField→VecOut $ getOuts tx0
listOuts = el
             (just
              (record
               { time = nat zero
               ; outSize = 1
               ; vecOut =
                   el
                   (record
                    { time = nat zero
                    ; position = zero
                    ; amount = 100
                    ; address = nat zero
                    })
                   refl refl
               ; proof = refl
               }))


txTree1El : TypeEl $ addTransactionTree txTree tx0
txTree1El = el (just
  (record
    { time = nat 1
    ; block = 1
    ; outputs =
    [
      record
      { time = nat zero
      ; position = 0
      ; amount = 100
      ; address = nat zero
      }
    ]
    ; txTree =
    txtree genesisTree
      (coinbase genesisTree
        (el
          (record
          { time = nat zero
          ; position = 0
          ; amount = 100
          ; address = nat zero
          })
          refl refl))
  }))

txTree1 = fromJust $ getElFromType txTree1El

tx1 : RawTX
tx1 = coinbase (record { outputs = record
  { time = nat 1
  ; position = zero
  ; amount = 20
  ; address = nat zero
  } ∷ [] })

txTree2El : TypeEl $ addTransactionTree txTree1 tx1
txTree2El = el (
  just
  (record
    { time = nat 2
    ; block = 2
    ; outputs =
        record
        { time = nat zero
        ; position = 0
        ; amount = 100
        ; address = nat zero
        }
        ∷
        [
        record
        { time = nat 1 ; position = 0 ; amount = 20 ; address = nat zero }
        ]
  ; txTree =
      txtree (RawTXTree.txTree txTree1)
      (coinbase (RawTXTree.txTree txTree1)
        (el
          (record
            { time = nat 1 ; position = 0 ; amount = 20 ; address = nat zero })
        refl refl))
  }))
