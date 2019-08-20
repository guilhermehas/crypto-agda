module Ledger where

open import Prelude
open import Utils
open import Cripto
open import Transactions
open import RawTransactions
open import TXTree

ledgerOutNoId : ∀ (outputs : List TXField) (addr : Address)
  → Amount
ledgerOutNoId [] addr = zero
ledgerOutNoId (output ∷ outputs) addr with TXField.address output == addr
... | yes _ = TXField.amount output + ledgerOutNoId outputs addr
... | no  _ = ledgerOutNoId outputs addr

ledgerOut : ∀ (outputs : List TXFieldWithId) (addr : Address)
  → Amount
ledgerOut [] addr = zero
ledgerOut (output ∷ outputs) addr with TXFieldWithId.address output == addr
... | yes _ = TXFieldWithId.amount output + ledgerOut outputs addr
... | no  _ = ledgerOut outputs addr

ledgerTree : (rawTXTree : RawTXTree) (addr : Address) → Amount
ledgerTree txTree = ledgerOut outputs
  where open RawTXTree txTree

deltaRawTX : (tx : RawTX) (addr : Address) → Int
deltaRawTX (coinbase record { outputs = outputs }) = pos ∘ ledgerOut outputs
deltaRawTX (normalTX record { inputs = [] ; outputs = outputs }) addr =
  pos $ ledgerOutNoId outputs addr
deltaRawTX (normalTX record { inputs = (record { time = _ ; position = _ ; amount = amount ; msg = _ ;
  signature = _ ; publicKey = pk } ∷ inputs) ; outputs = outputs }) addr
  with addr == publicKey2Address pk
... | yes _ = deltaRawTX (normalTX (record { inputs = inputs ; outputs = outputs })) addr - pos amount
... | no  _ = deltaRawTX (normalTX (record { inputs = inputs ; outputs = outputs })) addr
