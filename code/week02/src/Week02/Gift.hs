{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Week02.Gift where

import Control.Monad hiding (fmap)
import Data.Map as Map
import Data.Text (Text)
import Data.Void (Void)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import qualified Ledger.Scripts as Scripts
import Playground.Contract (ensureKnownCurrencies, printJson, printSchemas, stage)
import Playground.TH (mkKnownCurrencies, mkSchemaDefinitions)
import Playground.Types (KnownCurrency (..))
import Plutus.Contract hiding (when)
import PlutusTx (Data (..))
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), unless)
import Text.Printf (printf)
import Prelude (Semigroup (..))

newtype MySillyRedeemer = MySillyRedeemer Integer
    deriving Show

PlutusTx.unstableMakeIsData ''MySillyRedeemer

{-# INLINABLE mkValidator #-}
mkValidator :: () -> MySillyRedeemer -> ValidatorCtx -> Bool
mkValidator () (MySillyRedeemer r) _ = traceIfFalse "wrong redeemer" $ r == 42

data Typed
instance Scripts.ScriptType Typed where
    type instance DatumType Typed = ()
    type instance RedeemerType Typed = MySillyRedeemer

inst :: Scripts.ScriptInstance Typed
inst = Scripts.validator @Typed
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @() @MySillyRedeemer

validator :: Validator
validator = Scripts.validatorScript inst

valHash :: Ledger.ValidatorHash
valHash = Scripts.validatorHash validator

scrAddress :: Ledger.Address
scrAddress = ScriptAddress valHash

type GiftSchema =
  BlockchainActions
    .\/ Endpoint "give" Integer
    .\/ Endpoint "grab" ()

give :: (HasBlockchainActions s, AsContractError e) => Integer -> Contract w s e ()
give amount = do
  let tx = mustPayToOtherScript valHash (Datum $ Constr 0 []) $ Ada.lovelaceValueOf amount
  ledgerTx <- submitTx tx
  void $ awaitTxConfirmed $ txId ledgerTx
  logInfo @String $ printf "made a gift of %d lovelace" amount

grab :: forall w s e. (HasBlockchainActions s, AsContractError e) => Contract w s e ()
grab = do
  utxos <- utxoAt scrAddress
  let orefs = fst <$> Map.toList utxos
      lookups =
        Constraints.unspentOutputs utxos
          <> Constraints.otherScript validator
      tx :: TxConstraints Void Void
      tx = mconcat [mustSpendScriptOutput oref $ Redeemer $ I 17 | oref <- orefs]
  ledgerTx <- submitTxConstraintsWith @Void lookups tx
  void $ awaitTxConfirmed $ txId ledgerTx
  logInfo @String $ "collected gifts"

endpoints :: Contract () GiftSchema Text ()
endpoints = (give' `select` grab') >> endpoints
  where
    give' = endpoint @"give" >>= give
    grab' = endpoint @"grab" >> grab

mkSchemaDefinitions ''GiftSchema

mkKnownCurrencies []