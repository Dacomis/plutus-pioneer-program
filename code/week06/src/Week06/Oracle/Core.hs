{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Week06.Oracle.Core
  ( Oracle (..),
    OracleRedeemer (..),
    oracleTokenName,
    oracleValue,
    oracleAsset,
    oracleInst,
    oracleValidator,
    oracleAddress,
    OracleSchema,
    OracleParams (..),
    runOracle,
    findOracle,
  )
where

import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Map as Map
import Data.Monoid (Last (..))
import Data.Text (Text, pack)
import GHC.Generics (Generic)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value as Value
import Plutus.Contract as Contract hiding (when)
import Plutus.Contracts.Currency as Currency
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), unless)
import Prelude (Semigroup (..))
import qualified Prelude

-- parameters of the contract
data Oracle = Oracle
  { oSymbol :: !CurrencySymbol, -- the CurrencySymbol of our NFT. We don't need the TokenName, as we'll just leave this empty.
    oOperator :: !PubKeyHash, -- the public key hash of the owner/operator of the Oracle (can do updates, and collect the fees)
    oFee :: !Integer, -- fees in lovelace per usage of the oracle
    oAsset :: !AssetClass -- what to exchange for our ADA (in this case this would be USD (represented as a Token, since USD of course does not exist on the Blockchain))
  }
  deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Oracle

-- this data type OracleRedeemer supports this 2 operations
data OracleRedeemer = Update | Use
  deriving (Show)

-- I use template Haskell to implement isData for the redeemer type
PlutusTx.unstableMakeIsData ''OracleRedeemer

-- use emptyByteString as the token name
{-# INLINEABLE oracleTokenName #-}
oracleTokenName :: TokenName
oracleTokenName = TokenName emptyByteString

-- a way to indentify the NFT asset class given the oracle - the asset of the NFT | to not be confused with the oAsset
{-# INLINEABLE oracleAsset #-}
oracleAsset :: Oracle -> AssetClass
oracleAsset oracle = AssetClass (oSymbol oracle, oracleTokenName) -- extracting the symbol from the oracle a and using the fixed token name

-- a helper funtion
{-# INLINEABLE oracleValue #-}
-- TxOut - output of the UTxO that holds the output
-- Maybe Monad -> the bind catches the effect that this could go wrong so the overall resoult can be nothing
oracleValue :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe Integer
oracleValue o f = do
  dh <- txOutDatum o -- this can fail because not any output has a datum | dh = datum hash
  Datum d <- f dh -- make the DatumHash into a datum - it can fail or succed | Datum is a type wrapper on type Data
  PlutusTx.fromData d -- maybe turn this Data d into an integer

{-# INLINEABLE mkOracleValidator #-}
-- Oracle -> parametrization of our Oracle Data type
-- Integer -> Our Datum, in this case the current exchange rate
-- OracleRedeemer -> use or update
-- ScriptContext -> should be clear by now
mkOracleValidator :: Oracle -> Integer -> OracleRedeemer -> ScriptContext -> Bool
mkOracleValidator oracle x r ctx =
  -- check that we have the input and the output that holds the NFT (inputHasToken/outputHasToken)
  traceIfFalse "Token missing from Input" inputHasToken
    && traceIfFalse "Token missing from Output" outputHasToken
    && case r of
      Update ->
        -- the case of Update
        traceIfFalse "Operator signature missing" (txSignedBy info $ oOperator oracle) -- the operator signed the transaction (txSignedBy) | oOprator gives the pubKeyHas of the oprator which is checked by the txSignedBy
          && traceIfFalse "Invalid output datum" validOutputDatum -- check if it carries valid integer as an outputDatum
      Use ->
        -- the case of Use that can be use by anybody but doesn't allow the datum to be changed (1st condition)
        traceIfFalse "Oracle value changed" (outputDatum == Just x) -- check if the outputDatum :: Maybe integer that is the new value == Just x = old value of the oracle
          && traceIfFalse "Fees not paid" feesPaid
  where
    -- takes the context end extracts the transacations info from it
    info :: TxInfo
    info = scriptContextTxInfo ctx

    -- retrieves the Oracle input using findOwnInput on our ScriptContext, or returns an error if none is found.
    ownInput :: TxOut
    ownInput = case findOwnInput ctx of -- findOwnInput gives the input given the context - it is a maybe
      Nothing -> traceError "Oracle Input missing" -- we should never end up here
      Just i -> txInInfoResolved i -- i = the input that is of type TxInput | txInInfoResolved gets the corresponding TxOut

    -- checks if the NFT exists exactly once in the UTxO input (ownInput), using assetClassValueOf which returns the amount of times the asset is present.
    inputHasToken :: Bool
    -- assetClassValueOf takes a value of type AssetClass and returns an integer which represents how many coins are contained in the Value
    -- Value = txOutValue ownInput - value attached tot the input I'm consuming
    -- AssetClass = oracleAsset oracle - gives the NFT belonging to the oracle
    -- I check how often the NFT is contained in the value of the oracle output | because is an NFt it shouldn't be more than one but it can be 0
    inputHasToken = assetClassValueOf (txOutValue ownInput) (oracleAsset oracle) == 1

    -- validating the consumation of the oracle outputs
    ownOutput :: TxOut
    -- getContinuingOutputs = gets the ctx and returns a list of all the outputs that go to the same script address that we're currently validating
    ownOutput = case getContinuingOutputs ctx of
      [o] -> o -- I want to be one oracle outputs
      _ -> traceError "Expected exactly one oracle Output"

    -- check if the Oracle Output (UTxO output) holds the NFT exactly once
    outputHasToken :: Bool
    -- similar to the inputHasToken but now I get the value from the ownOutput
    outputHasToken = assetClassValueOf (txOutValue ownOutput) (oracleAsset oracle) == 1

    -- check if the new value which is attached to the oracle output integer
    outputDatum :: Maybe Integer
    -- ownOutput = given a datumHash tries to give me a datum
    -- findDatum = takes the info and the datum hash and tries to look up the coresponding datum
    outputDatum = oracleValue ownOutput (`findDatum` info)

    -- take the outputDatum :: Maybe Integer and check that is not nothing aka is a just
    validOutputDatum :: Bool
    validOutputDatum = isJust outputDatum

    feesPaid :: Bool
    feesPaid =
      let inVal = txOutValue ownInput -- value that was attached to the oracle Input
          outVal = txOutValue ownOutput -- value that was attached to the oracle Output
          -- oracle Output geq that oracle Input + fees
          -- geq allow the user to give the operator a tip
       in outVal `geq` (inVal <> Ada.lovelaceValueOf (oFee oracle)) -- semigroup opration <> to combine values | lovelaceValueOf - transforms the integer to lovelace

-- helper type that combines the DatumType and the ReedemerType
data Oracling

instance Scripts.ScriptType Oracling where
  type DatumType Oracling = Integer
  type RedeemerType Oracling = OracleRedeemer

-- template Haskell to compile it to script instance
oracleInst :: Oracle -> Scripts.ScriptInstance Oracling
oracleInst oracle =
  Scripts.validator @Oracling
    -- because it is paratemerized I applyCode and lift the parameted into the Plutus script
    ($$(PlutusTx.compile [||mkOracleValidator||]) `PlutusTx.applyCode` PlutusTx.liftCode oracle)
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @Integer @OracleRedeemer

-- turn the script instance into a validator
oracleValidator :: Oracle -> Validator
oracleValidator = Scripts.validatorScript . oracleInst

-- turn the validator into an address
oracleAddress :: Oracle -> Ledger.Address
oracleAddress = scriptAddress . oracleValidator

data OracleParams = OracleParams
  { opFees :: !Integer,
    opSymbol :: !CurrencySymbol, -- the currency symbol of the asset we want to track not the NFT
    opToken :: !TokenName -- the token name of the asset we want to track not the NFT
  }
  deriving (Show, Generic, FromJSON, ToJSON)

-- this function mints the NFT which will be used throughout all functions
startOracle :: forall w s. HasBlockchainActions s => OracleParams -> Contract w s Text Oracle
startOracle op = do
  pkh <- pubKeyHash <$> Contract.ownPubKey
  -- mapError allows us to convert a Contract of type w s e a to a Contract ot type Contract of type w s e' a
  -- show -> turns the error into a string and pack turns into a text
  -- forgeContract allows us to mint NFTs
  -- [(oracleTokenName, 1)] the list of token names and quantities that I want
  osc <- mapError (pack . show) (forgeContract pkh [(oracleTokenName, 1)] :: Contract w s CurrencyError OneShotCurrency)
  let cs = Currency.currencySymbol osc -- gives the currencySymbol of the osc
      oracle =
        Oracle
          { oSymbol = cs,
            oOperator = pkh,
            oFee = opFees op,
            oAsset = AssetClass (opSymbol op, opToken op)
          }
  logInfo @String $ "Started Oracle " ++ show oracle
  return oracle

-- deals with 2 cases: 1) we have te oracle value; 2) we just started the oracle and there is no UTxO;
updateOracle :: forall w s. HasBlockchainActions s => Oracle -> Integer -> Contract w s Text ()
updateOracle oracle x = do
  m <- findOracle oracle
  -- Constraints.mustPayToTheScript x pays with the script using the Datum (x) by creating an output
  -- assetClassValue (oracleAsset oracle) 1 the value of our NFT
  let c = Constraints.mustPayToTheScript x $ assetClassValue (oracleAsset oracle) 1
  case m of
    Nothing -> do
      -- we didn't find UTxO, we just started the oracle but haven't provided an inital value
      ledgerTx <- submitTxConstraints (oracleInst oracle) c
      awaitTxConfirmed $ txId ledgerTx
      logInfo @String $ "Set initial Oracle value to" ++ show x
    Just (oref, o, _) -> do
      -- we already have an oracle UTxO
      let lookups =
            Constraints.unspentOutputs (Map.singleton oref o) -- gets a map of singletons key value pairs UTxOs that we want to consume
              <> Constraints.scriptInstanceLookups (oracleInst oracle) -- input side
              <> Constraints.otherScript (oracleValidator oracle) -- output side
              -- Constraints.mustSpendScriptOutput pays to te script by creating an a script input | Redeemer $ PlutusTx.toData Update - converts the Update to data and then to redeemer
          tx = c <> Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData Update)
      ledgerTx <- submitTxConstraintsWith @Oracling lookups tx
      awaitTxConfirmed $ txId ledgerTx
      logInfo @String $ "Updated Oralce value to" ++ show x

-- looks up the existing oracle UTxO - it can fail if the oracle is just started and there is no UTxO yet
findOracle :: forall w s. HasBlockchainActions s => Oracle -> Contract w s Text (Maybe (TxOutRef, TxOutTx, Integer)) -- TxOutRef = identifier of the UTxO; TxOutTx = the UTxO itself containing all the data; Integer = the current exchange rate
findOracle oracle = do
  utxos <- Map.filter f <$> utxoAt (oracleAddress oracle) -- either 0 or 1 elems
  return $ case Map.toList utxos of -- Map.toList converts a list to a lists of key-value pair
    [(oref, o)] -> do
      -- we find exactly one element
      -- oracleValue gets the TxOut (txOutTxOut o) and the corresponding datum by giving the datumHash
      -- txOutTxTx o gives the transaction with a txData field | the txData field is just a map from DatumHashes to Datums | Map.lookup dh looks up given hashes and returns nothing or the datum
      x <- oracleValue (txOutTxOut o) $ \dh -> Map.lookup dh $ txData $ txOutTxTx o
      return (oref, o, x)
    _ -> Nothing -- we don't find just an element
  where
    f :: TxOutTx -> Bool
    -- checks if the UTxO value (txOutValue $ txOutTxOut o) contains the NFT (oracleAsset oracle) == 1
    f o = assetClassValueOf (txOutValue $ txOutTxOut o) (oracleAsset oracle) == 1

type OracleSchema = BlockchainActions .\/ Endpoint "update" Integer

-- starts the oracle, tells the oracle and waits the new values and updates the oracle accordingly
runOracle :: OracleParams -> Contract (Last Oracle) OracleSchema Text ()
runOracle op = do
  oracle <- startOracle op -- starts the oracle
  -- tell passes info out of an contract - it expects Monoids types
  -- Last monoid - it's a type wrapped on Maybe - it remembers the last just value
  tell $ Last $ Just oracle
  go oracle
  where
    -- go loops forever in order to block the update endpoint and as soon as someone provides an integer (the new value) it will call the update oracle function with the new value and loop to go again
    go :: Oracle -> Contract (Last Oracle) OracleSchema Text a
    go oracle = do
      x <- endpoint @"update"
      updateOracle oracle x
      go oracle
