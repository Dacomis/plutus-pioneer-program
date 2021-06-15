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

module Week06.Oracle.Swap
  ( SwapSchema,
    swap,
  )
where

import Control.Monad hiding (fmap)
import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Monoid (Last (..))
import Data.Text (Text)
import Ledger hiding (singleton)
import Ledger.Ada as Ada hiding (divide)
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value as Value
import Plutus.Contract as Contract hiding (when)
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), find, mapMaybe, unless, (<$>))
import Week06.Oracle.Core
import Week06.Oracle.Funds
import Prelude (Semigroup (..), (<$>))

{-# INLINEABLE price #-}
price :: Integer -> Integer -> Integer
price lovelace exchangeRate = (lovelace * exchangeRate) `divide` 1000000 -- $1 = 1.000.000 of tokens

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue -- Ada.fromValue gets the amount of Ada from a value | Ada.getLovelace gets the amount of Lovelaces

{-# INLINEABLE mkSwapValidator #-}
-- Oracle is imported from the Core module | Address is the address of the oracle | Datum = PubKeyHash of the seller which will receive the price
mkSwapValidator :: Oracle -> Address -> PubKeyHash -> () -> ScriptContext -> Bool
mkSwapValidator oracle addr pkh () ctx =
  txSignedBy info pkh -- check if the seller signs the transaction
    || ( traceIfFalse "Expected exactly two script inputs" hasTwoScriptInputs -- there are exactly 2 scripts inputs: oracle and the swap UTxO
           && traceIfFalse "Price not paid" sellerPaid -- checks if the seller gets paid
       )
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    oracleInput :: TxOut
    oracleInput =
      let ins =
            [ o
              | i <- txInfoInputs info, -- i an input from the list of inputs
                let o = txInInfoResolved i, -- compute the corresponding outputs based on the i
                txOutAddress o == addr -- I filter the outputs by making sure the address is the address of the oracle
            ] -- list comprehension
       in case ins of
            [o] -> o -- check that is exactly one oracle output
            _ -> traceError "Expected exactly one oracle input"

    oracleValue' = case oracleValue oracleInput (`findDatum` info) of
      Nothing -> traceError "Oracle value not found"
      Just x -> x

    hasTwoScriptInputs :: Bool
    hasTwoScriptInputs =
      -- txInInfoResolved => the output to the input | txOutAddress => the addres of the output | toValidatorHash => validatorHash if it's a scriptOutput or nothing if it's a plublicKeyOutput 
      let xs = filter (isJust . toValidatorHash . txOutAddress . txInInfoResolved) $ txInfoInputs info -- xs = all the script inputs
       in length xs == 2 -- xs shpuld contain the oracle script and the swap script

    minPrice :: Integer
    minPrice =
      let lovelaceIn = case findOwnInput ctx of -- findOwnInput => input that has just been validated aka the swap input
            Nothing -> traceError "Own input not found"
            Just i -> lovelaces $ txOutValue $ txInInfoResolved i
       in price lovelaceIn oracleValue'

    sellerPaid :: Bool
    sellerPaid =
      let pricePaid :: Integer
          pricePaid = assetClassValueOf (valuePaidTo info pkh) (oAsset oracle) -- valuePaidTo adds up all the values of all the pk outputs that goes to the seller 
       in pricePaid >= minPrice

data Swapping

instance Scripts.ScriptType Swapping where
  type DatumType Swapping = PubKeyHash
  type RedeemerType Swapping = ()

swapInst :: Oracle -> Scripts.ScriptInstance Swapping
swapInst oracle =
  Scripts.validator @Swapping
    ( $$(PlutusTx.compile [||mkSwapValidator||])
        `PlutusTx.applyCode` PlutusTx.liftCode oracle
        `PlutusTx.applyCode` PlutusTx.liftCode (oracleAddress oracle)
    )
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @PubKeyHash @()

swapValidator :: Oracle -> Validator
swapValidator = Scripts.validatorScript . swapInst

swapAddress :: Oracle -> Ledger.Address
swapAddress = scriptAddress . swapValidator

offerSwap :: forall w s. HasBlockchainActions s => Oracle -> Integer -> Contract w s Text ()
offerSwap oracle amt = do
  pkh <- pubKeyHash <$> Contract.ownPubKey
  let tx = Constraints.mustPayToTheScript pkh $ Ada.lovelaceValueOf amt
  ledgerTx <- submitTxConstraints (swapInst oracle) tx
  awaitTxConfirmed $ txId ledgerTx
  logInfo @String $ "Offered " ++ show amt ++ " lovelace for swap."

-- gives a list of all the UTxOs that sit at the swap address
findSwaps :: HasBlockchainActions s => Oracle -> (PubKeyHash -> Bool) -> Contract w s Text [(TxOutRef, TxOutTx, PubKeyHash)]
findSwaps oracle p = do
  utxos <- utxoAt $ swapAddress oracle
  return $ mapMaybe g $ Map.toList utxos
  where
    f :: TxOutTx -> Maybe PubKeyHash
    f o = do
      dh <- txOutDatumHash $ txOutTxOut o
      (Datum d) <- Map.lookup dh $ txData $ txOutTxTx o -- gets the data
      PlutusTx.fromData d -- deserielize the data to pkh

    g :: (TxOutRef, TxOutTx) -> Maybe (TxOutRef, TxOutTx, PubKeyHash)
    g (oref, o) = do
      pkh <- f o
      guard $ p pkh -- guard included in monads | it takes some boolean and it fails if the boolean is false
      return (oref, o, pkh)

retrieveSwaps :: HasBlockchainActions s => Oracle -> Contract w s Text ()
retrieveSwaps oracle = do
  pkh <- pubKeyHash <$> ownPubKey -- takes the owner's pkh
  xs <- findSwaps oracle (== pkh) -- checks that is the swaps that bleong to himself
  case xs of
    [] -> logInfo @String "No swaps found"
    _ -> do
      let lookups =
            Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- xs])
              <> Constraints.otherScript (swapValidator oracle)
          tx = mconcat [Constraints.mustSpendScriptOutput oref $ Redeemer $ PlutusTx.toData () | (oref, _, _) <- xs]
      ledgerTx <- submitTxConstraintsWith @Swapping lookups tx
      awaitTxConfirmed $ txId ledgerTx
      logInfo @String $ "Retrieved " ++ show (length xs) ++ " swap(s)."

useSwap :: forall w s. HasBlockchainActions s => Oracle -> Contract w s Text ()
useSwap oracle = do
  funds <- ownFunds
  let amt = assetClassValueOf funds $ oAsset oracle -- given all my funds I check how many tokens from the oracle I have
  logInfo @String $ "Available assets: " ++ show amt

  m <- findOracle oracle -- findOracle => finds the UTxOs that contains the oracle and the value
  case m of
    Nothing -> logInfo @String "Oracle not found."
    Just (oref, o, x) -> do
      logInfo @String $ "Found oracle, exchange rate " ++ show x
      pkh <- pubKeyHash <$> Contract.ownPubKey
      swaps <- findSwaps oracle (/= pkh) -- look for all available swaps where we are not the owner
      case find (f amt x) swaps of -- tries to find a swap that they can afford
        Nothing -> logInfo @String "No suitable swap found."
        Just (oref', o', pkh') -> do
          let v = txOutValue (txOutTxOut o) <> lovelaceValueOf (oFee oracle) -- to the existing NFT and fees of the oracle I add my fees => the outpur of the oracle
              p = assetClassValue (oAsset oracle) $ price (lovelaces $ txOutValue $ txOutTxOut o') x -- the price I have to pay
              lookups =
                Constraints.otherScript (swapValidator oracle)
                  <> Constraints.otherScript (oracleValidator oracle)
                  <> Constraints.unspentOutputs (Map.fromList [(oref, o), (oref', o')])
              tx =
                Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData Use) -- consume the oracle input
                  <> Constraints.mustSpendScriptOutput oref' (Redeemer $ PlutusTx.toData ()) -- consume the swap input
                  <> Constraints.mustPayToOtherScript
                    (validatorHash $ oracleValidator oracle)
                    (Datum $ PlutusTx.toData x)
                    v -- pay to the oracle
                  <> Constraints.mustPayToPubKey pkh' p -- pay the seller of the lovelace
          ledgerTx <- submitTxConstraintsWith @Swapping lookups tx
          awaitTxConfirmed $ txId ledgerTx
          logInfo @String $ "Made swap with price " ++ show (Value.flattenValue p)
  where
    getPrice :: Integer -> TxOutTx -> Integer
    getPrice x o = price (lovelaces $ txOutValue $ txOutTxOut o) x

    f :: Integer -> Integer -> (TxOutRef, TxOutTx, PubKeyHash) -> Bool
    f amt x (_, o, _) = getPrice x o <= amt -- x = current exhange rate | getPrice check if the price we wpuld have to pay for the specific swap at most as high as the tokens we own

type SwapSchema =
  BlockchainActions
    .\/ Endpoint "offer" Integer -- ofer a swap for a given amount of ADA
    .\/ Endpoint "retrieve" () -- retrieve all my swaps
    .\/ Endpoint "use" () -- do a swap
    .\/ Endpoint "funds" () -- gives my currently available funds

swap :: Oracle -> Contract (Last Value) SwapSchema Text ()
-- select offers simultainely the endpoints and whaterever is selected gets executed
swap oracle = (offer `select` retrieve `select` use `select` funds) >> swap oracle -- >> sequel again the endpoints
  where
    -- wrappers of the endpoints but now we add an endpoint
    offer :: Contract (Last Value) SwapSchema Text ()
    offer = h $ do
      amt <- endpoint @"offer" -- block the offer endpoint until an amount is inputed
      offerSwap oracle amt -- we call the offerSwap oracle with the amount inputed

    retrieve :: Contract (Last Value) SwapSchema Text ()
    retrieve = h $ do
      endpoint @"retrieve"
      retrieveSwaps oracle

    use :: Contract (Last Value) SwapSchema Text ()
    use = h $ do
      endpoint @"use"
      useSwap oracle

    -- logs the value to the outside
    funds :: Contract (Last Value) SwapSchema Text ()
    funds = h $ do
      endpoint @"funds"
      v <- ownFunds 
      tell $ Last $ Just v

    h :: Contract (Last Value) SwapSchema Text () -> Contract (Last Value) SwapSchema Text ()
    h = handleError logError -- an error handler function that logges an error
