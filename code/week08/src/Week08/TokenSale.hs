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

module Week08.TokenSale
  ( TokenSale (..),
    TSRedeemer (..),
    nftName,
    TSStartSchema,
    TSStartSchema',
    TSUseSchema,
    startEndpoint,
    startEndpoint',
    useEndpoints,
  )
where

import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import Data.Monoid (Last (..))
import Data.Text (Text, pack)
import GHC.Generics (Generic)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value
import Plutus.Contract as Contract hiding (when)
import Plutus.Contract.StateMachine
import qualified Plutus.Contracts.Currency as C
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), check, unless)
import Prelude (Semigroup (..), Show (..), uncurry)
import qualified Prelude

data TokenSale = TokenSale -- the parameter we will use for the contract
  { tsSeller :: !PubKeyHash,
    tsToken :: !AssetClass,
    tsNFT :: !AssetClass -- the NFT that is used to identify the correct UTXO
  }
  deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''TokenSale

data TSRedeemer
  = SetPrice Integer -- set price to a new value for the token price and lovelace
  | AddTokens Integer -- the argument gives the amount of tokens to add
  | BuyTokens Integer -- the arguments gives the amount of tokens to buy
  | Withdraw Integer Integer -- first argument = how many tokens to withdraw; the second argument = how many lovelace to withdraw
  | Close
  deriving (Show, Prelude.Eq)

PlutusTx.unstableMakeIsData ''TSRedeemer

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer -- given a value extracts the amount of lovelace is in the value
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINEABLE transition #-}
transition :: TokenSale -> State (Maybe Integer) -> TSRedeemer -> Maybe (TxConstraints Void Void, State (Maybe Integer))
transition ts s r = case (stateValue s, stateData s, r) of -- split the given state into the value and the datum
  (v, Just _, SetPrice p)
    | p >= 0 ->
      Just
        ( Constraints.mustBeSignedBy (tsSeller ts),
          State (Just p) $
            v
              <> nft (negate 1)
        )
  (v, Just p, AddTokens n)
    | n > 0 ->
      Just
        ( mempty,
          State (Just p) $
            v
              <> nft (negate 1)
              <> assetClassValue (tsToken ts) n
        )
  (v, Just p, BuyTokens n)
    | n > 0 ->
      Just
        ( mempty,
          State (Just p) $
            v
              <> nft (negate 1)
              <> assetClassValue (tsToken ts) (negate n)
              <> lovelaceValueOf (n * p)
        )
  (v, Just p, Withdraw n l)
    | n >= 0 && l >= 0 ->
      Just
        ( Constraints.mustBeSignedBy (tsSeller ts),
          State (Just p) $
            v
              <> nft (negate 1)
              <> assetClassValue (tsToken ts) (negate n)
              <> lovelaceValueOf (negate l)
        )
  (_, Just _, Close) ->
      Just (Constraints.mustBeSignedBy (tsSeller ts),
          State Nothing
          mempty
        )
  _ -> Nothing
  where
    nft :: Integer -> Value
    nft = assetClassValue (tsNFT ts)

{-# INLINEABLE tsStateMachine #-}
tsStateMachine :: TokenSale -> StateMachine (Maybe Integer) TSRedeemer
tsStateMachine ts = mkStateMachine (Just $ tsNFT ts) (transition ts) isNothing

{-# INLINEABLE mkTSValidator #-}
mkTSValidator :: TokenSale -> Maybe Integer -> TSRedeemer -> ScriptContext -> Bool
mkTSValidator = mkValidator . tsStateMachine

type TS = StateMachine (Maybe Integer) TSRedeemer

tsInst :: TokenSale -> Scripts.ScriptInstance TS
tsInst ts =
  Scripts.validator @TS
    ($$(PlutusTx.compile [||mkTSValidator||]) `PlutusTx.applyCode` PlutusTx.liftCode ts)
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @(Maybe Integer) @TSRedeemer

tsValidator :: TokenSale -> Validator
tsValidator = Scripts.validatorScript . tsInst

tsAddress :: TokenSale -> Ledger.Address
tsAddress = scriptAddress . tsValidator

tsClient :: TokenSale -> StateMachineClient (Maybe Integer) TSRedeemer
tsClient ts = mkStateMachineClient $ StateMachineInstance (tsStateMachine ts) (tsInst ts)

mapErrorC :: Contract w s C.CurrencyError a -> Contract w s Text a
mapErrorC = mapError $ pack . show

mapErrorSM :: Contract w s SMContractError a -> Contract w s Text a
mapErrorSM = mapError $ pack . show

nftName :: TokenName
nftName = "NFT"

-- is supposed to be invoked by the seller to set up this state machine
-- Maybe CurrencySymbol if you pass in nothing this off-chain contract will mint a new NFT for you using the forge contract method from the currency use case, but you can also provide just currency symbol if the NFT already exists.
-- AssetClass is the token you want to trade
-- Contract (Last TokenSale) s Text TokenSale - using the writer monad type with the last type (Last TokenSale)
-- once the token sale has been set up, it gets written here so that other contracts have the possibility to discover that, but I also return the created token sale in the end
startTS :: HasBlockchainActions s => Maybe CurrencySymbol -> AssetClass -> Contract (Last TokenSale) s Text TokenSale
startTS mcs token = do
  pkh <- pubKeyHash <$> Contract.ownPubKey -- public key hash of the seller
  cs <- case mcs of -- I check whether NFT currency similar has already been provided or not
    Nothing -> C.currencySymbol <$> mapErrorC (C.forgeContract pkh [(nftName, 1)]) -- if not, I use this forge contract as before to mint a fresh NFT
    Just cs' -> return cs' -- I use the curency similar provided in the function
  let ts =
        TokenSale
          { tsSeller = pkh, -- my own pkh
            tsToken = token,
            tsNFT = AssetClass (cs, nftName)
          }
      client = tsClient ts -- I set up a state machine client
  void $ mapErrorSM $ runInitialise client (Just 0) mempty -- runInitialize using a client initial price of zero and no additional funds on top of the NFT which is automatically added
  tell $ Last $ Just ts
  logInfo $ "started token sale " ++ show ts
  return ts

-- I need the TokenSale argument to identify the correct contract
setPrice :: HasBlockchainActions s => TokenSale -> Integer -> Contract w s Text ()
setPrice ts p = void $ mapErrorSM $ runStep (tsClient ts) $ SetPrice p

addTokens :: HasBlockchainActions s => TokenSale -> Integer -> Contract w s Text ()
addTokens ts n = void (mapErrorSM $ runStep (tsClient ts) $ AddTokens n)

buyTokens :: HasBlockchainActions s => TokenSale -> Integer -> Contract w s Text ()
buyTokens ts n = void $ mapErrorSM $ runStep (tsClient ts) $ BuyTokens n

withdraw :: HasBlockchainActions s => TokenSale -> Integer -> Integer -> Contract w s Text ()
withdraw ts n l = void $ mapErrorSM $ runStep (tsClient ts) $ Withdraw n l

close :: HasBlockchainActions s => TokenSale -> Contract w s Text ()
close ts = void $ mapErrorSM $ runStep (tsClient ts) Close

type TSStartSchema = -- for the seller who wants to start the contract
  BlockchainActions
    .\/ Endpoint "start" (CurrencySymbol, TokenName) -- it takes the currency symbol and the token name of the asset to be traded

type TSStartSchema' =
  BlockchainActions
    .\/ Endpoint "start" (CurrencySymbol, CurrencySymbol, TokenName) -- additionally takes the currency symbol of the provided NFT

type TSUseSchema =
  BlockchainActions
    .\/ Endpoint "set price" Integer
    .\/ Endpoint "add tokens" Integer
    .\/ Endpoint "buy tokens" Integer
    .\/ Endpoint "withdraw" (Integer, Integer)
    .\/ Endpoint "close" ()

startEndpoint :: Contract (Last TokenSale) TSStartSchema Text ()
startEndpoint = startTS' >> startEndpoint -- calls startTS', and then recurses
  where
    -- startTS' calls endpoint to block until the parameters are provided and then runs startTS using nothing as the first argument indicating that the NFT has to be minted
    startTS' = handleError logError $ endpoint @"start" >>= void . startTS Nothing . AssetClass

startEndpoint' :: Contract (Last TokenSale) TSStartSchema' Text ()
startEndpoint' = startTS' >> startEndpoint'
  where
    startTS' = handleError logError $ endpoint @"start" >>= \(cs1, cs2, tn) -> void $ startTS (Just cs1) $ AssetClass (cs2, tn)

useEndpoints :: TokenSale -> Contract () TSUseSchema Text ()
useEndpoints ts = (setPrice' `select` addTokens' `select` buyTokens' `select` withdraw' `select` close') >> useEndpoints ts
  where
    setPrice' = handleError logError $ endpoint @"set price" >>= setPrice ts
    addTokens' = handleError logError $ endpoint @"add tokens" >>= addTokens ts
    buyTokens' = handleError logError $ endpoint @"buy tokens" >>= buyTokens ts
    withdraw' = handleError logError $ endpoint @"withdraw" >>= uncurry (withdraw ts)
    close' = handleError logError $ endpoint @"close" >> close ts
