{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Spec.Model
  ( tests,
    test,
    TSModel (..),
  )
where

import Control.Lens hiding (elements)
import Control.Monad (void, when)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust, isNothing)
import Data.Monoid (Last (..))
import Data.String (IsString (..))
import Data.Text (Text)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Value
import Plutus.Contract.Test
import Plutus.Contract.Test.ContractModel
import Plutus.Trace.Emulator
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck
import Week08.TokenSale (TSStartSchema', TSUseSchema, TokenSale (..), nftName, startEndpoint', useEndpoints)

data TSState = TSState -- define a data type TS state for token sale state that
  { _tssPrice :: !Integer,
    _tssLovelace :: !Integer,
    _tssToken :: !Integer
  }
  deriving (Show)

makeLenses ''TSState

newtype TSModel = TSModel {_tsModel :: Map Wallet TSState} -- the model is just a map from wallet to token sale state
  deriving (Show)

makeLenses ''TSModel

tests :: TestTree
tests = testProperty "token sale model" prop_TS

instance ContractModel TSModel where
  data Action TSModel
    = Start Wallet -- that this wallet starts a token sale contract
    | SetPrice Wallet Wallet Integer -- the second wallet sets the prize for the token sale operated by the first wallet to this integer | this should only work if these two wallets are the same
    | AddTokens Wallet Wallet Integer
    | Withdraw Wallet Wallet Integer Integer -- the second wallet wants to withdraw tokens (1st Int) and ADA (1st Int) from the token sale run by the 1sr wallet that should again fail if the two wallets are not the same
    | BuyTokens Wallet Wallet Integer
    | Close Wallet Wallet
    deriving (Show, Eq)

  data ContractInstanceKey TSModel w s e where
    -- (Last TokenSale) - the state type
    -- TSStartSchema' - schema - we use the primed version because I don't want to generate an NFT using this forge contract, we want to pass it in
    -- Text - the error type
    StartKey :: Wallet -> ContractInstanceKey TSModel (Last TokenSale) TSStartSchema' Text
    -- 1st Wallet - the one that owns the token sale we are interacting with
    -- 2nd Wallet - the one that actually runs the contract
    UseKey :: Wallet -> Wallet -> ContractInstanceKey TSModel () TSUseSchema Text

  instanceTag key _ = fromString $ "instance tag for: " ++ show key

  -- generate an arbitrary action
  arbitraryAction _ =
    oneof $ -- randomly pick an action and generate the random argument for the constructor
      (Start <$> genWallet) : -- <$> fmap | calls the genWallet which generates wallets and start takes an wallet ant returns an action
      [SetPrice <$> genWallet <*> genWallet <*> genNonNeg] -- SetPrice (genWallet(), genWallet(), genNonNeg()) - similar to do block
        ++ [AddTokens <$> genWallet <*> genWallet <*> genNonNeg]
        ++ [BuyTokens <$> genWallet <*> genWallet <*> genNonNeg]
        ++ [Withdraw <$> genWallet <*> genWallet <*> genNonNeg <*> genNonNeg]
        ++ [Close <$> genWallet <*> genWallet]

  initialState = TSModel Map.empty

-- should now tell us what is the effect on our model if we encounter the start W action
  nextState (Start w) = do 
    withdraw w $ nfts Map.! w -- the effect of start will be, that wallet W loses the NFT
    -- this combined lens goes from the model to the entry at wallet w (tsModel . at w)
    -- $= comes from the spec monad -> it takes a lens on the left-hand side, and then a new value on the right-hand side
    -- at is a lense that results in a Maybe
    (tsModel . at w) $= Just (TSState 0 0 0) -- after I have started, there will be an entry in the map because the token sale has started and it will have price zero, no tokens, no ADA (TSState 0 0 0)
    wait 1 -- comes from the spec monad -> start will take 1 slot
  nextState (SetPrice v w p) = do
    when (v == w) $ -- I check whether the wallet that invokes set price is actually the same one that runs the token sale
      (tsModel . ix v . tssPrice) $= p
    wait 1
  nextState (AddTokens v w n) = do
    started <- hasStarted v -- has the token sale started?
    when (n > 0 && started) $ do
      bc <- askModelState $ view $ balanceChange w
      let token = tokens Map.! v
      when (tokenAmt + assetClassValueOf bc token >= n) $ do
        -- does the wallet have the tokens to give?
        withdraw w $ assetClassValue token n
        (tsModel . ix v . tssToken) $~ (+ n)
    wait 1
  nextState (BuyTokens v w n) = do
    when (n > 0) $ do
      m <- getTSState v
      case m of
        Just t
          | t ^. tssToken >= n -> do
            let p = t ^. tssPrice
                l = p * n
            withdraw w $ lovelaceValueOf l
            deposit w $ assetClassValue (tokens Map.! v) n
            (tsModel . ix v . tssLovelace) $~ (+ l)
            (tsModel . ix v . tssToken) $~ (+ (- n))
        _ -> return ()
    wait 1
  nextState (Withdraw v w n l) = do
    when (v == w) $ do
      m <- getTSState v
      case m of
        Just t
          | t ^. tssToken >= n && t ^. tssLovelace >= l -> do
            deposit w $ lovelaceValueOf l <> assetClassValue (tokens Map.! w) n
            (tsModel . ix v . tssLovelace) $~ (+ (- l))
            (tsModel . ix v . tssToken) $~ (+ (- n))
        _ -> return ()
    wait 1
  nextState (Close v w) = do
    when (v == w) $ do
      m <- getTSState v
      case m of
        Just t -> do
          deposit w $ lovelaceValueOf ( t ^. tssLovelace) <>
                      assetClassValue (tokens Map.! w) (t ^. tssToken) <>
                      (nfts Map.! w)
          (tsModel . at v) $= Nothing
        _ -> return ()
    wait 1

  perform h _ cmd = case cmd of
    (Start w) -> callEndpoint @"start" (h $ StartKey w) (nftCurrencies Map.! w, tokenCurrencies Map.! w, tokenNames Map.! w) >> delay 1
    (SetPrice v w p) -> callEndpoint @"set price" (h $ UseKey v w) p >> delay 1
    (AddTokens v w n) -> callEndpoint @"add tokens" (h $ UseKey v w) n >> delay 1
    (BuyTokens v w n) -> callEndpoint @"buy tokens" (h $ UseKey v w) n >> delay 1
    (Withdraw v w n l) -> callEndpoint @"withdraw" (h $ UseKey v w) (n, l) >> delay 1
    (Close v w) -> callEndpoint @"close" (h $ UseKey v w) () >> delay 1

  precondition s (Start w) = isNothing $ getTSState' s w
  precondition s (SetPrice v _ _) = isJust $ getTSState' s v
  precondition s (AddTokens v _ _) = isJust $ getTSState' s v
  precondition s (BuyTokens v _ _) = isJust $ getTSState' s v
  precondition s (Withdraw v _ _ _) = isJust $ getTSState' s v
  precondition s (Close v _) = isJust $ getTSState' s v

deriving instance Eq (ContractInstanceKey TSModel w s e)

deriving instance Show (ContractInstanceKey TSModel w s e)

getTSState' :: ModelState TSModel -> Wallet -> Maybe TSState
getTSState' s v = s ^. contractState . tsModel . at v

getTSState :: Wallet -> Spec TSModel (Maybe TSState)
getTSState v = do
  s <- getModelState
  return $ getTSState' s v

hasStarted :: Wallet -> Spec TSModel Bool
hasStarted v = isJust <$> getTSState v

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

wallets :: [Wallet]
wallets = [w1, w2]

tokenCurrencies, nftCurrencies :: Map Wallet CurrencySymbol
tokenCurrencies = Map.fromList $ zip wallets ["aa", "bb"]
nftCurrencies = Map.fromList $ zip wallets ["01", "02"]

tokenNames :: Map Wallet TokenName
tokenNames = Map.fromList $ zip wallets ["A", "B"]

tokens :: Map Wallet AssetClass
tokens = Map.fromList [(w, AssetClass (tokenCurrencies Map.! w, tokenNames Map.! w)) | w <- wallets]

nftAssets :: Map Wallet AssetClass
nftAssets = Map.fromList [(w, AssetClass (nftCurrencies Map.! w, nftName)) | w <- wallets]

nfts :: Map Wallet Value
nfts = Map.fromList [(w, assetClassValue (nftAssets Map.! w) 1) | w <- wallets]

tss :: Map Wallet TokenSale
tss =
  Map.fromList
    [ ( w,
        TokenSale
          { tsSeller = pubKeyHash $ walletPubKey w,
            tsToken = tokens Map.! w,
            tsNFT = nftAssets Map.! w
          }
      )
      | w <- wallets
    ]

delay :: Int -> EmulatorTrace ()
delay = void . waitNSlots . fromIntegral

instanceSpec :: [ContractInstanceSpec TSModel]
instanceSpec =
  [ContractInstanceSpec (StartKey w) w startEndpoint' | w <- wallets]
    ++ [ContractInstanceSpec (UseKey v w) w $ useEndpoints $ tss Map.! v | v <- wallets, w <- wallets]

genWallet :: Gen Wallet
genWallet = elements wallets

genNonNeg :: Gen Integer
genNonNeg = getNonNegative <$> arbitrary

tokenAmt :: Integer
tokenAmt = 1_000

prop_TS :: Actions TSModel -> Property
prop_TS =
  withMaxSuccess 100
    . propRunActionsWithOptions
      (defaultCheckOptions & emulatorConfig .~ EmulatorConfig (Left d))
      instanceSpec
      (const $ pure True)
  where
    d :: InitialDistribution
    d =
      Map.fromList $
        [ ( w,
            lovelaceValueOf 1000_000_000
              <> (nfts Map.! w)
              <> mconcat [assetClassValue t tokenAmt | t <- Map.elems tokens]
          )
          | w <- wallets
        ]

test :: IO ()
test = quickCheck prop_TS
