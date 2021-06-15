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

module Week06.Oracle.Funds
  ( ownFunds,
    ownFunds',
  )
where

import Control.Monad hiding (fmap)
import qualified Data.Map as Map
import Data.Monoid (Last (..))
import Data.Text (Text)
import Ledger hiding (singleton)
import Ledger.Value as Value
import Plutus.Contract as Contract hiding (when)
import PlutusTx.Prelude hiding ((<$>))
import Prelude ((<$>))

ownFunds :: HasBlockchainActions s => Contract w s Text Value -- sum up all the value in my own UTxOs
ownFunds = do
  pk <- ownPubKey
  utxos <- utxoAt $ pubKeyAddress pk -- looks at the UTxOs at my pk aka wallet
  let v = mconcat $ Map.elems $ txOutValue . txOutTxOut <$> utxos -- the sum of all the values of all the UTxOs that I own
  logInfo @String $ "own funds: " ++ show (Value.flattenValue v)
  return v

ownFunds' :: Contract (Last Value) BlockchainActions Text () -- instead oof returning the value permanently tells it
ownFunds' = do
  handleError logError $ ownFunds >>= tell . Last . Just
  void $ Contract.waitNSlots 1
  ownFunds'
