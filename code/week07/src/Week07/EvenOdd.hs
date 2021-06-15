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

module Week07.EvenOdd
  ( Game (..),
    GameChoice (..),
    FirstParams (..),
    SecondParams (..),
    GameSchema,
    endpoints,
  )
where

import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Map as Map
import Data.Text (Text)
import GHC.Generics (Generic)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value
import Playground.Contract (ToSchema)
import Plutus.Contract as Contract hiding (when)
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), unless)
import Prelude (Semigroup (..))
import qualified Prelude

data Game = Game
  { gFirst :: !PubKeyHash, -- the 2 players identified by the 2 pkh
    gSecond :: !PubKeyHash,
    gStake :: !Integer, -- number of lovelace that are to be used as stake in the game by each player
    gPlayDeadline :: !Slot, -- the time the second player has to make a move before the first player can claim back his stake
    gRevealDeadline :: !Slot, -- is in the case that the second player has made a move, how much time the first player has to claim victory by revealing his nonce
    gToken :: !AssetClass
  }
  deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Game

data GameChoice = Zero | One
  deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

instance Eq GameChoice where
  {-# INLINEABLE (==) #-}
  Zero == Zero = True
  One == One = True
  _ == _ = False

PlutusTx.unstableMakeIsData ''GameChoice

-- GameDatum is what I will use as state for the contract
-- ByteString is the hash that the first player submits
-- Maybe GameChoice is the move by the second player | Maybe -> in the beginning, the second player hasn't yet moved
data GameDatum = GameDatum ByteString (Maybe GameChoice)
  deriving (Show)

instance Eq GameDatum where
  {-# INLINEABLE (==) #-}
  GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')

PlutusTx.unstableMakeIsData ''GameDatum

-- Play is when the second player moves and as argument, it has a game choice
-- Reveal is for the case when the first player has won and must prove that by revealing its nonce (the argument)
-- ClaimFirst is in the case when the second player doesn't make a move
-- ClaimSecond is for the case that the first player doesn't reveal because he knows he has lost
data GameRedeemer = Play GameChoice | Reveal ByteString | ClaimFirst | ClaimSecond
  deriving (Show)

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINEABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
  dh <- txOutDatum o -- get the try to get the datum hash from the output, which may fail
  Datum d <- f dh -- use the second argument function to turn this hash into a datum value
  PlutusTx.fromData d -- pass this datum as something from of type game datum

{-# INLINEABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsZero' bsOne' dat red ctx =
  traceIfFalse "token missing from input" (assetClassValueOf (txOutValue ownInput) (gToken game) == 1) -- check that the own input, the input I'm presently validating, contains the state token
    && case (dat, red) of
      (GameDatum bs Nothing, Play c) ->
        -- first situation is the one where the first player has moved and the second player is moving now and chooses the move c
        traceIfFalse "not signed by second player" (txSignedBy info (gSecond game)) -- checks that this move is made by the second player so he has to sign the transaction
          && traceIfFalse "first player's stake missing" (lovelaces (txOutValue ownInput) == gStake game) -- checks that the first player has put down the stake for the game
          && traceIfFalse "second player's stake missing" (lovelaces (txOutValue ownOutput) == (2 * gStake game)) -- checks if the second player put down his own stake
          && traceIfFalse "wrong output datum" (outputDatum == GameDatum bs (Just c)) -- the datum of the output must be the same hash as before, but now the nothing is replaced by just C, where C is the move the second player is making
          && traceIfFalse "missed deadline" (to (gPlayDeadline game) `contains` txInfoValidRange info) -- the move has to happen before the first deadline (gPlayDeadline game)
          && traceIfFalse "token missing from output" (assetClassValueOf (txOutValue ownOutput) (gToken game) == 1) -- the NFT must be passed on to the new UTXO to identify that again
      (GameDatum bs (Just c), Reveal nonce) ->
        -- the second situation is both players have moved and the first player discovers that he has won
        traceIfFalse "not signed by first player" (txSignedBy info (gFirst game))
          && traceIfFalse "commit mismatch" (checkNonce bs nonce c) -- the nonce must indeed agree with the hash he submitted earlier
          && traceIfFalse "missed deadline" (to (gRevealDeadline game) `contains` txInfoValidRange info)
          && traceIfFalse "wrong stake" (lovelaces (txOutValue ownInput) == (2 * gStake game)) -- the input must contain the stake of both players
          && traceIfFalse "NFT must go to first player" nftToFirst
      (GameDatum _ Nothing, ClaimFirst) ->
        -- the third case is second player hasn't moved yet and also doesn't move in the deadline so the first player wants his stake back
        traceIfFalse "not signed by first player" (txSignedBy info (gFirst game))
          && traceIfFalse "too early" (from (1 + gPlayDeadline game) `contains` txInfoValidRange info) -- it must only happen after the deadline has passed
          && traceIfFalse "first player's stake missing" (lovelaces (txOutValue ownInput) == gStake game)
          && traceIfFalse "NFT must go to first player" nftToFirst
      (GameDatum _ (Just _), ClaimSecond) ->
        -- last case is both players have moved, but the first player realized that he didn't win so he doesn't reveal his nonce and therefore he missed the deadline
        traceIfFalse "not signed by second player" (txSignedBy info (gSecond game))
          && traceIfFalse "too early" (from (1 + gRevealDeadline game) `contains` txInfoValidRange info) -- it must not happen before the deadline
          && traceIfFalse "wrong stake" (lovelaces (txOutValue ownInput) == (2 * gStake game))
          && traceIfFalse "NFT must go to first player" nftToFirst
      _ -> False -- that's all legitimate transitions we can have so in all other cases we don't validate, we fail validation
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxOut
    ownInput = case findOwnInput ctx of
      Nothing -> traceError "game input missing"
      Just i -> txInInfoResolved i

    ownOutput :: TxOut
    ownOutput = case getContinuingOutputs ctx of
      [o] -> o
      _ -> traceError "expected exactly one game output"

    outputDatum :: GameDatum
    outputDatum = case gameDatum ownOutput (`findDatum` info) of
      Nothing -> traceError "game output datum not found"
      Just d -> d

    -- when the first player has won and wants to prove it by revealing his nonce so he needs to prove that the hash he submitted in the beginning of the game fits this nonce
    -- this function would only be involved or only be relevant in the case where the first player knows he has won
    -- the first argument is the hash we submitted
    -- the second argument is the nonce he now reveals
    -- the third argument is the move that both players made
    checkNonce :: ByteString -> ByteString -> GameChoice -> Bool
    -- to compute the hash and take the nonce concatenated with this ByteString and apply the sha2_256 hash function to it
    checkNonce bs nonce cSecond = sha2_256 (nonce `concatenate` cFirst) == bs -- check to make sure that that is indeed the hash, the first player committed in the first place (bs)
      where
        cFirst :: ByteString
        cFirst = case cSecond of
          Zero -> bsZero' -- if the choice (cSecond) was zero, I take the byte String representing zero
          One -> bsOne' -- if it was one, I take the byte String representing one

    -- after the game is over and there is no UTXO at the game address anymore the NFT goes back to the first player
    nftToFirst :: Bool
    -- valuePaidTo gets the info from the context and key hash and then it basically adds up all the values that go to that pub key hash in some output of the transaction
    nftToFirst = assetClassValueOf (valuePaidTo info $ gFirst game) (gToken game) == 1

-- helper type that just bundles information about what the datum and what the redeemer type are
data Gaming

instance Scripts.ScriptType Gaming where
  type DatumType Gaming = GameDatum
  type RedeemerType Gaming = GameRedeemer

-- we define the byte Strings for actually we are going to use for, the two choices, zero and one
bsZero, bsOne :: ByteString
bsZero = "0"
bsOne = "1"

gameInst :: Game -> Scripts.ScriptInstance Gaming
gameInst game =
  Scripts.validator @Gaming
    ( $$(PlutusTx.compile [||mkGameValidator||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsZero
        `PlutusTx.applyCode` PlutusTx.liftCode bsOne
    )
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . gameInst

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

-- gets the Game and then in the Contract monad tries to find the UTXO so it could fail, the UTXO could not be there (Maybe)
-- then I return the reference (TxOutRef) and the output itself (TxOutTx), and the GameDatum
findGameOutput :: HasBlockchainActions s => Game -> Contract w s Text (Maybe (TxOutRef, TxOutTx, GameDatum))
findGameOutput game = do
  utxos <- utxoAt $ gameAddress game -- get all the UTXOs at the game address
  return $ do
    -- find -> if it finds an element in the list that satisfies the predicate (f), it will return it as a just and otherwise it will return nothing
    (oref, o) <- find f $ Map.toList utxos -- Map.toList utxos -> turns UTxOs into a list of pairs
    dat <- gameDatum (txOutTxOut o) (`Map.lookup` txData (txOutTxTx o)) -- gets the datum
    return (oref, o, dat)
  where
    f :: (TxOutRef, TxOutTx) -> Bool
    -- take a pair, ignore the reference (TxOutRef), just take the output (o | TxOutTx) and check whether this output contains our token
    f (_, o) = assetClassValueOf (txOutValue $ txOutTxOut o) (gToken game) == 1

data FirstParams = FirstParams
  { fpSecond :: !PubKeyHash, -- we need to provide the second player
    fpStake :: !Integer,
    fpPlayDeadline :: !Slot,
    fpRevealDeadline :: !Slot,
    fpNonce :: !ByteString,
    fpCurrency :: !CurrencySymbol, -- the NFT is split into CurrencySymbol and TokenName
    fpTokenName :: !TokenName,
    fpChoice :: !GameChoice -- the move the player wants to make
  }
  deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

firstGame :: forall w s. HasBlockchainActions s => FirstParams -> Contract w s Text ()
firstGame fp = do
  pkh <- pubKeyHash <$> Contract.ownPubKey -- our own pkh
  let game =
        Game
          { gFirst = pkh,
            gSecond = fpSecond fp,
            gStake = fpStake fp,
            gPlayDeadline = fpPlayDeadline fp,
            gRevealDeadline = fpRevealDeadline fp,
            gToken = AssetClass (fpCurrency fp, fpTokenName fp) -- we assemble the currency symbol and token name into an asset class
          }
      v = lovelaceValueOf (fpStake fp) <> assetClassValue (gToken game) 1 --  our stake that we must put into the UTXO plus the NFT that we must put into the UTXO
      c = fpChoice fp -- our choice
      bs = sha2_256 $ fpNonce fp `concatenate` if c == Zero then bsZero else bsOne -- take the nonce and concatenate it with the zero byte string or the one byte String
      tx = Constraints.mustPayToTheScript (GameDatum bs Nothing) v -- produce a script output at this address with the datum that contains the hash (bs), nothing for the second player, because the second player hasn't played yet and the value we computed (v)
  ledgerTx <- submitTxConstraints (gameInst game) tx
  void $ awaitTxConfirmed $ txId ledgerTx
  logInfo @String $ "made first move: " ++ show (fpChoice fp)

  -- the second player has a chance to move, but it must happen before this fpPlayDeadline then the first player waits until this deadline has passed (awaitSlot $ 1)
  void $ awaitSlot $ 1 + fpPlayDeadline fp

  m <- findGameOutput game -- check whether we find UTXO containing the NFT
  case m of
    Nothing -> throwError "game output not found" -- something has gone very wrong that can't actually happen because it just can't disappear
    Just (oref, o, dat) -> case dat of
      GameDatum _ Nothing -> do
        -- in this case the deadline has passed and the second player hasn't moved
        logInfo @String "second player did not play"
        let lookups =
              Constraints.unspentOutputs (Map.singleton oref o)
                <> Constraints.otherScript (gameValidator game)
            tx' = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData ClaimFirst)
        ledgerTx' <- submitTxConstraintsWith @Gaming lookups tx'
        void $ awaitTxConfirmed $ txId ledgerTx'
        logInfo @String "reclaimed stake" -- we reclaim the stake
      GameDatum _ (Just c') | c' == c -> do
        logInfo @String "second player played and lost"
        let lookups =
              Constraints.unspentOutputs (Map.singleton oref o)
                <> Constraints.otherScript (gameValidator game)
            tx' =
              Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Reveal $ fpNonce fp) -- we reveal our nonce (Reveal $ fpNonce fp)
                <> Constraints.mustValidateIn (to $ fpRevealDeadline fp)
        ledgerTx' <- submitTxConstraintsWith @Gaming lookups tx'
        void $ awaitTxConfirmed $ txId ledgerTx'
        logInfo @String "victory"
      _ -> logInfo @String "second player played and won"

data SecondParams = SecondParams
  { spFirst :: !PubKeyHash, -- we need to provide the first player
    spStake :: !Integer,
    spPlayDeadline :: !Slot,
    spRevealDeadline :: !Slot,
    spCurrency :: !CurrencySymbol,
    spTokenName :: !TokenName,
    spChoice :: !GameChoice
  }
  deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

secondGame :: forall w s. HasBlockchainActions s => SecondParams -> Contract w s Text ()
secondGame sp = do
  pkh <- pubKeyHash <$> Contract.ownPubKey
  let game =
        Game
          { gFirst = spFirst sp,
            gSecond = pkh,
            gStake = spStake sp,
            gPlayDeadline = spPlayDeadline sp,
            gRevealDeadline = spRevealDeadline sp,
            gToken = AssetClass (spCurrency sp, spTokenName sp)
          }
  m <- findGameOutput game
  case m of
    Just (oref, o, GameDatum bs Nothing) -> do
      logInfo @String "running game found"
      let token = assetClassValue (gToken game) 1 -- the NFT
      -- we must consume the existing UTXO and producing one at the same address | into the output we must put twice the stake and the NFT
      let v = let x = lovelaceValueOf (spStake sp) in x <> x <> token -- x is local local variable = stake in lovelace
          c = spChoice sp -- choice
          lookups =
            Constraints.unspentOutputs (Map.singleton oref o)
              <> Constraints.otherScript (gameValidator game)
              <> Constraints.scriptInstanceLookups (gameInst game)
          tx =
            Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Play c) -- Reedemer = Play c
              <> Constraints.mustPayToTheScript (GameDatum bs $ Just c) v -- we create a new UTXO with the updated datum
              <> Constraints.mustValidateIn (to $ spPlayDeadline sp)
      ledgerTx <- submitTxConstraintsWith @Gaming lookups tx
      let tid = txId ledgerTx
      void $ awaitTxConfirmed tid
      logInfo @String $ "made second move: " ++ show (spChoice sp)

      -- now it's the first player turn again so we wait until this reveal deadline has passed
      void $ awaitSlot $ 1 + spRevealDeadline sp

      -- it's our turn again, and we try to find the UTXO which could now be a different one, that's why it's called m'
      m' <- findGameOutput game
      case m' of
        Nothing -> logInfo @String "first player won" -- if we don't find an UTXO any more => while we were waiting, the first player revealed and won
        Just (oref', o', _) -> do
          -- if you still do find the UTXO it means the first player didn't reveal and the second player won
          logInfo @String "first player didn't reveal"
          let lookups' =
                Constraints.unspentOutputs (Map.singleton oref' o')
                  <> Constraints.otherScript (gameValidator game)
              tx' =
                Constraints.mustSpendScriptOutput oref' (Redeemer $ PlutusTx.toData ClaimSecond) -- spend the UTxO we found
                  <> Constraints.mustValidateIn (from $ 1 + spRevealDeadline sp) -- after the reveal deadline has passed
                  <> Constraints.mustPayToPubKey (spFirst sp) token -- we hand back the NFT to the first player
          ledgerTx' <- submitTxConstraintsWith @Gaming lookups' tx'
          void $ awaitTxConfirmed $ txId ledgerTx'
          logInfo @String "second player won"
    _ -> logInfo @String "no running game found"

type GameSchema = BlockchainActions .\/ Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract () GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    first = endpoint @"first" >>= firstGame
    second = endpoint @"second" >>= secondGame
