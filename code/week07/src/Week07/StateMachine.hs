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

module Week07.StateMachine
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
import Data.Text (Text, pack)
import GHC.Generics (Generic)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Typed.Tx
import Ledger.Value
import Playground.Contract (ToSchema)
import Plutus.Contract as Contract hiding (when)
import Plutus.Contract.StateMachine
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), check, unless)
import Prelude (Semigroup (..))
import qualified Prelude

data Game = Game
  { gFirst :: !PubKeyHash,
    gSecond :: !PubKeyHash,
    gStake :: !Integer,
    gPlayDeadline :: !Slot,
    gRevealDeadline :: !Slot,
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

data GameDatum = GameDatum ByteString (Maybe GameChoice) | Finished -- Finished represents the final state of our state machine
  deriving (Show)

instance Eq GameDatum where
  {-# INLINEABLE (==) #-}
  GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')
  Finished == Finished = True
  _ == _ = False

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | Reveal ByteString | ClaimFirst | ClaimSecond
  deriving (Show)

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINEABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
  dh <- txOutDatum o
  Datum d <- f dh
  PlutusTx.fromData d

{-# INLINEABLE transition #-}
transition :: Game -> State GameDatum -> GameRedeemer -> Maybe (TxConstraints Void Void, State GameDatum)
transition game s r = case (stateValue s, stateData s, r) of -- stateValue s = the Value in the UTXO that we are consuming, stateData s = Datum, r = Redeemer
  (v, GameDatum bs Nothing, Play c) -- first situation is the one where the first player has moved and the second player is moving now and chooses the move c
    | lovelaces v == gStake game -> -- value is actually the stake of the game
      Just
        ( Constraints.mustBeSignedBy (gSecond game)
            <> Constraints.mustValidateIn (to $ gPlayDeadline game),
          -- the new state of the result in UTxO which again is given by datum and value
          State (GameDatum bs $ Just c) (lovelaceValueOf $ 2 * gStake game) -- the new datum will be bs $ Just c | the new value will be twice the stake of the game
        )
  (v, GameDatum _ (Just _), Reveal _) -- the second situation is both players have moved and the first player discovers that he has won
    | lovelaces v == (2 * gStake game) ->
      Just
        ( Constraints.mustBeSignedBy (gFirst game)
            <> Constraints.mustValidateIn (to $ gRevealDeadline game)
            <> Constraints.mustPayToPubKey (gFirst game) token,
          State Finished mempty -- the game is over and nothing is left in the contract
        )
  (v, GameDatum _ Nothing, ClaimFirst) -- the third case is second player hasn't moved yet and also doesn't move in the deadline so the first player wants his stake back
    | lovelaces v == gStake game ->
      Just
        ( Constraints.mustBeSignedBy (gFirst game)
            <> Constraints.mustValidateIn (from $ 1 + gPlayDeadline game)
            <> Constraints.mustPayToPubKey (gFirst game) token,
          State Finished mempty
        )
  (v, GameDatum _ (Just _), ClaimSecond)
    | lovelaces v == (2 * gStake game) ->
      Just
        ( Constraints.mustBeSignedBy (gSecond game)
            <> Constraints.mustValidateIn (from $ 1 + gRevealDeadline game)
            <> Constraints.mustPayToPubKey (gFirst game) token,
          State Finished mempty
        )
  _ -> Nothing -- all other states are invalid
  where
    token :: Value
    token = assetClassValue (gToken game) 1 -- the NFT

{-# INLINEABLE final #-}
final :: GameDatum -> Bool
final Finished = True -- we must specify what final states are and that's just this finished state
final _ = False

{-# INLINEABLE check #-}
check :: ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
check bsZero' bsOne' (GameDatum bs (Just c)) (Reveal nonce) _ =
  -- the only condition we have to put into this check function is the one with the nonce
  sha2_256 (nonce `concatenate` if c == Zero then bsZero' else bsOne') == bs
check _ _ _ _ _ = True

{-# INLINEABLE gameStateMachine #-}
gameStateMachine :: Game -> ByteString -> ByteString -> StateMachine GameDatum GameRedeemer
gameStateMachine game bsZero' bsOne' =
  StateMachine
    { smTransition = transition game,
      smFinal = final, --this final check
      smCheck = check bsZero' bsOne', -- the additional check
      smThreadToken = Just $ gToken game
    }

{-# INLINEABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsZero' bsOne' = mkValidator $ gameStateMachine game bsZero' bsOne'

type Gaming = StateMachine GameDatum GameRedeemer

bsZero, bsOne :: ByteString
bsZero = "0"
bsOne = "1"

gameStateMachine' :: Game -> StateMachine GameDatum GameRedeemer
gameStateMachine' game = gameStateMachine game bsZero bsOne

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

-- a state machine client, and this is basically what we need to interact with state machine from our wallet, from our contract monad
gameClient :: Game -> StateMachineClient GameDatum GameRedeemer
gameClient game = mkStateMachineClient $ StateMachineInstance (gameStateMachine' game) (gameInst game) -- to get a client, we first create a state machine instance
-- mkStateMachineClient -> turns the StateMachineInstance into a client | the client can interact with the state machine from off-chain code

data FirstParams = FirstParams
  { fpSecond :: !PubKeyHash,
    fpStake :: !Integer,
    fpPlayDeadline :: !Slot,
    fpRevealDeadline :: !Slot,
    fpNonce :: !ByteString,
    fpCurrency :: !CurrencySymbol,
    fpTokenName :: !TokenName,
    fpChoice :: !GameChoice
  }
  deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

-- it turns an SM contract error into a text by showing the SM contract error and then picking the resulting string into a text
mapError' :: Contract w s SMContractError a -> Contract w s Text a
mapError' = mapError $ pack . show

firstGame :: forall w s. HasBlockchainActions s => FirstParams -> Contract w s Text ()
firstGame fp = do
  pkh <- pubKeyHash <$> Contract.ownPubKey
  let game =
        Game
          { gFirst = pkh,
            gSecond = fpSecond fp,
            gStake = fpStake fp,
            gPlayDeadline = fpPlayDeadline fp,
            gRevealDeadline = fpRevealDeadline fp,
            gToken = AssetClass (fpCurrency fp, fpTokenName fp)
          }
      client = gameClient game
      v = lovelaceValueOf (fpStake fp) -- stake | the NFT is automaticaly put into this value
      c = fpChoice fp -- choice
      bs = sha2_256 $ fpNonce fp `concatenate` if c == Zero then bsZero else bsOne -- hash

  -- runInitialise -> starts the state machine by creating a UTxO at the state machine address | args: client, datum, value
  void $ mapError' $ runInitialise client (GameDatum bs Nothing) v
  logInfo @String $ "made first move: " ++ show (fpChoice fp)

  void $ awaitSlot $ 1 + fpPlayDeadline fp -- wait
  m <- mapError' $ getOnChainState client -- takes the client and returns, something of type Maybe OnChainState: Just OnChainState or Nothing
  case m of
    Nothing -> throwError "game output not found" -- no output is found
    Just ((o, _), _) -> case tyTxOutData o of -- tyTxOutData directly accesses the datum
      GameDatum _ Nothing -> do
        -- the second player hasn't moved
        logInfo @String "second player did not play"
        void $ mapError' $ runStep client ClaimFirst --
        logInfo @String "first player reclaimed stake"
      GameDatum _ (Just c') | c' == c -> do
        -- the second player moved
        logInfo @String "second player played and lost"
        void $ mapError' $ runStep client $ Reveal $ fpNonce fp
        logInfo @String "first player revealed and won"
      _ -> logInfo @String "second player played and won"

data SecondParams = SecondParams
  { spFirst :: !PubKeyHash,
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
      client = gameClient game
  m <- mapError' $ getOnChainState client
  case m of
    Nothing -> logInfo @String "no running game found"
    Just ((o, _), _) -> case tyTxOutData o of
      GameDatum _ Nothing -> do
        logInfo @String "running game found"
        void $ mapError' $ runStep client $ Play $ spChoice sp
        logInfo @String $ "made second move: " ++ show (spChoice sp)

        void $ awaitSlot $ 1 + spRevealDeadline sp

        m' <- mapError' $ getOnChainState client
        case m' of
          Nothing -> logInfo @String "first player won"
          Just _ -> do
            logInfo @String "first player didn't reveal"
            void $ mapError' $ runStep client ClaimSecond
            logInfo @String "second player won"
      _ -> throwError "unexpected datum"

type GameSchema = BlockchainActions .\/ Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract () GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    first = endpoint @"first" >>= firstGame
    second = endpoint @"second" >>= secondGame
