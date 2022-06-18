{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Tender
( Tender (..)
, CreateParams (..)
, BidParams (..)
, RevealParams (..)
, CancelParams (..)
, FinishParams (..)
, TenderSchema
, endpoints
) where


import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text, pack)
import GHC.Generics (Generic)
import Plutus.Contract as Contract hiding (when)
import Plutus.Contract.StateMachine
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup(..), check, unless)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import Ledger.Typed.Tx
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value
import Playground.Contract (ToSchema)
import Prelude (Semigroup (..))
import qualified Prelude

data Tender = Tender
{ tenderOwner :: !PubKeyHash
, minBidTime :: !Slot
, minRevealTime :: !Slot
, txCost :: !Integer
, tToken :: !AssetClass
} deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)
PlutusTx.makeLift ''Tender
data BidInfo = BidInfo
{ bidOwner :: !PubKeyHash
, bidValue :: !Integer
} deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq,
Prelude.Ord)
-- Need to defined an instance of Eq only because I really need an instance of
Ord
instance Eq BidInfo where
{-# INLINABLE (==) #-}
BidInfo i == BidInfo i' = bidValue i == bidValue i'
-- Defining an instance of Ord to make it easier to sort bid infos
instance Ord BidInfo where
{-# INLINABLE (<=) #-}
BidInfo i <= BidInfo i' = bidValue i <= bidValue i'
PlutusTx.unstableMakeIsData ''BidInfo
data TenderDatum = TenderDatum (Maybe [ByteString]) (Maybe [BidInfo]) | Finished
deriving Show
instance Eq TenderDatum where
{-# INLINABLE (==) #-}
TenderDatum i == TenderDatum i' = bidValue i == bidValue i'
PlutusTx.unstableMakeIsData ''TenderDatum
data TenderRedeemer = Create
| Bid ByteString
| Close
| Reveal ByteString BidInfo
| Finish
| Cancel
deriving Show

PlutusTx.unstableMakeIsData ''TenderRedeemer
{-# INLINABLE default #-}
default :: Tender
default = Tender
{ dMinBidTime = Slot 10
, dMinRevealTime = Slot 20
, dTxCost = 1 }
{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue
{-# INLINABLE maybeToBool #-}
maybeToBool :: Maybe a -> Bool
maybeToBool (Just x) = True
maybeToBool Nothing = False
{-# INLINABLE transition #-}
transition :: Tender -> State TenderDatum -> TenderRedeemer -> Maybe
(TxConstraints Void Void, State TenderDatum)
transition tender s r = case (stateValue s, stateData s, r) of
-- Creating the state machine
(v, TenderDatum Nothing Nothing, Create) -> Just (
Constraints.mustBeSignedBy (tenderOwner tender)
, State
(TenderDatum Nothing Nothing) (lovelaceValueOf $ txCost tender))
-- BIDING
-- First bid
(v, TenderDatum Nothing Nothing, Bid bs') -> Just (
Constraints.mustPayToPubKey (tenderOwner tender) token
, State
(TenderDatum (Just [bs']) Nothing) (lovelaceValueOf $ txCost tender))
-- Next bids.
(v, TenderDatum (Just bs) Nothing, Bid bs') -> Just (
Constraints.mustPayToPubKey (tenderOwner tender) token
, State
(TenderDatum (fmap ((++) [bs']) bs) Nothing) (lovelaceValueOf $ txCost tender))
-- REVEALING
-- First reveal

(v, TenderDatum (Just bs) Nothing, Reveal bs' bi')
| maybeToBool $ fmap (bs' `elem`) bs -> Just (
Constraints.mustPayToPubKey (tenderOwner tender) token <>
Constraints.mus
tValidateIn (from $ 1 + minBidTime tender)
, State
(TenderDatum (Just bs) [bi']) (lovelaceValueOf $ txCost tender))
-- Next reveals
(v, TenderDatum (Just bs) (Just bi), Reveal bs' bi')
| maybeToBool $ fmap (bs' `elem`) bs -> Just (
Constraints.mustPayToPubKey (tenderOwner tender) token <>
Constraints.mus
tValidateIn (from $ 1 + minBidTime tender)
, State
(TenderDatum (Just bs) (fmap ((++) [bi']) bi)) (lovelaceValueOf $ txCost tender))
-- Finish
(v, TenderDatum (Just bs) (Just bi), Finish) -> Just (
Constraints.mustBeSignedBy (tenderOwner tender) <>
Constraints.mus
tValidateIn (from $ 1 + minRevealTime tender)
, State
(TenderDatum (Just bs) (Just bi)) (lovelaceValueOf $ txCost tender))
-- Cancel
(v, d, Cancel) -> Just (
Constraints.mustBeSignedBy (tenderOwner tender)
, State d
(lovelaceValueOf $ txCost tender))
-- Default
_ -> Nothing
where
token :: Value
token = assetClassValue (tToken tender) 1
{-# INLINABLE final #-}
final :: TenderDatum -> Bool
final Finished = True
final _ = False
{-# INLINABLE bidInfoToBS #-}
bidInfoToBS :: BidInfo -> ByteString
bidInfoToBS bi = sha2_256 (appendByteString (getPubKeyHash $ bidOwner bi)
(consByteString $ bidValue bi))
{-# INLINABLE check #-}
check :: ByteString -> TenderDatum -> TenderRedeemer -> Bool
check bs (TenderDatum (Just bs) _) (Reveal bs' bi') = bidInfoToBS bi' == bs
{-# INLINABLE tenderStateMachine #-}
tenderStateMachine :: Tender -> ByteString -> StateMachine TenderDatum
TenderRedeemer
tenderStateMachine tender bs = StateMachine
{ smTransition = transition tender
, smFinal = final
, smCheck = check bs
, smThreadToken = Just $ tToken tender}
{-# INLINABLE mkTenderValidator #-}
mkTenderValidator :: Tender -> ByteString -> TenderDatum -> TenderRedeemer ->
ScriptContext -> Bool
mkTenderValidator tender bs = mkValidator $ tenderStateMachine tender bs
type Tendering = StateMachine TenderDatum TenderRedeemer
tenderStateMachine' :: Tender -> StateMachine TenderDatum TenderRedeemer
tenderStateMachine' tender = tenderStateMachine tender bs
tenderInst :: Tender -> Scripts.ScriptInstance Tendering
tenderInst tender = Scripts.validator @Tendering
($$(PlutusTx.compile [|| mkTenderValidator ||])
`PlutusTx.applyCode` PlutusTx.liftCode tender
`PlutusTx.applyCode` PlutusTx.liftCode bs)
$$(PlutusTx.compile [|| wrap ||])
where
wrap = Scripts.wrapValidator @TenderDatum @TenderRedeemer
tenderValidator :: Tender -> Validator
tenderValidator = Scripts.validatorScript . tenderInst
tenderAddress :: Tender -> Ledger.Address
tenderAddress = scriptAddress . tenderValidator
tenderClient :: Tender -> StateMachineClient TenderDatum TenderRedeemer
tenderClient tender = mkStateMachineClient $ StateMachineInstance
(tenderStateMachine' tender) (tenderInst tender)
mapError' :: Contract w s SMContractError a -> Contract w s Text a
mapError' = mapError $ pack . show
data CreateParams = CreateParams
, cpCurrency :: !CurrencySymbol
, cpTokenName :: !TokenName
} deriving (Show, Generic, FromJSON, ToJSON, ToSchema)
createTender :: forall w s. HasBlockchainActions s => CreateParams -> Contract w
s Text ()
createTender cp = do
pkh <- pubKeyHash <$> Contract.ownPubKey
let tender = Tender
{ tenderOwner = pkh
, minBidTime = dMinBidTime default
, minRevealTime = dMinRevealTime default
, txCost = dTxCost default
, tToken = AssetClass (cpCurrency fp, cpTokenName fp)}
client = tenderClient tender
v = lovelaceValueOf (cpTxCost cp)
void $ mapError' $ runInitialise client (TenderDatum Nothing Nothing) v
logInfo @String $ "Tender created."
data BidParams = BidParams
{ bpTenderOwner :: !PubKeyHash
, bpBidInfo :: !BidInfo
, bpCurrency :: !CurrencySymbol
, bpTokenName :: !TokenName }
bidTender :: forall w s. HasBlockchainActions s => BidParams -> Contract w s Text
()
bidTender bp = do
pkh <- pubKeyHash <$> Contract.ownPubKey
let tender = Tender
{ tenderOwner = bpTenderOwner bp
, minBidTime = dMinBidTime default
, minRevealTime = dMinRevealTime default
, txCost = dTxCost default
, tToken = AssetClass (bpTokenName bp, bpTenderOwner bp)}
client = tenderClient tender
m <- mapError' $ getOnChainState client
case m of
Nothing -> logInfo @String "No tender found."
Just ((o, _), _) -> case tyTxOutData o of
TenderDatum _ _ -> do
logInfo @String "Running tender found."
void $ mapError' $ runStep client $ Bid $ bidInfoToBS $ bpBidInfo
bp
logInfo @String "Bid placed."
data RevealParams = RevealParams
{ rpTenderOwner :: !PubKeyHash
, rpBidInfo :: !BidInfo
, rpCurrency :: !CurrencySymbol
, rpTokenName :: !TokenName }
revealTender :: forall w s. HasBlockchainActions s => RevealParams -> Contract w
s Text ()
revealTender rp = do
pkh <- pubKeyHash <$> Contract.ownPubKey
let tender = Tender
{ tenderOwner = rpTenderOwner rp
, minBidTime = dMinBidTime default
, minRevealTime = dMinRevealTime default
, txCost = dTxCost default
, tToken = AssetClass (rpTokenName rp, rpCurrency rp)}
client = tenderClient tender
m <- mapError' $ getOnChainState client
case m of
Nothing -> logInfo @String "No tender found."
Just ((o, _), _) -> case tyTxOutData o of
TenderDatum _ _ -> do
logInfo @String "Running tender found."
void $ mapError' $ runStep client $ Reveal $ (bidInfoToBS $
rpBidInfo bp) (rpBidInfo rp)
logInfo @String "Bid revealed."
data CancelParams = CancelParams
{ capCurrency :: !CurrencySymbol
, capTokenName :: !TokenName }
cancelTender :: forall w s. HasBlockchainActions s => CancelParams -> Contract w
s Text ()
cancelTender cp = do
pkh <- pubKeyHash <$> Contract.ownPubKey
let tender = Tender
{ tenderOwner = pkh
, minBidTime = dMinBidTime default
, minRevealTime = dMinRevealTime default
, txCost = dTxCost default
, tToken = AssetClass (capTokenName rp, capCurrency rp)}
client = tenderClient tender
m <- mapError' $ getOnChainState client
case m of
Nothing -> logInfo @String "No tender found."
Just ((o, _), _) -> case tyTxOutData o of
TenderDatum _ _ -> do
logInfo @String "Running tender found."
void $ mapError' $ runStep client $ Cancel
logInfo @String "Bid revealed."
data FinishParams = FinishParams
{ fpCurrency :: !CurrencySymbol
, fpTokenName :: !TokenName }
 finishTender :: forall w s. HasBlockchainActions s => FinishParams -> Contract w s Text ()
finishTender fp = do
pkh <- pubKeyHash <$> Contract.ownPubKey
let tender = Tender
{ tenderOwner = pkh
, minBidTime = dMinBidTime default
, minRevealTime = dMinRevealTime default
, txCost = dTxCost default
, tToken = AssetClass (fpTokenName rp, fpCurrency rp)}
client = tenderClient tender
m <- mapError' $ getOnChainState client
case m of
Nothing -> logInfo @String "No tender found."
Just ((o, _), _) -> case tyTxOutData o of
TenderDatum _ _ -> do
logInfo @String "Running tender found."
void $ mapError' $ runStep client $ Finish
logInfo @String "Tender finished."
type TenderSchema = BlockchainActions
 .\/ Endpoint "create" CreateParams
 .\/ Endpoint "bid" BidParams
 .\/ Endpoint "reveal" RevealParams
 .\/ Endpoint "cancel" CancelParams
 .\/ Endpoint "finish" FinishParams
endpoints :: Contract () TenderSchema Text ()
endpoints = (create `select` bid `select` reveal `select` cancel `select` finish)
>> endpoints
where
create = endpoint @"create" >>= createTender
bid = endpoint @"bid" >>= bidTender
reveal = endpoint @"reveal" >>= revealTender
cancel = endpoint @"cancel" >>= cancelTender
finish = endpoint @"finish" >>= finishTender