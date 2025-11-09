module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SequentializeTranslation where

import qualified Types.LocalBehavior as LB
import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior (LCenter (..), LLeft (..), LRight (..), SeqLocalBehavior (..))

data SequentializeError
  = LimitReached
  | NotCorrectSend
  deriving (Show, Eq)

-- | Entry point for sequentializing a local behavior.
--   It transforms the local behavior into a sequential local behavior.
sequentialize :: LB.LocalBehavior -> Either SequentializeError SeqLocalBehavior
sequentialize lb = do
  let maxFUEL = 100000
  lleft <- toLeft maxFUEL lb
  return $ L lleft

-- | Recursively transforms the `LLeft` side of a local behavior.
toLeft :: Int -> LB.LocalBehavior -> Either SequentializeError LLeft
toLeft 0 _ = Left LimitReached
toLeft fuel (LB.LReceive l lb) = do
  lb' <- toLeft fuel lb
  return $ LReceive l lb'
toLeft fuel (LB.LLock la) = toLeftA fuel la
toLeft fuel lb = do
  lb' <- toCenter fuel lb
  return $ C lb'

-- | Recursively transforms the `LCenter` of a local behavior.
toCenter :: Int -> LB.LocalBehavior -> Either SequentializeError LCenter
toCenter fuel (LB.LLock la) = toCenterA fuel la
toCenter fuel lb = do
  lb' <- toRight fuel lb
  return $ LNew [] lb'

-- | Recursively transforms the `LRight` side of a local behavior.
toRight :: Int -> LB.LocalBehavior -> Either SequentializeError LRight
toRight _ LB.LNil = return LNil
toRight fuel (LB.LSend lbs) =
  case lbs of
    ((r, lb') : _) -> do
      lb'' <- toRight fuel lb'
      return $ LSend r lb''
    _ -> Left NotCorrectSend
toRight fuel (LB.LLock la) = toRightA fuel la
toRight fuel lb = do
  lb' <- toLeft (fuel - 1) lb
  return $ LSeq lb'

-- | Recursively transforms the `LLeft` side of an atomic local behavior.
toLeftA :: Int -> LB.LocalAtomic -> Either SequentializeError LLeft
toLeftA 0 _ = Left LimitReached
toLeftA fuel (LB.LChoice m l d la) = do
  la' <- toLeftA fuel la
  return $ LChoice m l d la'
toLeftA fuel (LB.LUnlock lb) = toLeft fuel lb
toLeftA fuel la = do
  la' <- toCenterA fuel la
  return $ C la'

-- | Recursively transforms the `LCenter` side of an atomic local behavior.
toCenterA :: Int -> LB.LocalAtomic -> Either SequentializeError LCenter
toCenterA fuel (LB.LNew l la) = toCenterRightA fuel [l] la
toCenterA fuel (LB.LRead l c r la) = do
  la' <- toCenterA fuel la
  return $ LRead l c r la'
toCenterA fuel (LB.LIf r1 r2 la1 la2) = do
  la1' <- toCenterA fuel la1
  la2' <- toCenterA fuel la2
  return $ LIf r1 r2 la1' la2'
toCenterA fuel (LB.LTry l f rs la1 la2) = do
  la1' <- toCenterA fuel la1
  la2' <- toCenterA fuel la2
  return $ LTry l f rs la1' la2'
toCenterA fuel (LB.LUnlock lb) = toCenter fuel lb
toCenterA fuel la = do
  la' <- toRightA fuel la
  return $ LNew [] la'

-- | Recursively transforms the `LCenterRight` side of an atomic local behavior.
--   Specifically, handles consecutive nested `LNew` constructs,
--   accumulating labels before transitioning to a right-hand sequence.
toCenterRightA :: Int -> [LB.Label] -> LB.LocalAtomic -> Either SequentializeError LCenter
toCenterRightA fuel acc (LB.LNew l la) = toCenterRightA fuel (acc ++ [l]) la
toCenterRightA fuel acc la = do
  la' <- toRightA fuel la
  return $ LNew acc la'

-- | Recursively transforms the `LRight` side of an atomic local behavior.
toRightA :: Int -> LB.LocalAtomic -> Either SequentializeError LRight
toRightA fuel (LB.LWrite c r1 r2 la) = do
  la' <- toRightA fuel la
  return $ LWrite c r1 r2 la'
toRightA fuel (LB.LRelease m f la) = do
  la' <- toRightA fuel la
  return $ LRelease m f la'
toRightA fuel (LB.LUnlock lb) = toRight fuel lb
toRightA fuel la = do
  la' <- toLeftA (fuel - 1) la
  return $ LSeq la'
