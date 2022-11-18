{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BS
import qualified Data.ByteString.Internal as BS

import Data.STRef
import GHC.Word
import Control.Monad.IO.Class (MonadIO(..))
import Unsafe.Coerce (unsafeCoerce)
import GHC.IO hiding (liftIO)
import GHC.ST hiding (liftST)
import GHC.Exts
import GHC.ForeignPtr

data NoIO

newtype ParserST st e a = ParserST
  { runParserST# :: ForeignPtrContents
                 -> Addr#
                 -> Addr#
                 -> State# st
                 -> Res# st e a
  }

type Res# st e a =
  (#
    (# State# st, a, Addr# #)
  | (# State# st #)
  | (# State# st, e #)
  #)

data Result e a =
    OK a !(BS.ByteString)  -- ^ Contains return value and unconsumed input.
  | Fail                  -- ^ Recoverable-by-default failure.
  | Err !e                -- ^ Unrecoverble-by-default error.
  deriving Show

pattern OK# :: State# st -> a -> Addr# -> Res# st e a
pattern OK# st a s = (# (# st, a, s #) | | #)

-- | Constructor for errors which are by default non-recoverable.
pattern Err# :: State# st -> e -> Res# st e a
pattern Err# st e = (# | | (# st, e #) #)

-- | Constructor for recoverable failure.
pattern Fail# :: State# st -> Res# st e a
pattern Fail# st = (# | (# st #) | #)
{-# complete OK#, Err#, Fail# #-}

instance Functor (ParserST s e) where
  fmap f (ParserST g) = ParserST \fp eob s st -> case g fp eob s st of
    OK# st' a s -> OK# st' (f $! a) s
    x           -> unsafeCoerce# x
  {-# inline fmap #-}

  (<$) a' (ParserST g) = ParserST \fp eob s st -> case g fp eob s st of
    OK# st' a s -> OK# st' a' s
    x          -> unsafeCoerce# x
  {-# inline (<$) #-}

instance Applicative (ParserST s e) where
  pure a = ParserST \fp eob s st -> OK# st a s
  {-# inline pure #-}
  ParserST ff <*> ParserST fa = ParserST \fp eob s st -> case ff fp eob s st of
    OK# st' f s -> case fa fp eob s st' of
      OK# st'' a s -> OK# st'' (f $! a) s
      x            -> unsafeCoerce# x
    x -> unsafeCoerce# x
  {-# inline (<*>) #-}
  ParserST fa <* ParserST fb = ParserST \fp eob s st -> case fa fp eob s st of
    OK# st' a s -> case fb fp eob s st' of
      OK# st'' b s -> OK# st'' a s
      x -> unsafeCoerce# x
    x -> unsafeCoerce# x
  {-# inline (<*) #-}
  ParserST fa *> ParserST fb = ParserST \fp eob s st -> case fa fp eob s st of
    OK# st' a s -> fb fp eob s st'
    x       -> unsafeCoerce# x
  {-# inline (*>) #-}

instance Monad (ParserST s e) where
  return = pure
  {-# inline return #-}
  ParserST fa >>= f = ParserST \fp eob s st -> case fa fp eob s st of
    OK# st' a s -> runParserST# (f a) fp eob s st'
    x       -> unsafeCoerce# x
  {-# inline (>>=) #-}
  (>>) = (*>)
  {-# inline (>>) #-}

instance MonadIO (ParserST RealWorld e) where
  liftIO (IO a) = ParserST \fp eob s rw ->
    case a rw of 
      (# rw', a #) -> OK# rw' a s

type Parser = ParserST NoIO
type ParserIO = ParserST RealWorld

runParser :: Parser e a -> BS.ByteString -> Result e a
runParser pst buf = unsafePerformIO (runParserIO (unsafeCoerce pst) buf)

runParserST :: (forall s. ParserST s e a) -> BS.ByteString -> Result e a
runParserST pst buf = unsafeDupablePerformIO (runParserIO (unsafeCoerce pst) buf)

runParserIO :: ParserIO e a -> BS.ByteString -> IO (Result e a)
runParserIO (ParserST f) b@(BS.PS (ForeignPtr _ fp) _ (I# len)) = do
  BS.unsafeUseAsCString b \(Ptr buf) -> do
    let end = plusAddr# buf len
    IO \st -> case f fp end buf st of
      OK# rw' a s ->  let offset = minusAddr# s buf
                      in (# rw', OK a (BS.drop (I# offset) b) #)
      
      Err# rw' e ->  (# rw', Err e #)
      Fail# rw'  ->  (# rw', Fail #)

embedIOinST :: ParserIO e a -> ParserST s e a
embedIOinST = unsafeCoerce

unsafeEmbedSTinPure :: ParserST s e a -> Parser e a
unsafeEmbedSTinPure = unsafeCoerce

unsafeEmbedIOinPure :: ParserIO e a -> Parser e a
unsafeEmbedIOinPure p = unsafeDupableEmbedParserIO (liftIO noDuplicate >> p)

unsafeDupableEmbedIOinPure :: ParserIO e a -> Parser e a
unsafeDupableEmbedIOinPure = unsafeCoerce

liftST :: ST s a -> ParserST s e a
liftST (ST t) = ParserST \fp eob s st -> 
  case t st of
    (# st', a #) -> OK# st' a s

thing :: ParserIO () ()
thing = do
  liftIO (putStrLn "start parsing")
  liftIO . print =<< word8
  liftIO . print =<< word8
  liftIO . print =<< word8
  liftIO (putStrLn "done")

another :: ParserST s () Int
another = do
  ref <- liftST $ newSTRef (0 :: Int)
  w1 <- word8
  w2 <- word8
  w3 <- word8

  liftST $ do
    modifySTRef ref (+ (fromIntegral w1))
    modifySTRef ref (+ (fromIntegral w2))
    modifySTRef ref (+ (fromIntegral w3))
    readSTRef ref

word8 :: ParserST st e Word8
word8 = ParserST \fp eob s st -> case eqAddr# eob s of
  1# -> Fail# st
  _  -> case indexWord8OffAddr# s 0# of
    w# -> OK# st (W8# w#) (plusAddr# s 1#)

main :: IO ()
main = do
  print =<< runParserIO thing "123"
  print (runParserST another "123")
