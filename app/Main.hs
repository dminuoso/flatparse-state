{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UnboxedTuples          #-}

module Main where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BS
import qualified Data.ByteString.Unsafe as BS

import           Control.Monad.IO.Class (MonadIO(..))
import           Data.STRef
import           GHC.Exts
import           GHC.ForeignPtr
import           GHC.IO hiding (liftIO)
import           GHC.ST hiding (liftST)
import           GHC.Word
import           Unsafe.Coerce (unsafeCoerce)

{-
data Mode s = PureMode | IOMode | STMode s
type family State m = r | r -> m where
  State PureMode   = State# ()
  State IOMode     = State# RealWorld
  State (STMode s) = Proxy# s

 - -}

#if !MIN_VERSION_base(4,17,0)
type ZeroBitRep = 'TupleRep ('[] :: [RuntimeRep])
type ZeroBitType = TYPE ZeroBitRep
#endif

type IOMode = State# RealWorld
type PureMode = Proxy# ()
type STMode s = State# s

newtype ParserT (st :: ZeroBitType) e a = ParserT
  { runParserT# :: ForeignPtrContents
                 -> Addr#
                 -> Addr#
                 -> st
                 -> Res# st e a
  }

type Res# (st :: ZeroBitType) e a =
  (#
    (# st, a, Addr# #)
  | (# st #)
  | (# st, e #)
  #)

data Result e a =
    OK a !(BS.ByteString)  -- ^ Contains return value and unconsumed input.
  | Fail                  -- ^ Recoverable-by-default failure.
  | Err !e                -- ^ Unrecoverble-by-default error.
  deriving Show

pattern OK# :: (st :: ZeroBitType) -> a -> Addr# -> Res# st e a
pattern OK# st a s = (# (# st, a, s #) | | #)

-- | Constructor for errors which are by default non-recoverable.
pattern Err# :: (st :: ZeroBitType) -> e -> Res# st e a
pattern Err# st e = (# | | (# st, e #) #)

-- | Constructor for recoverable failure.
pattern Fail# :: (st :: ZeroBitType) -> Res# st e a
pattern Fail# st = (# | (# st #) | #)
{-# complete OK#, Err#, Fail# #-}

instance Functor (ParserT s e) where
  fmap f (ParserT g) = ParserT \fp eob s st -> case g fp eob s st of
    OK# st' a s -> OK# st' (f $! a) s
    x           -> unsafeCoerce# x
  {-# inline fmap #-}

  (<$) a' (ParserT g) = ParserT \fp eob s st -> case g fp eob s st of
    OK# st' a s -> OK# st' a' s
    x           -> unsafeCoerce# x
  {-# inline (<$) #-}

instance Applicative (ParserT s e) where
  pure a = ParserT \fp eob s st -> OK# st a s
  {-# inline pure #-}
  ParserT ff <*> ParserT fa = ParserT \fp eob s st -> case ff fp eob s st of
    OK# st' f s -> case fa fp eob s st' of
      OK# st'' a s -> OK# st'' (f $! a) s
      x            -> unsafeCoerce# x
    x -> unsafeCoerce# x
  {-# inline (<*>) #-}
  ParserT fa <* ParserT fb = ParserT \fp eob s st -> case fa fp eob s st of
    OK# st' a s -> case fb fp eob s st' of
      OK# st'' b s -> OK# st'' a s
      x            -> unsafeCoerce# x
    x -> unsafeCoerce# x
  {-# inline (<*) #-}
  ParserT fa *> ParserT fb = ParserT \fp eob s st -> case fa fp eob s st of
    OK# st' a s -> fb fp eob s st'
    x           -> unsafeCoerce# x
  {-# inline (*>) #-}

instance Monad (ParserT s e) where
  return = pure
  {-# inline return #-}
  ParserT fa >>= f = ParserT \fp eob s st -> case fa fp eob s st of
    OK# st' a s -> runParserT# (f a) fp eob s st'
    x           -> unsafeCoerce# x
  {-# inline (>>=) #-}
  (>>) = (*>)
  {-# inline (>>) #-}

instance MonadIO (ParserT IOMode e) where
  liftIO (IO a) = ParserT \fp eob s rw ->
    case a rw of
      (# rw', a #) -> OK# rw' a s

data PureWorld
type Parser = ParserT PureMode
type ParserIO = ParserT IOMode
type ParserST s = ParserT (STMode s)

runParser :: Parser e a -> BS.ByteString -> Result e a
runParser pst buf = unsafePerformIO (runParserIO (unsafeCoerce pst) buf)

runParserST :: (forall s. ParserST s e a) -> BS.ByteString -> Result e a
runParserST pst buf = unsafeDupablePerformIO (runParserIO pst buf)

runParserIO :: ParserIO e a -> BS.ByteString -> IO (Result e a)
runParserIO (ParserT f) b@(BS.PS (ForeignPtr _ fp) _ (I# len)) = do
  BS.unsafeUseAsCString b \(Ptr buf) -> do
    let end = plusAddr# buf len
    IO \st -> case f fp end buf st of
      OK# rw' a s ->  let offset = minusAddr# s buf
                      in (# rw', OK a (BS.drop (I# offset) b) #)

      Err# rw' e ->  (# rw', Err e #)
      Fail# rw'  ->  (# rw', Fail #)

embedIOinST :: ParserIO e a -> ParserT s e a
embedIOinST = unsafeCoerce

unsafeEmbedSTinPure :: ParserT s e a -> Parser e a
unsafeEmbedSTinPure = unsafeCoerce

unsafeEmbedIOinPure :: ParserIO e a -> Parser e a
unsafeEmbedIOinPure p = unsafeDupableEmbedIOinPure (liftIO noDuplicate >> p)

unsafeDupableEmbedIOinPure :: ParserIO e a -> Parser e a
unsafeDupableEmbedIOinPure = unsafeCoerce

liftST :: ST s a -> ParserST s e a
liftST (ST t) = ParserT \fp eob s st ->
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

err :: Parser () Int
err = thing

word8 :: ParserT st e Word8
word8 = ParserT \fp eob s st -> case eqAddr# eob s of
  1# -> Fail# st
  _  -> case indexWord8OffAddr# s 0# of
    w# -> OK# st (W8# w#) (plusAddr# s 1#)

main :: IO ()
main = do
  print =<< runParserIO thing "123"
  print (runParserST another "123")
