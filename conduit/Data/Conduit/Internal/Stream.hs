{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TupleSections #-}

module Data.Conduit.Internal.Stream where

import Control.Applicative (Applicative (..))
import Control.Monad (liftM)
import Control.Monad.Trans.Class (MonadTrans (lift))
import qualified Data.Conduit.Internal as C
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Base (MonadBase (liftBase))
import Data.Void (Void, absurd)
import Data.Monoid (Monoid (mappend, mempty))
import Control.Monad.Trans.Resource
import Control.Monad.Morph

data Stream l i o u m r = forall s . Stream s (s -> Step l i o u m r s)
-- data Stream l i o u m r = forall sfunc . Stream (forall r . sfunc r -> r) (sfunc (Step l i o u m r (forall r . sfunc r -> r)))
data Step l i o u m r s =
    HaveOutputS s (m ()) o
  | NeedInputS (i -> s) (u -> s)
  | DoneS r
  | PipeMS (m s)
  | LeftoverS s l
  | Skip s

{-# RULES
"stream/unstream" forall s . stream (unstream s) = s
  #-}

stream :: C.Pipe l i o u m r -> Stream l i o u m r
stream pip = Stream pip next where
    next (C.HaveOutput p c o) = HaveOutputS p c o
    next (C.NeedInput p c) = NeedInputS p c
    next (C.Done x) = DoneS x
    next (C.PipeM mp) = PipeMS mp
    next (C.Leftover p i) = LeftoverS p i

unstream :: (Monad m) => Stream l i o u m r -> C.Pipe l i o u m r
unstream (Stream s0 next) = go s0 where
    go s = case next s of
        HaveOutputS s' c o -> C.HaveOutput (go s') c o
        NeedInputS p c -> C.NeedInput (go . p) (go . c)
        DoneS x -> C.Done x
        PipeMS ms -> C.PipeM (liftM go ms)
        LeftoverS s' l -> C.Leftover (go s') l
        Skip s' -> go s'

instance Functor (Stream l i o u m) where
    fmap f (Stream s0 next) = Stream s0 next' where
        next' s = case next s of
            HaveOutputS s' c o -> HaveOutputS s' c o
            NeedInputS p c -> NeedInputS p c
            DoneS x -> DoneS (f x)
            PipeMS ms -> PipeMS ms
            LeftoverS s' l -> LeftoverS s' l
            Skip s' -> Skip s'

instance Monad m => Applicative (Stream l i o u m) where
    pure x = Stream () next where
        next = const (DoneS x)
    
    Stream s0f nextf <*> Stream s0x nextx = Stream s0 next where
        s0 = Left s0f
        next (Left sf) = case nextf sf of
            HaveOutputS s' c o -> HaveOutputS (Left s') c o
            NeedInputS p c -> NeedInputS (Left . p) (Left . c)
            DoneS f -> Skip (Right (f, s0x))
            PipeMS ms -> PipeMS (liftM Left ms)
            LeftoverS s' l -> LeftoverS (Left s') l
            Skip s' -> Skip (Left s')
        next (Right (f, sx)) = case nextx sx of
            HaveOutputS s' c o -> HaveOutputS (Right (f, s')) c o
            NeedInputS p c -> NeedInputS (Right . (f,) . p) (Right . (f,) . c)
            DoneS x -> DoneS (f x)
            PipeMS ms -> PipeMS (liftM (Right . (f,)) ms)
            LeftoverS s' l -> LeftoverS (Right (f, s')) l
            Skip s' -> Skip (Right (f, s'))

instance Monad m => Monad (Stream l i o u m) where
    return = pure
    Stream s0 next >>= fp = Stream (Left s0) next' where
        next' (Left s) = case next s of
            HaveOutputS s' c o -> HaveOutputS (Left s') c o
            NeedInputS p c -> NeedInputS (Left . p) (Left . c)
            DoneS x -> Skip (Right (fp x))
            PipeMS ms -> PipeMS (liftM Left ms)
            LeftoverS s' l -> LeftoverS (Left s') l
            Skip s' -> Skip (Left s')
        next' (Right (Stream s inext)) = (case inext s of
            HaveOutputS s' c o -> HaveOutputS (recurse s') c o
            NeedInputS p c -> NeedInputS (recurse . p) (recurse . c)
            DoneS x -> DoneS x
            PipeMS ms -> PipeMS (liftM recurse ms)
            LeftoverS s' l -> LeftoverS (recurse s') l
            Skip s' -> Skip (recurse s')) where
                recurse s' = Right (Stream s' inext)

    (>>) = (*>)

instance MonadBase base m => MonadBase base (Stream l i o u m) where
    liftBase = lift . liftBase

instance MonadTrans (Stream l i o u) where
    lift act = Stream Nothing next where
        next Nothing = PipeMS (liftM Just act)
        next (Just x) = DoneS x

instance MonadIO m => MonadIO (Stream l i o u m) where
    liftIO = lift . liftIO

instance MonadThrow m => MonadThrow (Stream l i o u m) where
    monadThrow = lift . monadThrow

instance MonadActive m => MonadActive (Stream l i o u m) where
    monadActive = lift monadActive

instance Monad m => Monoid (Stream l i o u m ()) where
    mempty = return ()
    mappend = (>>)

instance MonadResource m => MonadResource (Stream l i o u m) where
    liftResourceT = lift . liftResourceT

data AwaitState a = AwaitStart | AwaitSuccess a | AwaitFail
await :: Stream l i o u m (Maybe i)
await = Stream AwaitStart next where
    next AwaitStart = NeedInputS AwaitSuccess (const AwaitFail)
    next (AwaitSuccess x) = DoneS (Just x)
    next (AwaitFail) = DoneS Nothing

data AwaitEState a b = AwaitEStart | AwaitESuccess a | AwaitEFail b
awaitE :: Stream l i o u m (Either u i)
awaitE = Stream AwaitEStart next where
    next AwaitEStart = NeedInputS AwaitESuccess AwaitEFail
    next (AwaitESuccess x) = DoneS (Right x)
    next (AwaitEFail x) = DoneS (Left x)

yield :: Monad m => o -> Stream l i o u m ()
yield x = Stream False next where
    next False = HaveOutputS True (return ()) x
    next True = DoneS ()

leftover :: l -> Stream l i o u m ()
leftover l = Stream False next where
    next False = LeftoverS True l
    next True = DoneS ()

addCleanup :: Monad m => (Bool -> m ()) -> Stream l i o u m r -> Stream l i o u m r
addCleanup cleanup (Stream s0 next) = Stream (Right s0) next' where
    next' (Left x) = DoneS x
    next' (Right s) = case next s of
        HaveOutputS s' close x -> HaveOutputS (Right s') (cleanup False >> close) x
        NeedInputS p c -> NeedInputS (Right . p) (Right . c)
        DoneS x -> PipeMS (cleanup True >> return (Left x))
        PipeMS ms -> PipeMS (liftM Right ms)
        LeftoverS s' l -> LeftoverS (Right s') l
        Skip s' -> Skip (Right s')

idP :: Monad m => Stream l a a r m r
idP = Stream AwaitEStart next where
    next AwaitEStart = NeedInputS AwaitESuccess AwaitEFail
    next (AwaitESuccess x) = HaveOutputS AwaitEStart (return ()) x
    next (AwaitEFail x) = DoneS x

pipe :: Monad m => Stream l a b r0 m r1 -> Stream Void b c r1 m r2 -> Stream l a c r0 m r2
Stream s0l nextl `pipe` Stream s0r nextr = Stream s0 next where
    s0 = Left (s0l, Right s0r, return ())
    next (Right x) = DoneS x
    next (Left (sl, Right sr, final)) = (case nextr sr of
        HaveOutputS s' c o -> HaveOutputS (recurse s') (c >> final) o
        NeedInputS rp rc -> Skip (Left (sl, Left (rp, rc), final))
        DoneS x -> PipeMS (final >> return (Right x))
        PipeMS ms -> PipeMS (liftM recurse ms)
        LeftoverS _ i -> absurd i
        Skip s' -> Skip (recurse s')) where
            recurse s' = Left (sl, Right s', final)
    next (Left (sl, Left (rp, rc), final)) = (case nextl sl of
        HaveOutputS s' c o -> Skip (Left (s', Right (rp o), c))
        NeedInputS p c -> NeedInputS (recurse . p) (recurse . c)
        DoneS r1 -> Skip (Left (sl, Right (rc r1), return ()))
        PipeMS ms -> PipeMS (liftM recurse ms)
        LeftoverS s' i -> LeftoverS (recurse s') i
        Skip s' -> Skip (recurse s')) where
            recurse s' = Left (s', Left (rp, rc), final)

runPipe :: Monad m => Stream Void () Void () m r -> m r
runPipe (Stream s0 next) = go s0 where
    go s = case next s of
        HaveOutputS _ _ o -> absurd o
        NeedInputS _ c -> go (c ())
        DoneS x -> return x
        PipeMS ms -> ms >>= go
        LeftoverS _ i -> absurd i
        Skip s' -> go s'

injectLeftovers :: Monad m => Stream i i o u m r -> Stream l i o u m r
injectLeftovers (Stream s0 next) = Stream ([], s0) next' where
    next' (ls, s) = case next s of
        HaveOutputS s' c o -> HaveOutputS (ls, s') c o
        NeedInputS p c -> case ls of
            [] -> NeedInputS (([],) . p) (([],) . c)
            (l : ls') -> Skip (ls', p l)
        DoneS x -> DoneS x
        PipeMS ms -> PipeMS (liftM ([],) ms)
        LeftoverS s' l -> Skip (l:ls, s')
        Skip s' -> Skip (ls, s')

transPipe :: (forall a . m a -> n a) -> Stream l i o u m r -> Stream l i o u n r
transPipe f (Stream s0 next) = Stream s0 next' where
    next' s = case next s of
        HaveOutputS s' c o -> HaveOutputS s' (f c) o
        NeedInputS p c -> NeedInputS p c
        DoneS x -> DoneS x
        PipeMS ms -> PipeMS (f ms)
        LeftoverS s' l -> LeftoverS s' l
        Skip s' -> Skip s'

mapOutput :: (o1 -> o2) -> Stream l i o1 u m r -> Stream l i o2 u m r
mapOutput f (Stream s0 next) = Stream s0 next' where
    next' s = case next s of
        HaveOutputS s' c o -> HaveOutputS s' c (f o)
        NeedInputS p c -> NeedInputS p c
        DoneS x -> DoneS x
        PipeMS ms -> PipeMS ms
        LeftoverS s' l -> LeftoverS s' l
        Skip s' -> Skip s'

mapOutputMaybe :: (o1 -> Maybe o2) -> Stream l i o1 u m r -> Stream l i o2 u m r
mapOutputMaybe f (Stream s0 next) = Stream s0 next' where
    next' s = case next s of
        HaveOutputS s' c o -> case f o of
            Nothing -> Skip s'
            Just val -> HaveOutputS s' c val
        NeedInputS p c -> NeedInputS p c
        DoneS x -> DoneS x
        PipeMS ms -> PipeMS ms
        LeftoverS s' l -> LeftoverS s' l
        Skip s' -> Skip s'

mapInput :: (i1 -> i2) -> (l2 -> Maybe l1) -> Stream l2 i2 o u m r -> Stream l1 i1 o u m r
mapInput f f' (Stream s0 next) = Stream s0 next' where
    next' s = case next s of
        HaveOutputS s' c o -> HaveOutputS s' c o
        NeedInputS p c -> NeedInputS (p . f) c
        DoneS x -> DoneS x
        PipeMS ms -> PipeMS ms
        LeftoverS s' l -> case f' l of
            Nothing -> Skip s'
            Just l' -> LeftoverS s' l'
        Skip s' -> Skip s'

sourceList :: Monad m => [o] -> Stream l i o u m ()
sourceList list = Stream list next where
    next [] = DoneS ()
    next (x : xs) = HaveOutputS xs (return ()) x
