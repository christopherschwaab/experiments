{-# LANGUAGE Rank2Types, ExplicitForAll, KindSignatures, TypeOperators, GADTs, FlexibleInstances #-}
module Mauro where

type Nat f g = forall x. f x -> g x
type Bind m = forall x y. m x -> (x -> m y) -> m y
type Ret m = forall x. x -> m x

mfmap :: Monad m => (a -> b) -> m a -> m b
mfmap f m = m >>= return . f

newtype S s x = S { unS :: s -> (x, s) }
instance Monad (S s) where
  return x = S $ \s -> (x, s)
  S m >>= f = S $ \s -> let (a, s') = m s in unS (f a) s'

class MT t where
  retT :: Monad m => Ret (t m)
  bindT :: Monad m => Bind (t m)
  liftT :: Monad m => forall (x :: *). m x -> t m x
instance (Monad m, MT t) => Monad (t m) where
  return = retT
  (>>=) = bindT

newtype O f g x = O { unO :: f (g x) }
type SigHatOp (sig :: * -> *) (m :: * -> *) = Nat (sig `O` m) m

data State s x where
  Get :: (s -> x) -> State s x
  Set :: (s, x) -> State s x
instance Functor (State s) where
  fmap f (Get k) = Get (f . k)
  fmap f (Set (s, x)) = Set (s, f x)
stateOp :: SigHatOp (State s) (S s)
stateOp (O m) = case m of
  Get k -> S $ \s -> unS (k s) s
  Set (s, m) -> S $ \s -> unS m s

type MM m n = Nat m n

phi :: (Functor sig, Monad m) => SigHatOp sig m -> Nat sig m
phi op = op . O . fmap return

psi :: (Functor sig, Monad m) => Nat sig m -> SigHatOp sig m
psi op' = joinM . op' . unO where
  joinM m = m >>= id

type AlgebraicOp x = forall a b. (a, b -> x)

algLift :: (Functor sig, Monad m, Monad n) =>
           SigHatOp sig m -> MM m n -> Nat (sig `O` n) n
algLift op xi = joinM . xi . op . O . fmap return . unO where
  joinM m = m >>= id

type Map f = forall x y. (x -> y) -> f x -> f y
class MT t => FMT t where
  hmap :: (Functor m, Functor n) => Nat m n -> Nat (t m) (t n)
newtype Cod m x = Cod { runCod :: forall y. (x -> m y) -> m y }
instance Functor (Cod m) where
  fmap f c = Cod (\k -> runCod c (k . f))
instance MT Cod where
  retT x = Cod (\k -> k x)
  bindT c f = Cod (\k -> runCod c (\x -> runCod (f x) k))
  liftT m = Cod (\k -> m >>= k)

kappa :: Functor s => Nat (s `O` m) m -> Nat s (Cod m)
kappa tau = \s -> Cod (\k -> tau . O $ fmap k s)

from :: Monad m => Nat (Cod m) m
from c = runCod c return

runOp :: (Monad m, Functor s) => SigHatOp s m -> Nat (s `O` Cod m) (Cod m)
runOp op = psi (kappa op)

liftF :: (FMT t, Monad m, Functor m, Functor s) => SigHatOp s m -> Nat (s `O` t m) (t m)
liftF op = hmap from . algLift (runOp op) liftT . O . fmap (hmap liftT) . unO
