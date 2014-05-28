{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}
import Prelude hiding (foldr, sequence)
import Control.Concurrent.MVar
import Control.Concurrent
import Data.Foldable
import Data.Map (Map)
import Data.Maybe (fromJust)
import qualified Data.Map as M
import Prelude.Extras
import Unsafe.Coerce

data Void
instance Show Void where show = undefined
instance Eq Void where (==) = undefined
data Var b a = B b | F a deriving (Eq, Show, Functor, Foldable)

newtype Scope b f a = Scope { unscope :: f (Var b a) }
  deriving (Functor, Foldable)
instance (Show b, Show a, Show1 f) => Show (Scope b f a) where
  show (Scope e) = "{" ++ show1 e ++ "}"
instance (Eq b, Eq a, Eq1 f) => Eq (Scope b f a) where
  Scope e1 == Scope e2 = e1 ==# e2
  
data Pi n = Nu (Scope () Pi n)
          | Rx n (Scope () Pi n)
          | Tx n n
          | Zero
          | Pi n :| Pi n
          | Guard n n (Pi n)
          | Print n
          -- We can just borrow Haskell's functions.
          deriving (Eq, Show, Functor, Foldable)
instance Show1 Pi where showsPrec1 = showsPrec
instance Eq1 Pi where (==#) = (==)

instantiate :: (b -> n) -> Scope b Pi n -> Pi n
instantiate f p = fmap (\v -> case v of
                           B x -> f x
                           F e -> e) (unscope p)
instantiate1 x = instantiate (const x)

abstract :: (n -> Maybe b) -> Pi n -> Scope b Pi n
abstract f e = Scope $ fmap (\v -> case f v of
                                Just x  -> B x
                                Nothing -> F v) e
abstract1 x = abstract (\v -> if v == x then Just () else Nothing)

nu x e = Nu (abstract1 x e)
rx n x e = Rx n (abstract1 x e)

data Free f a = Val a | Roll { unroll :: f (Free f  a) }
  deriving (Functor)
instance (Eq a, Eq1 f) => Eq (Free f a) where
  Val v1  == Val v2  = v1 == v2
  Roll e1 == Roll e2 = e1 ==# e2
  _ == _ = False
instance Eq1 MVar where (==#) = (==)
instance (Show1 f, Show a) => Show (Free f a) where
  show (Val x)  = show x
  show (Roll e) = show1 e
instance Show1 MVar where
  showsPrec1 _ _ _ = "<<MVar>>"

eval :: (Show atom, Eq atom) => Pi (Free MVar atom) -> IO ()
eval (Nu e) = newEmptyMVar >>= \c -> eval (instantiate1 (Roll c) e)
eval (Rx c e) = takeMVar (unroll c) >>= \v -> eval (instantiate1 v e)
eval (Tx c n) = putMVar (unroll c) n
eval Zero = return ()
eval (e1 :| e2) = forkIO (eval e1) >> eval e2
eval (Guard v n e) | v == n    = eval e
                   | otherwise = return ()
eval (Print n) = putStrLn (show n)

evalOpen :: (Ord v, Show v) => Pi (Var Void v) -> IO ()
evalOpen e = do
  ctx <- foldr (\(F v) mm -> mm >>= \m -> case M.lookup v m of
                  Just c  -> return m
                  Nothing -> newEmptyMVar >>= \c ->
                             return (M.insert v (Roll c) m))
           (return (M.empty :: Map v (Free MVar Void))) e
  eval (fmap (\(F v) -> fromJust (M.lookup v ctx)) e)

cases :: n -> [(n, Pi n)] -> Pi n
cases x es = Rx x (Scope (foldr (\(n, e) p -> p :| Guard (B ()) n e) Zero
                            (map (\(n, e) -> (F n, fmap F e)) es)))
(==>) = (,)

chan = F

copy :: Var b String -> Var b String -> Pi (Var b String)
copy y z = cases y
             [chan "T" ==> Tx z (chan "T")
             ,chan "F" ==> Tx z (chan "F")]
and x y z = cases x
              [chan "T" ==> copy y z
              ,chan "F" ==> Tx z (chan "F")]
 
p :: Pi Void
p = unsafeCoerce (nu "x" (rx "x" "y" Zero))

main = print (rx "x" "y" Zero)
