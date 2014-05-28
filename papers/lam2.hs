import Control.Monad
import Data.List

class Eq1 f where
  (==#) :: Eq a => f a -> f a -> Bool
class Show1 f where
  showsPrec1 :: Show a => Int -> f a -> ShowS
  showList1 :: (Show a) => [f a] -> ShowS
  showList1 ls s = showList__ shows1 ls s
showList__ :: (a -> ShowS) -> [a] -> ShowS
showList__ _ [] s = "[]" ++ s
showList__ showx (x:xs) s = '[' : showx x (showl xs)
  where
    showl [] = ']' : s
    showl (y:ys) = ',' : showx y (showl ys)
show1 :: (Show1 f, Show a) => f a -> String
show1 x = shows1 x ""

shows1 :: (Show1 f, Show a) => f a -> ShowS
shows1 = showsPrec1 0

class Bound t where
  (>>>=) :: Monad f => t f a -> (a -> f b) -> t f b

data Empty
instance Show Empty where show = undefined

data Var b a = B b | F a deriving (Eq, Show)
instance Functor (Var b) where
  fmap f (B b) = B b
  fmap f (F x) = F (f x)

newtype Scope b f v = Scope { unscope :: f (Var b v) }
instance Functor f => Functor (Scope b f) where
  fmap f (Scope ma) = Scope (fmap (fmap f) ma)
instance (Eq b, Eq1 f, Eq a) => Eq (Scope b f a) where
  Scope x == Scope y = x ==# y
instance (Show b, Show1 f, Show a) => Show (Scope b f a) where
  show (Scope x) = "{" ++ show1 x ++ "}"

instance Monad f => Monad (Scope b f) where
  return = Scope . return . F
  Scope e >>= f = Scope $ e >>= \v -> case v of
    F x -> unscope (f x)
    B b -> return (B b)
instance Bound (Scope b) where
  Scope e >>>= f = Scope $ e >>= \v -> case v of
    F x -> liftM F (f x)
    B b -> return (B b)

abstract :: Monad f => (v -> Maybe b) -> f v -> Scope b f v
abstract f e = Scope (e >>= subst) where
  subst x = case f x of
    Just y  -> return (B y)
    Nothing -> return (F x)
abstract1 x = abstract (\y -> if x == y then Just () else Nothing)

instantiate :: Monad f => (b -> f v) -> Scope b f v -> f v
instantiate k (Scope e) = e >>= \v -> case v of
  B b -> k b
  F v -> return v
instantiate1 e = instantiate (const e)

data Const = ZZ Int | BB Bool deriving (Eq, Show)
data E v = Const Const
         | V v
         | E v :@ E v
         | Abs (Scope () E v)
         | Cond (E v) (E v) (E v)
         | Letrec (Scope Int E v) (Scope () E v)
         deriving Show
instance Functor E where
  fmap f (Const c) = Const c
  fmap f (V v) = V (f v)
  fmap f (e1 :@ e2) = fmap f e1 :@ fmap f e2
  fmap f (Abs e) = Abs (fmap f e)
  fmap f (Cond b c a) = Cond (fmap f b) (fmap f c) (fmap f a)
  fmap f (Letrec g e) = Letrec (fmap f g) (fmap f e)
instance Show1 E where showsPrec1 = showsPrec
instance Monad E where
  return = V
  Const c >>= f = Const c
  V x >>= f = f x
  e1 :@ e2 >>= f = (e1 >>= f) :@ (e2 >>= f)
  Abs e >>= f = Abs (e >>>= f)
  Cond b c a >>= f = Cond (b >>= f) (c >>= f) (a >>= f)
  Letrec g e >>= f = Letrec (g >>>= f) (e >>>= f)

letrec :: Eq v => v -> v -> E v -> E v -> E v
letrec f x e b = Letrec (abstract (`elemIndex` [f,x]) e) (abstract1 f b)

data Val = C Const | Fun (Val -> Val) | Var String
instance Show Val where show = show . reflect

reflect :: Val -> E String
reflect = re vars where
  vars = map (:[]) ['a'..'z'] ++ [c:show n | n <- [0..], c <- ['a'..'z']]
  re vs     (Var x) = V x
  re vs     (C c)   = Const c
  re (v:vs) (Fun f) = Abs (abstract1 v (re vs (f (Var v))))

var = V . F
alloc = var . length

eval :: (Val -> Val) -> [Val] -> E (Var Empty Int) -> Val
eval k p (V (F x)) = k $ p !! (length p - x - 1)
eval k p (Const r) = k (C r)
eval k p (f :@ e) = eval (\(Fun f) -> k $ eval f p e) p f
eval k p (Abs e) = k . Fun  $ \x -> eval k (x:p) (instantiate1 (alloc p) e)
eval k p (Cond b c a) = eval (\(C (BB b)) -> if b then eval k p c else eval k p a) p b
eval k p (Letrec f e) = eval k (step k p f:p) (instantiate1 (alloc p) e)
  where step k p b = Fun (\x -> eval k (x:step k p b:p) $ instantiate (subst p) b)
        subst p 0 = var (length p+1)
        subst p 1 = var (length p)

zz = Const . ZZ
dec = Fun (\(C (ZZ n)) -> C . ZZ $ if n == 0 then 0 else n-1)
isZ = Fun (\(C (ZZ n)) -> C . BB $ n == 0)

toZero = letrec "f" "x" (Cond (V "isZ" :@ V "x") (V "x") (V "f" :@ (V "dec" :@ V "x"))) $
           V "f" :@ zz 3

run :: E String -> Val
run = eval id (map snd p0) . fmap initEnv
  where fromJust (Just x) = x
        p0 = [("isZ", isZ), ("dec", dec)]
        initEnv x = F $ length p0 - fromJust (elemIndex x (map fst p0)) :: Var Empty Int

main = putStrLn . show . reflect . run $ toZero
