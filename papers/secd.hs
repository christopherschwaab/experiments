{-# LANGUAGE DeriveFunctor #-}
import Prelude hiding (abs)
import Data.Maybe
import Data.List
import Debug.Trace

newtype Scope f v = Scope (f v) deriving (Eq, Show, Functor)
data Var v = B Int | F v deriving (Eq, Show, Functor)
newtype Addr = Addr Int deriving (Eq, Show)
data Const = N Int deriving (Eq, Show)
data Syscall = Mul1 Int
             | Mul2
             | Pred
             | IsZ
             deriving (Eq, Show)
data AE v = Var (Var v)
          | Const Const
          | Abs (Scope AE v)
          | AE v :@ AE v
          | Native Syscall
          | Lazy (AE v)
          deriving (Eq, Show, Functor)

data PE = PConst Const
        | PClosure (Env, Scope AE Addr)
        | PNative Syscall
        | PLazy (Env, AE Addr)
        deriving (Eq, Show)

type Stack = [PE]
type Env = [PE]
data Ctl v = Ap | T (AE v) deriving (Eq, Show, Functor)
data Dump v = State (Stack, Env, [Ctl v], Dump v) | Empty deriving (Eq, Show)
type SECD = Dump Addr

prettyP (PLazy (e, ae)) =
  "[" ++ intercalate "; " (map prettyP e) ++ " |-" ++ pretty ae ++ "]"
prettyP (PNative c) = show c
prettyP (PConst c) = show c
prettyP (PClosure (e, Scope ae)) =
  "(" ++ intercalate "; " (map prettyP e) ++ " |- " ++ pretty ae ++ ")"

pretty (Var (B n))     = "{" ++ show n ++ "}"
pretty (Var (F x))     = show x
pretty (Const (N n))   = show n
pretty (Abs (Scope t)) = "(\\." ++ pretty t ++ ")"
pretty (f :@ x)        = "(" ++ pretty f ++ " " ++ pretty x ++ ")"
pretty (Native c)      = "*" ++ show c
pretty (Lazy t)        = "[" ++ pretty t ++ "]"

prettyE (T ae)  = pretty ae
prettyE Ap = "Ap"
prettyState (State (s, e, c, d)) =
  unlines ["---------------"
          ,"Stack: " ++ intercalate "; " (map prettyP s)
          ,"Env: " ++ show e
          ,"Ctl: " ++ intercalate "; " (map prettyE c)
          ,"Dump: " ++ show d]

coerceClosed :: AE v -> AE Addr
coerceClosed = fmap (\_ -> error "error: attempt to evaluate open term, exiting...")

abstract :: Eq v => v -> AE v -> Scope AE v
abstract x t = Scope (abstract' 0 t) where
  abstract' n (Var (F v)) | v == x    = Var (B n)
                          | otherwise = Var (F v)
  abstract' n y@(Var{})       = y
  abstract' n (Const c)       = Const c
  abstract' n (Abs (Scope t)) = Abs . Scope $ abstract' (n+1) t
  abstract' n (f :@ t)        = abstract' n f :@ abstract' n t
  abstract' n (Lazy f)        = Lazy (abstract' n f)
  abstract' n (Native f)      = Native f

instantiate :: AE v -> Scope AE v -> AE v
instantiate t (Scope f) = instantiate' 0 f where
  instantiate' n (Var (B v)) | v == n    = t
                             | otherwise = Var (B v)
  instantiate' n y@(Var{})       = y
  instantiate' n (Const c)       = Const c
  instantiate' n (Abs (Scope t)) = Abs . Scope $ instantiate' (n+1) t
  instantiate' n (f :@ t)        = instantiate' n f :@ instantiate' n t
  instantiate' n (Lazy f)        = Lazy (instantiate' n f)
  instantiate' n (Native f)      = Native f

toAE :: PE -> AE Addr
toAE (PConst c) = Const c
toAE (PClosure (e, Scope ae)) = foldr (\v ae -> instantiate v (Scope ae)) ae (map toAE e)
toAE (PNative c) = Native c

var = Var . F
abs x t = Abs (abstract x t)
nat = Const . N
native f x = Native f :@ x

constructclosure p t = PClosure (p, t)
derive = (:)
val p (Addr a) = p !! (length p - a - 1)

alloc = var . Addr . length

runSyscall IsZ (PConst (N 0)) = Abs (Scope (Abs (Scope (Var (B 1)))))
runSyscall IsZ (PConst (N n)) = Abs (Scope (Abs (Scope (Var (B 0)))))
runSyscall Pred (PConst (N n)) = Const . N $ n - 1
runSyscall Mul2 (PConst (N n)) = coerceClosed . abs "x" $ Native (Mul1 n) :@ var "x"
runSyscall (Mul1 m) (PConst (N n)) = Const $ N (m * n)
runSyscall f (PClosure (e, Scope ae)) = Native f :@ (ae :@ Const (N 0))
runSyscall f x = error (show $ (f, x))

step :: SECD -> SECD
step (State (PLazy (te, t) : s', e, [], d)) =
  State ([], te, [T t], State (s', e, [], d))
step (State (s, e, [], State (s', e', c', d'))) = State (head s : s', e', c', d')
step (State (s, e, T ae : c', d)) = case ae of
  Var (B n)     -> error ("oops: " ++ show n)
  Var (F a)     -> State (val e a : s, e, c', d)
  Const k       -> State (PConst k : s, e, c', d)
  Abs t         -> State (constructclosure e t : s, e, c', d)
  Native f      -> State (PNative f : s, e, c', d)
  Lazy t        -> State (PLazy (e, t) : s, e, c', d)
  f :@ t        -> State (s, e, T t : T f : Ap : c', d)
step (State (PNative f : PLazy (te, t) : s', e, Ap : c', d)) =
  State ([], te, [T t, T (Native f), Ap], State (s', e, c', d))
step (State (PNative f : t : s', e, Ap : c', d)) =
  State (s', e, T (runSyscall f t) : c', d)
step (State (PLazy (fe, f) : t : s', e, Ap : c', d)) =
  State ([t], fe, [T f, Ap], State (s', e, c', d))
step (State (f : t : s', e, Ap : c', d)) = case f of
  PClosure (e', x') ->
    let bodyX' = instantiate (alloc e') x'
    in State ([], derive t e', [T bodyX'], State (s', e, c', d))
  _ ->
    error ("error: can't apply non-functional '" ++ show f ++
           "' to '" ++ show t ++ "', exiting...")

eval :: SECD -> SECD
eval st@(State (_, _, [], Empty)) = st
eval st = eval (step st)

toSecd :: AE v -> SECD
toSecd t = State ([], [], [T (coerceClosed t)], Empty)

evalAE :: AE v -> SECD
evalAE = eval . toSecd

ident = abs "x" (var "x")
t0 = (ident :@ ident) :@ nat 3

bnd = Var . B
y = abs "f" ((abs "x" $ var "f" :@ Lazy (var "x" :@ var "x")) :@
             (abs "x" $ var "f" :@ Lazy (var "x" :@ var "x")))
lg = abs "fac" . abs "x" $
       Native IsZ :@ (var "x") :@
         Const (N 1) :@
         Lazy (Native Mul2 :@
                 var "x" :@
                 (var "fac" :@ (Native Pred :@ (bnd 0))))
go = evalAE $ y :@ lg :@ nat 5

y' = abs "f" $ (abs "x" $ var "f" :@ (abs "v" $ ((var "x" :@ var "x") :@ var "v"))) :@
               (abs "x" $ var "f" :@ (abs "v" $ ((var "x" :@ var "x") :@ var "v")))

g = abs "fac" . abs "x" $
      Native IsZ :@ (var "x") :@
        Const (N 1) :@
        (Native Mul2 :@
          var "x" :@
          (var "fac" :@ (Native Pred :@ (bnd 0))))
go' = toSecd (y' :@ g :@ nat 5)

u = (abs "h" . abs "F" $ var "F" :@ (abs "x" $ var "h" :@ var "h" :@ var "F" :@ var "x")) :@
    (abs "h" . abs "F" $ var "F" :@ (abs "x" $ var "h" :@ var "h" :@ var "F" :@ var "x"))
gou = toSecd $ u :@ g :@ nat 0
