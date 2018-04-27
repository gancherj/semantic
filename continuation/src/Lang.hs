module Lang where

import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Cont
import qualified Data.Parameterized.Context as C
import Data.Parameterized.Classes
import Control.Monad.State
import Data.List
import System.IO.Unsafe
import Types


data Exp (tp :: Ty) where
    -- only for printing
    Var :: String -> TyRepr tp -> Exp tp
    Tup :: Exp tp -> Exp tp2 -> Exp (tp ** tp2)
    PiL :: Exp (tp ** tp2) -> Exp tp
    PiR :: Exp (tp ** tp2) -> Exp tp2
    Const :: String -> TyRepr tp -> Exp tp
    Lam :: KnownTy tp => (Exp tp -> Exp tp2) -> Exp (tp --> tp2)
    App :: Exp (tp --> tp2) -> Exp tp -> Exp tp2
    Forall :: KnownTy t => Exp (t --> T) -> Exp T
    Exists :: KnownTy t => Exp (t --> T) -> Exp T
    And :: Exp T -> Exp T -> Exp T
    Implies :: Exp T -> Exp T -> Exp T


type VarStream = ([String], [String], [String]) -- e and wildcard, s, functions
varStreams :: VarStream
varStreams = (baseEVars ++ (map (\i -> "x" ++ (show i)) [0,1]),
             baseSVars ++ (map (\i -> "x" ++ (show i)) [0,1]),
             baseFVars ++ (map (\i -> "x" ++ (show i)) [0,1]))
    where
        baseEVars = ["x", "y", "z", "a", "b", "c"]
        baseSVars = ["w", "v", "u"]
        baseFVars = ["k", "f", "g", "h"]

varStream_filter :: (String -> Bool) -> VarStream -> VarStream
varStream_filter f (a, b, c) =
    (filter f a, filter f b, filter f c)

varStream_intersect :: VarStream -> VarStream -> VarStream
varStream_intersect (x,y,z) (a,b,c) =
    (intersect x a, intersect y b, intersect z c)
                            
typeOf :: Exp tp -> TyRepr tp
typeOf (Var _ t) = t
typeOf (Const _ t) = t
typeOf (Lam f) = knownRepr ==> t2
    where t2 = typeOf $ f (Var "!" knownRepr)
typeOf (App f _) =
    case typeOf f of
      (ArrowRepr t t2) -> t2
typeOf (Tup x y) = PairRepr (typeOf x) (typeOf y)
typeOf (PiL p) =
    case typeOf p of
      PairRepr t _ -> t
typeOf (PiR p) =
    case typeOf p of
      PairRepr _ t -> t
typeOf (Forall _) = tt
typeOf (Exists _) = tt
typeOf (And _ _) = tt

freshNames :: Exp tp -> VarStream
freshNames (Var x _) = varStream_filter (/= x) varStreams
freshNames (Const x _) = varStream_filter (/= x) varStreams
freshNames (Lam f) = freshNames $ f (Var "!" knownRepr)
freshNames (App f e) = varStream_intersect (freshNames f) (freshNames e) 
freshNames (Tup f e) = varStream_intersect (freshNames f) (freshNames e) 
freshNames (PiL p) = freshNames p
freshNames (PiR p) = freshNames p
freshNames (Forall p) = freshNames p
freshNames (Exists p) = freshNames p
freshNames (And p p') = varStream_intersect (freshNames p) (freshNames p')
freshNames (Implies p p') = varStream_intersect (freshNames p) (freshNames p')


freshName :: Exp tp -> TyRepr tp2 -> [String] -> String -- fresh name from E, at type T, given that I've also used used
freshName e t used =
    let (x,y,z) = varStream_filter (\x -> not $ x `elem` used) (freshNames e) in
    case t of
      ArrowRepr _ _ -> head $ take 1 $ z
      SRepr -> head $ take 1 $ y
      _ -> head $ take 1 $ x

-- list argument keeps track of names used
-- TODO make a better printer for this.
ppExp :: Exp tp -> [String] -> String
ppExp (Var x _) _ = x
ppExp (Const x _) _ = x
ppExp e@(Lam f) used =
    "λ " ++ x  
    -- ++ ": " ++ (show t) 
    ++ ". " ++ (ppExp (f (Var x xt)) (x : used))
        where x = freshName e xt used
              xt = knownRepr
ppExp (App f e) used = "(" ++ (ppExp f used) ++ ") (" ++ (ppExp e used) ++ ")"
ppExp (Tup p1 p2) used = "(" ++ (ppExp p1 used) ++ ", " ++ (ppExp p2 used) ++ ")"
ppExp (PiL p) used = (ppExp p used) ++ "#1"
ppExp (PiR p) used = (ppExp p used) ++ "#2"
ppExp (Forall f) used = "∀" ++ x ++ ". [" ++ (ppExp (simpl $ App f (Var x xt)) (x : used)) ++ "]"
    where x = freshName f xt used
          xt = knownRepr
ppExp (Exists f) used = "∃" ++ x ++ ". [" ++ (ppExp (simpl $ App f (Var x xt)) (x : used)) ++ "]"
    where x = freshName f xt used
          xt = knownRepr
ppExp (And x y) used = "(" ++ (ppExp x used) ++ " /\\ " ++ (ppExp y used) ++ ")"
ppExp (Implies x y) used = "(" ++ (ppExp x used) ++ " => " ++ (ppExp y used) ++ ")"

type family Conv t where
    Conv (Exp tp) = tp
    Conv (Identity t) = Conv t
    Conv (t -> t2) = (Conv t) --> (Conv t2)
    Conv (ReaderT t m t2) = Conv (t -> (m t2))
    Conv (StateT t m t2) = Conv (t -> m (t2, t))
    Conv (ContT r m a) = Conv ((a -> m r) -> m r)
    Conv (t,t2) = ((Conv t) ** (Conv t2))

instance Show (Exp tp) where
    show e = ppExp e []

class ToExp t where
    toExp :: t -> Exp (Conv t)
    fromExp :: Exp (Conv t) -> t

instance ToExp (Exp tp) where
    toExp t = t
    fromExp t = t

instance (ToExp t, ToExp t2) => ToExp (t,t2) where
    toExp p = Tup (toExp $ fst p) (toExp $ snd p)
    fromExp p = (fromExp $ (PiL p), fromExp $ (PiR p))
       
instance ToExp t => ToExp (Identity t) where
    toExp t = toExp $ runIdentity t
    fromExp t = return $ fromExp t

instance (ToExp t, ToExp t', KnownTy (Conv t)) => ToExp (t -> t') where
    toExp f = Lam $ \e -> toExp $ f (fromExp e)
    fromExp e = \a -> fromExp $ App e (toExp a)

instance (ToExp t, KnownTy tp, ToExp (m t)) => ToExp (ReaderT (Exp tp) m t) where
    toExp ma = toExp $ runReaderT ma
    fromExp r = ReaderT $ \s -> fromExp $ App r s

instance (ToExp t, KnownTy tp, ToExp (m (t, Exp tp))) => ToExp (StateT (Exp tp) m t) where
    toExp ma = toExp $ runStateT ma
    fromExp r = StateT $ \s -> fromExp $ App r s

instance (KnownTy tp, ToExp t, ToExp (m (Exp tp)), KnownTy (Conv t), KnownTy (Conv (m (Exp tp)))) => ToExp (ContT (Exp tp) m t) where
    toExp ma = toExp $ runContT ma
    fromExp r = ContT $ \f -> fromExp $ App r (toExp f)

type KnownM m t = (ToExp (m (Exp t)), KnownTy (Conv (m (Exp t))))

he :: MonadState ([Exp E]) m => Int -> m (Exp E)
he i = do
    ls <- get
    return $ ls !! i

type M r s a = ReaderT (Exp s) (Cont (Exp r)) (Exp a)
type N r s a = ContT (Exp r) (Reader (Exp s)) (Exp a)
type O a = ContT (Exp T) (ReaderT (Exp S) (State ([Exp E]))) (Exp a)
             
class LiftQuant m where
    liftForall :: KnownTy t => (Exp t -> m (Exp T)) -> m (Exp T)
    liftExists :: KnownTy t => (Exp t -> m (Exp T)) -> m (Exp T)
    

instance LiftQuant Identity where
    liftForall f =
        return $ Forall $ Lam $ \e -> runIdentity (f e)
    liftExists f =
        return $ Exists $ Lam $ \e -> runIdentity (f e)

instance (LiftQuant m, Monad m) => LiftQuant (ReaderT (Exp S) m) where
    liftForall f = do
        s <- ask
        lift $ liftForall $ \e -> runReaderT (f e) s

    liftExists f = do
        s <- ask
        lift $ liftExists $ \e -> runReaderT (f e) s

instance (LiftQuant m) => LiftQuant (ContT (Exp T) m) where
    liftForall f = 
        ContT $ \g -> 
            liftForall $ \e ->
                runContT (f e) g
    liftExists f = 
        ContT $ \g -> 
            liftExists $ \e ->
                runContT (f e) g

simpl :: Exp t2 -> Exp t2
simpl (App f e) =
    case simpl f of
      Lam b -> simpl (b e)
      _ -> App (simpl f) (simpl e)
simpl (Lam f) =
    Lam  (\x -> simpl (f x))
simpl (Forall f) =
    Forall (simpl f)
simpl (And x y) =
    And (simpl x) (simpl y)
simpl (Implies x y) =
    Implies (simpl x) (simpl y)
simpl e = e

print_lower :: N T S T -> String
print_lower e = 
    show $ simpl $ toExp $ runContT e return 



        

{-
    to encode:
    quantification
    believe / know / wonder / admire
    intensionality
    -}
