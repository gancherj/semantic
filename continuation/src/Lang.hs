-- NOTE: The strategy of lifting applicatives does NOT work as expected. They really need to be monads.
-- For this approach to be sound, I need to verify that Cont (Reader (State)) really is a monad.
--
--
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

tr s =
    unsafePerformIO $ putStrLn s


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

    EmptyAssign :: Exp G
    Push :: Exp E -> Exp G -> Exp G
    Get :: Int -> Exp G -> Exp E


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
typeOf (EmptyAssign) = gg
typeOf (Push _ _) = gg
typeOf (Get _ _) = ee

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
freshNames (EmptyAssign) = varStreams
freshNames (Push p p') = varStream_intersect (freshNames p) (freshNames p')
freshNames (Get _ p) = freshNames p


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
ppExp (EmptyAssign) used = "g"
ppExp (Push e g) used = "(" ++ (ppExp e used) ++ ": " ++ (ppExp g used) ++ ")"
ppExp (Get i g) used = (ppExp g used) ++ "[" ++ (show i) ++ "]"

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

type M a = ContT (Exp T) (ReaderT (Exp S) (State (Exp G))) (Exp a)

runM :: Exp S -> Exp G -> M a -> (Exp a -> ReaderT (Exp S) (State (Exp G)) (Exp T)) -> Exp T
runM w g m k =
    evalState (runReaderT (runContT m k) w) g
             

evalGet :: Int -> Exp G -> Maybe (Exp E)
evalGet _ EmptyAssign = Nothing
evalGet 0 (Push e _) = Just e
evalGet i (Push _ g) = evalGet (i - 1) g


simpl :: Exp t2 -> Exp t2
simpl (App f e) =
    case simpl f of
      Lam b -> simpl (b (simpl e))
      _ -> App (simpl f) (simpl e)
simpl (Lam f) =
    Lam  (\x -> simpl (f x))
simpl (Forall f) =
    Forall (simpl f)
simpl (And x y) =
    And (simpl x) (simpl y)
simpl (Implies x y) =
    Implies (simpl x) (simpl y)
simpl (Get i g) =
    case (evalGet i g) of
      Just e -> simpl e
      Nothing -> Get i g
simpl (Tup x y) = Tup (simpl x) (simpl y)
simpl (PiL t) =
    case simpl t of
      Tup x _ -> simpl x
      _ -> PiL $ simpl t
simpl (PiR t) =
    case simpl t of
      Tup _ y -> simpl y
      _ -> PiR $ simpl t

simpl e = e

print_lower :: M T -> String
print_lower e = 
    show $ simpl $
        
        Lam $ \w ->
            App (App (toExp $ runContT e return ) w) EmptyAssign



        

{-
    to encode:
    quantification
    believe / know / wonder / admire
    intensionality
    -}

