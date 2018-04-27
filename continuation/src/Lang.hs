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

tr s = unsafePerformIO $ putStrLn s


data Exp (tp :: Ty) where
    -- only for printing
    Var :: String -> TyRepr tp -> Exp tp
    Tup :: Exp tp -> Exp tp2 -> Exp (tp ** tp2)
    PiL :: Exp (tp ** tp2) -> Exp tp
    PiR :: Exp (tp ** tp2) -> Exp tp2
    Const :: String -> TyRepr tp -> Exp tp
    Lam :: KnownTy tp => (Exp tp -> Exp tp2) -> Exp (tp --> tp2)
    App :: Exp (tp --> tp2) -> Exp tp -> Exp tp2

varStream :: [String]
varStream = baseVars ++ (map (\i -> "x" ++ (show i)) [0,1]) -- TODO I'm not taking advantage of laziness properly
    where
        baseVars = ["x", "y", "z", "a", "b", "c", "d", "e"]
                            
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

freshNames :: Exp tp -> [String]
freshNames (Var x _) = filter (/= x) varStream
freshNames (Const x _) = filter (/= x) varStream
freshNames (Lam f) = freshNames $ f (Var "!" knownRepr)
freshNames (App f e) = intersect (freshNames f) (freshNames e) 
freshNames (Tup f e) = intersect (freshNames f) (freshNames e) 
freshNames (PiL p) = freshNames p
freshNames (PiR p) = freshNames p


freshName :: Exp tp -> [String] -> String
freshName e used = head $ take 1 $ (freshNames e) \\ used

-- list argument keeps track of names used
ppExp :: Exp tp -> [String] -> String
ppExp (Var x _) _ = x
ppExp (Const x _) _ = x
ppExp e@(Lam f) used =
    "λ " ++ (ppExp (Var x t) used) 
    -- ++ ": " ++ (show t) 
    ++ ". " ++ (ppExp (f (Var x knownRepr)) (x : used))
        where x = freshName e used
ppExp (App f e) used = "(" ++ (ppExp f used) ++ ") (" ++ (ppExp e used) ++ ")"
ppExp (Tup p1 p2) used = "(" ++ (ppExp p1 used) ++ ", " ++ (ppExp p2 used) ++ ")"
ppExp (PiL p) used = (ppExp p used) ++ "#1"
ppExp (PiR p) used = (ppExp p used) ++ "#2"

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



type M r s a = ReaderT (Exp s) (Cont (Exp r)) (Exp a)
type N r s a = ContT (Exp r) (Reader (Exp s)) (Exp a)
             

everyone' = Const "everyone" ((e ==> t) ==> t)
ieveryone = Const "everyone" ((e ==> s ==> t) ==> t)

everyone :: M T S E
everyone = do
    lift $ ContT $ \f ->
        return $ App everyone' (toExp f)

everyone2 :: N T S E
everyone2 = do
    ContT $ \f ->
        return $ App ieveryone (toExp f)


left = \e -> App (Const "left" (ERepr ==> TRepr)) e

john = Const "john" ERepr

everyone_left :: M T S T
everyone_left = do
    e <- everyone
    l <- return left
    return $ l e

everyone_left2 :: N T S T
everyone_left2 = do
    e <- everyone2
    l <- return left
    return $ l e







simpl :: Exp t2 -> Exp t2
simpl (App f e) =
    case simpl f of
      Lam b -> simpl (b e)
      _ -> App (simpl f) (simpl e)
simpl (Lam f) =
    Lam  (\x -> simpl (f x))
simpl e = e






{-
   manual continuation combinators

sent = kap2 everyone' (kret left')

type M a b c = ((c --> b) --> a)
mRepr a b c = ((c ==> b) ==> a)

kbind :: (KnownTy e1, KnownTy e2, KnownTy c) => Exp (M a b e1) -> (Exp (e1 --> M b c e2)) -> Exp (M a c e2)
kbind m f =
    Lam $ \k -> App m (Lam $ \x -> App (App f x) k)

klower :: (KnownTy a) => Exp (M e a a) -> Exp e
klower m = App m (Lam $ \x -> x)

kret :: (KnownTy e, KnownTy a) => Exp e -> Exp (M a a e)
kret e = Lam $ \k -> App k e

-- combl
kap :: (KnownTy e1, KnownTy e2, KnownTy c) => Exp (M a b (e1 --> e2)) -> Exp (M b c e1) -> Exp (M a c e2)
kap mf ma =
    kbind mf (Lam $ \f ->
        kbind ma (Lam $ \a -> 
            kret (App f a)))

-- combr
kap2 :: (KnownTy a, KnownTy b, KnownTy e) => Exp (M c d a) -> Exp (M d e (a --> b)) -> Exp (M c e b)
kap2 ma mf =
    Lam $ \k ->
        App ma (Lam $ \x -> App mf (Lam $ \g -> App k (App g x)))
        -}
