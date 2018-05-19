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
    Not :: Exp T -> Exp T
    And :: Exp T -> Exp T -> Exp T
    Or :: Exp T -> Exp T -> Exp T
    Implies :: Exp T -> Exp T -> Exp T
    ListNil :: KnownTy t => Exp (List t)
    ListCons :: Exp t -> Exp (List t) -> Exp (List t)


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
typeOf (Not _) = tt
typeOf (And _ _) = tt
typeOf (Or _ _) = tt
typeOf (ListNil) = knownRepr
typeOf (ListCons _ t) = typeOf t

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
freshNames (Not p) = freshNames p
freshNames (And p p') = varStream_intersect (freshNames p) (freshNames p')
freshNames (Or p p') = varStream_intersect (freshNames p) (freshNames p')
freshNames (Implies p p') = varStream_intersect (freshNames p) (freshNames p')
freshNames ListNil = varStreams
freshNames (ListCons p p') = varStream_intersect (freshNames p) (freshNames p') 


freshName :: Exp tp -> TyRepr tp2 -> [String] -> String -- fresh name from E, at type T, given that I've also used used
freshName e t used =
    let (x,y,z) = varStream_filter (\x -> not $ x `elem` used) (freshNames e) in
    case t of
      ArrowRepr _ _ -> head $ take 1 $ z
      SRepr -> head $ take 1 $ y
      _ -> head $ take 1 $ x



paren :: Bool -> String -> String
paren b s = if b then "(" ++ s ++ ")" else s

prec :: Exp tp -> Int
prec e = case e of
 Lam _ -> 1
 Forall _ -> 1
 Exists _ -> 1
 Implies _ _ -> 2
 Or _ _ -> 2
 And _ _ -> 3
 Not _ -> 4
 PiL _ -> 5
 PiR _ -> 5
 Tup _ _ -> 6
 ListNil -> 8
 ListCons _ _ -> 9
 App _ _ -> 9
 Var _ _ -> 10 
 Const _ _ -> 10 

ppExp :: Exp tp -> [String] -> Int -> String
ppExp e used p = 
    let n = prec e in
    paren (p > n) $
    case e of
      Var x _ -> x
      Const x _ -> x
      Lam f ->
        "λ " ++ x  
        ++ ". " ++ (ppExp (f (Var x xt)) (x : used) (n))
        where x = freshName e xt used
              xt = knownRepr
      App f e ->
          (ppExp f used (n)) ++ " " ++ (ppExp e used (n + 1))
      Tup p1 p2 ->
          "(" ++ (ppExp p1 used (n + 1)) ++ "," ++ (ppExp e used (n + 1)) ++ ")"
      PiL e -> ppExp e used (n + 1) ++ "#1"
      PiR e -> ppExp e used (n + 1) ++ "#2"
      Forall f ->
          "∀" ++ x ++ ". " ++ (ppExp (simpl $ App f (Var x xt)) (x : used) (n + 1)) 
            where x = freshName f xt used
                  xt = knownRepr
      Exists f ->
          "∃" ++ x ++ ". " ++ (ppExp (simpl $ App f (Var x xt)) (x : used) (n + 1)) 
            where x = freshName f xt used
                  xt = knownRepr
      Not f -> "¬" ++ ppExp f used (n + 1)
      And x y -> (ppExp x used (n + 1)) ++ " /\\ " ++ (ppExp y used n)
      Or x y -> (ppExp x used (n + 1)) ++ " \\/ " ++ (ppExp y used n)
      Implies x y -> (ppExp x used (n + 1)) ++ " => " ++ (ppExp y used n)
      ListNil -> "nil"
      ListCons h t -> (ppExp h used (n + 1)) ++ " :: " ++ (ppExp t used (n + 1))


instance Show (Exp tp) where
    show e = ppExp e [] 1


type family Conv t where
    Conv (Exp tp) = tp
    Conv (Identity t) = Conv t
    Conv (t -> t2) = (Conv t) --> (Conv t2)
    Conv (ReaderT t m t2) = Conv (t -> (m t2))
    Conv (StateT t m t2) = Conv (t -> m (t2, t))
    Conv (ContT r m a) = Conv ((a -> m r) -> m r)
    Conv (t,t2) = ((Conv t) ** (Conv t2))
    Conv [t] = List (Conv t)


class ToExp t where
    toExp :: t -> Exp (Conv t)
    fromExp :: Exp (Conv t) -> t

instance ToExp (Exp tp) where
    toExp t = t
    fromExp t = t

instance (ToExp t, KnownTy (Conv t)) => ToExp [t] where
    toExp ls =
        case ls of
          [] -> ListNil
          x:xs -> ListCons (toExp x) (toExp xs)

    fromExp e =
        case e of
          ListNil -> []
          ListCons h t ->
              (fromExp h) : (fromExp t)

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

instance (ToExp t, ToExp s, KnownTy tp, ToExp (m (t, s)), KnownTy (Conv s)) => ToExp (StateT s m t) where
    toExp ma = toExp $ runStateT ma
    fromExp r = StateT $ \s -> fromExp $ App r (toExp s)

instance (KnownTy tp, ToExp t, ToExp (m (Exp tp)), KnownTy (Conv t), KnownTy (Conv (m (Exp tp)))) => ToExp (ContT (Exp tp) m t) where
    toExp ma = toExp $ runContT ma
    fromExp r = ContT $ \f -> fromExp $ App r (toExp f)

type KnownM m t = (ToExp (m (Exp t)), KnownTy (Conv (m (Exp t))))


data MS = MS {
    _erefs :: [Exp E],
    -- Note here the Kleisli arrow is actually necessary. An example is if the et has an embedded pronoun.
    _etrefs :: [Exp E -> M T] }

type Mon a = ContT (Exp T) (ReaderT (Exp S) (State MS)) a
type M a = ContT (Exp T) (ReaderT (Exp S) (State MS)) (Exp a)

runM :: Exp S -> MS -> M a -> (Exp a -> ReaderT (Exp S) (State MS) (Exp T)) -> Exp T
runM w g m k =
    evalState (runReaderT (runContT m k) w) g
             



simpl :: Exp t2 -> Exp t2
simpl (App f e) =
    case simpl f of
      Lam b -> simpl (b (simpl e))
      _ -> App (simpl f) (simpl e)
simpl (Lam f) =
    Lam  (\x -> simpl (f x))
simpl (Forall f) =
    Forall (simpl f)
simpl (Exists f) =
    Exists (simpl f)
simpl (Not f) =
    Not (simpl f)
simpl (And x y) =
    And (simpl x) (simpl y)
simpl (Or x y) =
    Or (simpl x) (simpl y)
simpl (Implies x y) =
    Implies (simpl x) (simpl y)
simpl (Tup x y) = Tup (simpl x) (simpl y)
simpl (PiL t) =
    case simpl t of
      Tup x _ -> simpl x
      _ -> PiL $ simpl t
simpl (PiR t) =
    case simpl t of
      Tup _ y -> simpl y
      _ -> PiR $ simpl t
simpl (ListCons h t) =
    ListCons (simpl h) (simpl t)

simpl e = e

print_lower :: M T -> String
print_lower e = 
    show $ simpl $
            Lam $ \w ->
                runM w (MS [] []) e return



        

{-
    to encode:
    quantification
    believe / know / wonder / admire
    intensionality
    -}

