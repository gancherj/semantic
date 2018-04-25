module Lang where

import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Data.Parameterized.Context as C
import Data.Parameterized.Classes
import Data.Parameterized.Some
import Data.Parameterized.Ctx
import Data.List
import System.IO.Unsafe
import Types

tr s = unsafePerformIO $ putStrLn s

-- TODO: interpret sets as predicates, instead of as lists.

data Exp (tp :: Ty) where
    -- only for printing
    Var :: String -> TyRepr tp -> Exp tp
    Const :: String -> TyRepr tp -> Exp tp
    Lam :: TyRepr tp -> (Exp tp -> Exp tp2) -> Exp (tp --> tp2)
    App :: Exp (tp --> tp2) -> Exp tp -> Exp tp2

varStream :: [String]
varStream = baseVars ++ (map (\i -> "x" ++ (show i)) [0,1]) -- TODO I'm not taking advantage of laziness properly
    where
        baseVars = ["x", "y", "z", "a", "b", "c", "d", "e"]
                            
typeOf :: Exp tp -> TyRepr tp
typeOf (Var _ t) = t
typeOf (Const _ t) = t
typeOf (Lam t f) = t ==> t2
    where t2 = typeOf $ f (Var "!" t)
typeOf (App f _) =
    case typeOf f of
      (ArrowRepr t t2) -> t2

freshNames :: Exp tp -> [String]
freshNames (Var x _) = filter (/= x) varStream
freshNames (Const x _) = filter (/= x) varStream
freshNames (Lam t f) = freshNames $ f (Var "!" t)
freshNames (App f e) = intersect (freshNames f) (freshNames e) 


freshName :: Exp tp -> [String] -> String
freshName e used = head $ take 1 $ (freshNames e) \\ used

-- list argument keeps track of names used
ppExp :: Exp tp -> [String] -> String
ppExp (Var x _) _ = x
ppExp (Const x _) _ = x
ppExp e@(Lam t f) used =
    "λ " ++ (ppExp (Var x t) used) 
    -- ++ ": " ++ (show t) 
    ++ ". " ++ (ppExp (f (Var x t)) (x : used))
        where x = freshName e used
ppExp (App f e) used = "(" ++ (ppExp f used) ++ ") (" ++ (ppExp e used) ++ ")"


instance Show (Exp tp) where
    show e = ppExp e []



type M a b c = ((c --> b) --> a)
mRepr a b c = ((c ==> b) ==> a)


kbind :: (KnownTy e1, KnownTy e2, KnownTy c) => Exp (M a b e1) -> (Exp (e1 --> M b c e2)) -> Exp (M a c e2)
kbind m f =
    Lam (knownRepr ==> knownRepr) $ \k -> App m (Lam knownRepr $ \x -> App (App f x) k)

klower :: (KnownTy a) => Exp (M e a a) -> Exp e
klower m = App m (Lam knownRepr $ \x -> x)

kret :: (KnownTy e, KnownTy a) => Exp e -> Exp (M a a e)
kret e = Lam knownRepr $ \k -> App k e

-- combl
kap :: (KnownTy e1, KnownTy e2, KnownTy c) => Exp (M a b (e1 --> e2)) -> Exp (M b c e1) -> Exp (M a c e2)
kap mf ma =
    kbind mf (Lam knownRepr $ \f ->
        kbind ma (Lam knownRepr $ \a -> 
            kret (App f a)))

-- combr
kap2 :: (KnownTy a, KnownTy b, KnownTy e) => Exp (M c d a) -> Exp (M d e (a --> b)) -> Exp (M c e b)
kap2 ma mf =
    Lam knownRepr $ \k ->
        App ma (Lam knownRepr $ \x -> App mf (Lam knownRepr $ \g -> App k (App g x)))
             

everyone = Const "everyone" ((ERepr ==> TRepr) ==> TRepr)
left = Const "left" (ERepr ==> TRepr)

sent = kap2 everyone (kret left)



--kap :: M a b (e1 --> e2) -> M b c e1 -> M a c e2
--kap mf ma =




-- a >>= (\x. b x >>= f)
-- (a >>= b) >>= f

simpl :: Exp t2 -> Exp t2
simpl (App f e) =
    case simpl f of
      Lam t b -> simpl (b e)
      _ -> App (simpl f) (simpl e)
simpl (Lam t f) =
    Lam t (\x -> simpl (f x))
simpl e = e






