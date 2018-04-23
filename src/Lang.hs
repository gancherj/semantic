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


data Exp (tp :: Ty) where
    -- only for printing
    Var :: String -> TyRepr tp -> Exp tp
    Const :: String -> TyRepr tp -> Exp tp
    Lam :: TyRepr tp -> (Exp tp -> Exp tp2) -> Exp (tp --> tp2)
    App :: Exp (tp --> tp2) -> Exp tp -> Exp tp2
    Bind :: Exp (Set t) -> Exp (t --> Set t2) -> Exp (Set t2)
    SetLit :: [Exp t] -> Exp (Set t)
    Sat :: Exp (Set T) -> Exp T
    Implies :: Exp T -> Exp T -> Exp T

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
typeOf (Bind _ f) =
    case typeOf f of
      (ArrowRepr t t2) -> t2
typeOf (SetLit xs) = SetRepr $ typeOf $ head xs
typeOf (Sat _) = TRepr
typeOf (Implies _ _) = TRepr

freshNames :: Exp tp -> [String]
freshNames (SetLit ts) = foldl (\acc n -> intersect acc (freshNames n)) varStream ts
freshNames (Var x _) = filter (/= x) varStream
freshNames (Const x _) = filter (/= x) varStream
freshNames (Lam t f) = freshNames $ f (Var "!" t)
freshNames (App f e) = intersect (freshNames f) (freshNames e) 
freshNames (Bind e f) = intersect (freshNames f) (freshNames e) 
freshNames (Implies e f) = intersect (freshNames e) (freshNames f) 
freshNames (Sat t) = freshNames t


freshName :: Exp tp -> [String] -> String
freshName e used = head $ take 1 $ (freshNames e) \\ used

-- list argument keeps track of names used
ppExp :: Exp tp -> [String] -> String
ppExp (Var x _) _ = x
ppExp (Const x _) _ = x
ppExp e@(Lam t f) used =
    "fun " ++ (ppExp (Var x t) used) ++ ": " ++ (show t) ++ " -> " ++ (ppExp (f (Var x t)) (x : used))
        where x = freshName e used
ppExp (App f e) used = "(" ++ (ppExp f used) ++ ") (" ++ (ppExp e used) ++ ")"
ppExp (Bind f e) used = (ppExp f used) ++ " >>= (" ++ (ppExp e used) ++ ")"
ppExp (SetLit ts) used = "{" ++ (concat $ intersperse ", " (map (\t -> ppExp t used) ts)) ++ "}"
ppExp (Sat t) used = "sat " ++ (ppExp t used)
ppExp (Implies x y) used = (ppExp x used) ++ " ==> " ++ (ppExp y used)


instance Show (Exp tp) where
    show e = ppExp e []


--a_rel = Const "a.rel" (SetRepr ERepr)
a_rel = SetLit $ map (\i -> Const i ERepr) ["alice", "bob", "dave"]
dies = Const "dies" (ERepr ==> TRepr)
sif = 
    Lam (SetRepr TRepr) $ \m ->
        Lam (SetRepr TRepr) $ \n ->
            SetLit [Implies (Sat m) (Sat n)]

house = Const "house" TRepr


sent :: Exp (Set T)
sent = Bind (Bind a_rel $ Lam ERepr $ \x -> SetLit [App dies x]) $ Lam TRepr $ \p -> App (App sif (SetLit [p])) (SetLit [house])



beta :: Exp t2 -> Exp t2
beta (App f e) =
    case beta f of
      Lam t b -> (b e)
      _ -> App f (beta e)
beta e@(Bind s f) =
    case (beta s, beta f) of
      (SetLit xs, Lam t b) -> 
          case (simpSets $ map beta $ map b xs) of
            Just ts -> SetLit ts
            Nothing -> Bind (beta s) (beta f) 
      (s', f') -> Bind s' f' 
beta e = e


simpSets :: [Exp (Set t2)] -> Maybe [Exp t2]
simpSets xs = do
    ys <- forM xs $ \y ->
        case y of
          SetLit zs -> Just zs
          _ -> Nothing
    return $ concat ys




