module Types where
import Data.Parameterized.Classes

import Data.Type.Equality

data Ty = E | S | T | Arrow Ty Ty | Pair Ty Ty
    deriving (Eq, Show)

type E = 'E
type T = 'T
type S = 'S
type Arrow = 'Arrow
type Pair = 'Pair

infixr 1 -->
type (-->) = Arrow
type (**) = Pair



data TyRepr (t :: Ty) where
    ERepr :: TyRepr E
    TRepr :: TyRepr T
    SRepr :: TyRepr S
    ArrowRepr :: TyRepr t1 -> TyRepr t2 -> TyRepr (Arrow t1 t2)
    PairRepr :: TyRepr t1 -> TyRepr t2 -> TyRepr (Pair t1 t2)


instance Show (TyRepr t) where
    show ERepr = "E"
    show TRepr = "T"
    show SRepr = "S"
    show (ArrowRepr t1 t2) = "(" ++ (show t1) ++ " -> " ++ (show t2) ++ ")"
    show (PairRepr t1 t2) = (show t1) ++ " * " ++ (show t2)

ee = ERepr
tt = TRepr
ss = SRepr

infixr 1 ==>
(==>) = ArrowRepr


instance KnownRepr TyRepr E where knownRepr = ERepr
instance KnownRepr TyRepr T where knownRepr = TRepr
instance KnownRepr TyRepr S where knownRepr = SRepr
instance (KnownRepr TyRepr t, KnownRepr TyRepr t2) => KnownRepr TyRepr (t --> t2) where knownRepr = ArrowRepr knownRepr knownRepr
instance (KnownRepr TyRepr t, KnownRepr TyRepr t2) => KnownRepr TyRepr (t ** t2) where knownRepr = PairRepr knownRepr knownRepr

type KnownTy t = KnownRepr TyRepr t

instance TestEquality TyRepr where
    testEquality ERepr ERepr = Just Refl
    testEquality TRepr TRepr = Just Refl
    testEquality SRepr SRepr = Just Refl
    testEquality (PairRepr t1 t2) (PairRepr t1' t2') = do
        Refl <- testEquality t1 t1'
        Refl <- testEquality t2 t2'
        return Refl
    testEquality (ArrowRepr t1 t2) (ArrowRepr t1' t2') = do
        Refl <- testEquality t1 t1'
        Refl <- testEquality t2 t2'
        return Refl
