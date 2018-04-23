module Types where
import Data.Parameterized.Classes

import Data.Type.Equality

data Ty = E | T | Arrow Ty Ty | Set Ty
    deriving (Eq, Show)

type E = 'E
type T = 'T
type Set = 'Set
type Arrow = 'Arrow

infixr 1 -->
type (-->) = Arrow



data TyRepr (t :: Ty) where
    ERepr :: TyRepr E
    TRepr :: TyRepr T
    SetRepr :: TyRepr t -> TyRepr (Set t)
    ArrowRepr :: TyRepr t1 -> TyRepr t2 -> TyRepr (Arrow t1 t2)

instance Show (TyRepr t) where
    show ERepr = "E"
    show TRepr = "T"
    show (SetRepr t) = "{"++(show t)++"}"
    show (ArrowRepr t1 t2) = (show t1) ++ " -> " ++ (show t2)

e = ERepr
t = TRepr
set = SetRepr
infixr 1 ==>
(==>) = ArrowRepr

instance KnownRepr TyRepr E where knownRepr = ERepr
instance KnownRepr TyRepr T where knownRepr = TRepr
instance KnownRepr TyRepr t => KnownRepr TyRepr (Set t) where knownRepr = SetRepr knownRepr
instance (KnownRepr TyRepr t, KnownRepr TyRepr t2) => KnownRepr TyRepr (t --> t2) where knownRepr = ArrowRepr knownRepr knownRepr

type KnownTy t = KnownRepr TyRepr t

instance TestEquality TyRepr where
    testEquality ERepr ERepr = Just Refl
    testEquality TRepr TRepr = Just Refl
    testEquality (SetRepr t) (SetRepr t') = do
        Refl <- testEquality t t'
        return Refl
    testEquality (ArrowRepr t1 t2) (ArrowRepr t1' t2') = do
        Refl <- testEquality t1 t1'
        Refl <- testEquality t2 t2'
        return Refl
