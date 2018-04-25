module Types where
import Data.Parameterized.Classes

import Data.Type.Equality

data Ty = E | T | Arrow Ty Ty 
    deriving (Eq, Show)

type E = 'E
type T = 'T
type Arrow = 'Arrow

infixr 1 -->
type (-->) = Arrow



data TyRepr (t :: Ty) where
    ERepr :: TyRepr E
    TRepr :: TyRepr T
    ArrowRepr :: TyRepr t1 -> TyRepr t2 -> TyRepr (Arrow t1 t2)

instance Show (TyRepr t) where
    show ERepr = "E"
    show TRepr = "T"
    show (ArrowRepr t1 t2) = (show t1) ++ " -> " ++ (show t2)

e = ERepr
t = TRepr

infixr 1 ==>
(==>) = ArrowRepr

instance KnownRepr TyRepr E where knownRepr = ERepr
instance KnownRepr TyRepr T where knownRepr = TRepr
instance (KnownRepr TyRepr t, KnownRepr TyRepr t2) => KnownRepr TyRepr (t --> t2) where knownRepr = ArrowRepr knownRepr knownRepr

type KnownTy t = KnownRepr TyRepr t

instance TestEquality TyRepr where
    testEquality ERepr ERepr = Just Refl
    testEquality TRepr TRepr = Just Refl
    testEquality (ArrowRepr t1 t2) (ArrowRepr t1' t2') = do
        Refl <- testEquality t1 t1'
        Refl <- testEquality t2 t2'
        return Refl
