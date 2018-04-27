module Examples where
import Lang
import Types
import Data.Parameterized.Classes
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Cont


curWorld :: MonadReader (Exp S) m => m (Exp S)
curWorld = ask

(<**>) :: (KnownTy a, Monad m) => m (Exp (a --> b)) -> m (Exp a) -> m (Exp b)
(<**>) f g = (fromExp <$> f) <*> g

truth :: Monad m => m (Exp T)
truth = return $ Const "true" knownRepr

person :: MonadReader (Exp S) m => m (Exp (E --> T))
person = do
    (App (Const "person" knownRepr)) <$> curWorld

every :: N T S E
every = ContT $ liftForall


combres :: Monad m => ContT (Exp T) m a -> (a -> m (Exp T)) -> (Exp T -> Exp T -> Exp T) -> ContT (Exp T) m a
combres me mf comb =
    ContT $ \f ->
        runContT me $ \e -> do
            liftM2 comb (mf e) (f e)

substWorld :: N T S a -> Exp S -> N T S a
substWorld m w = 
    ContT $ \f -> 
        ReaderT $ \_ ->
            runReaderT (runContT m f) w

bdi :: N T S (S --> E --> S --> T) -> N T S E -> N T S T -> N T S T
bdi m x t = 
    liftForall $ \v -> do
        liftM2 Implies
          (m <**> curWorld <**> x <**> (return v))
          (substWorld t v)

believe = bdi (return (Const "believe" knownRepr))
know = bdi (return (Const "know" knownRepr))
want = bdi (return (Const "want" knownRepr))
desire = bdi (return (Const "desire" knownRepr))

wonders_if :: N T S E -> N T S T -> N T S T
wonders_if x t =
    want x (know x t)

everyone :: N T S E
everyone = 
    combres every (\e -> person <**> (return e)) Implies

some :: N T S E
some = ContT liftExists

someone :: N T S E
someone = combres some (\e -> person <**> (return e)) And

admire :: N T S (E --> E --> T)
admire =
    (App (Const "admire" knownRepr)) <$> curWorld


left :: N T S (E --> T)
left = 
    (App (Const "left" knownRepr)) <$> curWorld


john :: N T S E
john = 
    (App (Const "john" knownRepr)) <$> curWorld

everyone_left :: N T S T
everyone_left = 
    (fromExp <$> left) <*> everyone

john_left :: N T S T
john_left =
    (fromExp <$> left) <*> john

john_admires_everyone :: N T S T
john_admires_everyone =
    admire <**> john <**> everyone

everyone_admires_everyone :: N T S T
everyone_admires_everyone =
    admire <**> everyone <**> everyone

someone_admires_everyone :: N T S T
someone_admires_everyone =
    admire <**> someone <**> everyone

everyone_admires_someone :: N T S T
everyone_admires_someone =
    admire <**> everyone <**> someone

someone_admires_someone :: N T S T
someone_admires_someone =
    admire <**> someone <**> someone

john_wonders_if_everyone_admires_someone :: N T S T
john_wonders_if_everyone_admires_someone =
    wonders_if john $ admire <**> everyone <**> someone

john_wonders_if_true :: N T S T
john_wonders_if_true =
    wonders_if john truth
