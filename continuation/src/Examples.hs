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

he :: Int -> M E
he i = do
    g <- get
    return $ Get i g

push :: MonadState (Exp G) m => Exp E -> m ()
push e = do
    g <- get
    put $ Push e g

person :: MonadReader (Exp S) m => m (Exp (E --> T))
person = do
    (App (Const "person" knownRepr)) <$> curWorld

every :: M E
every = ContT $ liftForall knownRepr


combres :: Monad m => ContT (Exp T) m a -> (a -> m (Exp T)) -> (Exp T -> Exp T -> Exp T) -> ContT (Exp T) m a
combres me mf comb =
    ContT $ \f ->
        runContT me $ \e -> do
            liftM2 comb (mf e) (f e)

substWorld :: M a -> Exp S -> M a
substWorld m w = 
    ContT $ \f -> 
        ReaderT $ \_ ->
            runReaderT (runContT m f) w

-- TODO: Have the verb be a haskell function. Descend the forall to be only the part that quantifies over s.
--
--


bdi :: M (S --> E --> S --> T) -> M E -> M T -> M T
bdi m mx t = do
    x <- mx 
    liftForall knownRepr $ \v -> do
        liftM2 Implies
          (m <**> curWorld <**> (return x) <**> (return v))
          (substWorld t v)

believe = bdi (return (Const "believe" knownRepr))
know = bdi (return (Const "know" knownRepr))
want = bdi (return (Const "want" knownRepr))
desire = bdi (return (Const "desire" knownRepr))

wonders_if :: M E -> M T -> M T
wonders_if x t =
    want x (know x t)

everyone :: M E
everyone = 
    combres every (\e -> person <**> (return e)) Implies

some :: M E
some = ContT $ liftExists knownRepr

someone :: M E
someone = combres some (\e -> person <**> (return e)) And

admire :: M (E --> E --> T)
admire =
    (App (Const "admire" knownRepr)) <$> curWorld

asleep :: M (E --> T)
asleep =
    (App (Const "asleep" knownRepr)) <$> curWorld


left :: M (E --> T)
left = 
    (App (Const "left" knownRepr)) <$> curWorld

to_be :: M T -> M T
to_be = id

john :: M E
john = do 
    w <- curWorld
    let j = App (Const "john" (ss ==> ee)) w
    push j
    return j

everyone_left :: M T
everyone_left = 
    (fromExp <$> left) <*> everyone

john_wanted_john_to_be_asleep :: M T
john_wanted_john_to_be_asleep =  want john (asleep  <**> john)
    

john_left :: M T
john_left =
    (fromExp <$> left) <*> john

john_admires_everyone :: M T
john_admires_everyone =
    admire <**> john <**> everyone

everyone_admires_everyone :: M T
everyone_admires_everyone =
    admire <**> everyone <**> everyone

someone_admires_everyone :: M T
someone_admires_everyone =
    admire <**> someone <**> everyone

everyone_admires_someone :: M T
everyone_admires_someone =
    admire <**> everyone <**> someone

someone_admires_someone :: M T
someone_admires_someone =
    admire <**> someone <**> someone

john_wonders_if_everyone_admires_someone :: M T
john_wonders_if_everyone_admires_someone =
    wonders_if john $ admire <**> everyone <**> someone

john_wonders_if_true :: M T
john_wonders_if_true =
    wonders_if john truth
