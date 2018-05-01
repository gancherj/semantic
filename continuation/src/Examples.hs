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

person :: M E -> M T
person mx = do
    ((App (Const "person" knownRepr)) <$> curWorld) <**> mx

every :: M E
every = do
    ContT $ \k -> do
        s <- get
        w <- ask
        return $ Forall $ Lam $ \e -> evalState (runReaderT (k e) w) s

everyone :: M E
everyone = 
    ContT $ \k -> do
        s <- get
        w <- ask
        let t1 e = evalState (runReaderT (k e) w) s
            t2 e = runM w s (person (return e)) return
        return $ Forall $ Lam $ \e -> Implies (t2 e) (t1 e)

noone :: M E
noone =
    ContT $ \k -> do
        t <- runContT someone k
        return $ Not t


substWorld :: M a -> Exp S -> M a
substWorld m w = 
    ContT $ \f -> 
        ReaderT $ \_ ->
            runReaderT (runContT m f) w


bdi :: M (S --> E --> S --> T) -> M E -> M T -> M T
bdi m mx t = do
    f <- m
    x <- mx 
    ContT $ \k -> do
        g <- get
        w <- ask
        return $ Forall $ Lam $ \v ->
            Implies (App (App (App f w) x) v)
                    (runM v g t k)
                    
                    

believe = bdi (return (Const "believe" knownRepr))
know = bdi (return (Const "know" knownRepr))
want = bdi (return $ Const "want" knownRepr) 
desire = bdi (return (Const "desire" knownRepr))

wonders_if :: M E -> M T -> M T
wonders_if x t =
    want x (know x t)

some :: M E
some = do
    ContT $ \k -> do
        s <- get
        w <- ask
        return $ Exists $ Lam $ \e -> evalState (runReaderT (k e) w) s

someone :: M E
someone = 
    ContT $ \k -> do
        s <- get
        w <- ask
        let t1 e = evalState (runReaderT (k e) w) s
            t2 e = runM w s (person (return e)) return
        return $ Exists $ Lam $ \e -> And (t2 e) (t1 e)

admire :: M E -> M E -> M T
admire x y =
    ((App (Const "admire" knownRepr)) <$> curWorld) <**> x <**> y

asleep :: M E -> M T
asleep x =
    ((App (Const "asleep" knownRepr)) <$> curWorld) <**> x


left :: M E -> M T
left x = 
    ((App (Const "left" knownRepr)) <$> curWorld) <**> x

to_be :: M T -> M T
to_be = id

mkE :: String -> M E
mkE s = do
    w <- curWorld
    let j = App (Const s (ss ==> ee)) w
    push j
    return j

john = mkE "john"
keisha = mkE "keisha"

everyone_left :: M T
everyone_left = 
    left everyone

john_wanted_john_to_be_asleep :: M T
john_wanted_john_to_be_asleep =  want john (asleep john)
    

john_left :: M T
john_left =
    left john

john_admires_everyone :: M T
john_admires_everyone =
    admire john everyone

everyone_admires_everyone :: M T
everyone_admires_everyone =
    admire everyone everyone

someone_admires_everyone :: M T
someone_admires_everyone =
    admire someone everyone

everyone_admires_someone :: M T
everyone_admires_someone =
    admire everyone someone

someone_admires_someone :: M T
someone_admires_someone =
    admire someone someone

john_wonders_if_everyone_admires_someone :: M T
john_wonders_if_everyone_admires_someone =
    wonders_if john $ admire everyone someone

john_wonders_if_true :: M T
john_wonders_if_true =
    wonders_if john truth

he_is_asleep :: M T
he_is_asleep =
    asleep (he 0)

conj :: M a -> M a -> M a
conj t1 t2 =
    ContT $ \k -> do
        t1 <- runContT t1 k
        t2 <- runContT t2 k
        return $ And t1 t2

disj :: M a -> M a -> M a
disj t1 t2 =
    ContT $ \k -> do
        t1 <- runContT t1 k
        t2 <- runContT t2 k
        return $ Or t1 t2

conj_sent :: M T
conj_sent = 
    conj john_wanted_john_to_be_asleep he_is_asleep

disj_sent :: M T
disj_sent =
    admire (disj john keisha) someone

