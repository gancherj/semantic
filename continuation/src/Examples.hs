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


(!) :: Int -> [a] -> Maybe a
0 ! (x : xs) = Just x
0 ! [] = Nothing
i ! [] = Nothing
i ! (x : xs) = (i-1) ! xs

curWorld :: MonadReader (Exp S) m => m (Exp S)
curWorld = ask

(<**>) :: (KnownTy a, Monad m) => m (Exp (a --> b)) -> m (Exp a) -> m (Exp b)
(<**>) f g = (fromExp <$> f) <*> g

truth :: Monad m => m (Exp T)
truth = return $ Const "true" knownRepr


getDref :: Int -> Mon (Exp E -> M T)
getDref i = do
    (MS _ fs) <- get
    case (i ! fs) of
      Just f -> return f
      Nothing -> return $ \e -> return $
          App (Const ("g_et(" ++ (show i) ++ ")") knownRepr) e

he :: Int -> M E
he i = do
    (MS g _) <- get
    case (i ! g) of
      Just e -> e
      Nothing -> return $ Const ("g_e (" ++ (show i) ++ ")") ERepr

his :: Int -> (M E -> M E) -> M E
his i f = do
    f (he i)

mother :: M E -> M E
mother x =
    ((App (Const "mother" knownRepr)) <$> curWorld) <**> x

called :: M E -> M E -> M T
called x y =
    ((App (Const "called" knownRepr)) <$> curWorld) <**> x <**> y

push_e :: MonadState MS m => M E -> m ()
push_e e = do
    ms <- get
    put $ ms { _erefs = (e : (_erefs ms)) }

push_et :: MonadState MS m => (Exp E -> M T) -> m ()
push_et et = do
    ms <- get
    put $ ms { _etrefs = (et : (_etrefs ms)) }

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


bdi :: M (S --> E --> S --> T) -> M E -> M T -> M T
bdi m mx t = do
    f <- m
    x <- mx 
    ContT $ \k -> do
        g <- get
        w <- ask
--        if topush then 
--                  push_et $ \e -> Forall $ Lam $ \v ->
--                      Implies (App (App (App f w) e) v)
--                              (runM v g t k)
--                  else return ()
        return $ Forall $ Lam $ \v ->
            Implies (App (App (App f w) x) v)
                    (runM v g t k)

believe' = bdi (return (Const "believe" knownRepr))
know' = bdi (return (Const "know" knownRepr))
want' = bdi (return $ Const "want" knownRepr) 
desire' = bdi (return (Const "desire" knownRepr))

want :: M E -> M T -> M T
want x t = do
    push_et $ \e -> want' (return e) t
    want' x t

wonders_if :: M E -> M T -> M T
wonders_if x t = do
    push_et $ \e -> want' (return e) (know' (return e) t)
    want' x (know' x t)

believes' :: M T -> M E -> M T
believes' mt = mkVerbFrom (go mt)
    where
        go :: M T -> Exp (S --> E --> T)
        go mt = error "unimp"





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
admire = mkVerb2 "admire"

asleep :: M E -> M T
asleep = mkVerb1 "asleep"

actor :: M E -> M T
actor = mkVerb1 "actor"


left :: M E -> M T
left = mkVerb1 "left"

to_be :: M T -> M T
to_be = id


mkVerbFrom :: Exp (S --> E --> T) -> M E -> M T
mkVerbFrom v agent = do
    s <- curWorld
    let t = App v s
    push_et $ \e -> return $ App t e
    e <- agent
    return $ App t e

mkVerb1 :: String -> M E -> M T
mkVerb1 name agent = do
    s <- curWorld
    let t = App (Const name (ss ==> ee ==> tt)) s
    push_et $ \e -> return $ App t e
    e <- agent
    return $ App t e


eflip :: (KnownTy a, KnownTy b) => Exp (a --> b --> c) -> Exp (b --> a --> c)
eflip f =
    Lam $ \a -> Lam $ \b -> App (App f b) a

mkVerb2 :: String -> M E -> M E -> M T
mkVerb2 name agent theme = do
    s <- curWorld
    let verb a t = App (App (App (Const name knownRepr) s) a) t
    -- NOTE: Order here matters. The agent must be bound first.
    a <- agent
    t <- theme
    push_et $ \a -> return $ verb a t
    return $ verb a t

mkE :: String -> M E
mkE s = do
    let (j :: M E) = do
                w <- curWorld
                return $ App (Const s (ss ==> ee)) w
    push_e $ j
    j

john = mkE "john"
bill = mkE "bill"
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

is_such_that :: M a -> (M a -> M T) -> M T
is_such_that ma f = do
    x <- ma
    f (return x)

conj_sent :: M T
conj_sent = 
    conj john_wanted_john_to_be_asleep he_is_asleep

disj_sent :: M T
disj_sent =
    admire (disj john keisha) someone

disj_sent3 :: M T
disj_sent3 =
    is_such_that someone $ admire (disj john keisha)

disj_sent2 :: M T
disj_sent2 =
    called (disj john bill) (his 0 mother)

so_does :: M E -> M T
so_does me = do
    f <- getDref 0
    me >>= f


john_wants_actor :: M T
john_wants_actor =
    want john (actor (he 0))

