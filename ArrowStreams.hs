-- Arrow Streams

{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE Arrows        #-}


module Main where

import Prelude hiding (id)
import Data.Functor.Identity
import Data.List
import Control.Category
import Control.Arrow
import System.Random
import System.IO.Unsafe


-- Fixpoint equation for monoidal streams. Figure 5.
type Stream c = StreamWithMemory c ()

data StreamWithMemory c n x y where
  StreamWithMemory :: (Arrow c) =>
     c (n , x) (m , y)
    -> StreamWithMemory c m x y
    -> StreamWithMemory c n x y


--------------
-- EXAMPLES --
--------------
fibonacci :: Stream (Kleisli Identity) () Int
fibonacci = fbk $ runitS
  >>> copy                                >>> lunitinvS *** id
  >>> delay (k1 *** wait) *** id
  >>> delay fby *** id
  >>> plus                                >>> lunitinvS
  >>> k0 *** id
  >>> fby
  >>> copy

liftEffect a = lift (Kleisli a)

-- walk :: Stream (Kleisli IO) (()) (Int)
-- walk = fbk $ proc (w, ()) -> do
--     u <- unif -< ()
--     v <- fby -< (0, u + w)
--     returnA -< (v,v)
walk :: Stream (Kleisli IO) (()) (Int)
walk = proc () -> do
  u <- (liftEffect $ \() -> do
           boolean <- randomIO
           return (if boolean then 1 else -1)) -< ()
  rec v <- fby -< (0, u + v)
  returnA -< v


type Urn = [Int]

ehrenfest :: Stream (Kleisli IO) () (Urn,Urn)
ehrenfest = proc () -> do

  rec

    -- The left box is initially empty, the right box is initially full.
    l <- fby -< ([],        leftBox)
    r <- fby -< ([1,2,3,4], rightBox)

    -- We pick a ball uniformly.
    ball <- unif -< ()

    -- And we move it from one box to the other.
    leftBox <- move -< (l, ball)
    rightBox <- move -< (r, ball)

  returnA -< (leftBox,rightBox)

  where
    unif :: Stream (Kleisli IO) () Int
    unif = liftEffect (\() -> randomRIO (1,4))

    empty :: Stream (Kleisli IO) () Urn
    empty = arr (\() -> [])

    full :: Stream (Kleisli IO) () Urn
    full = arr (\() -> [1,2,3,4])

    move :: Stream (Kleisli IO) (Urn, Int) Urn
    move = arr (\(u,i) ->
      if elem i u
        then (delete i u)
        else (insert i u))

--- take 10 <$> run fibonacci
--- take 10 <$> run walk
--- take 10 <$> run ehrenfest



---------------------------
-- THE FEEDBACK CATEGORY --
---------------------------

compS :: (Arrow c) =>
  StreamWithMemory c m x y ->
  StreamWithMemory c n y z ->
  StreamWithMemory c (m , n) x z
compS
  (StreamWithMemory f laterf)
  (StreamWithMemory g laterg) =
  StreamWithMemory
    (proc ((m,n),x) -> do
       (p,y) <- f -< (m,x)
       (q,z) <- g -< (n,y)
       returnA -< ((p,q),z))
    (compS laterf laterg)

comp :: (Arrow c) => Stream c x y -> Stream c y z -> Stream c x z
comp f g = lact lunitinv (compS f g)



tensorS :: (Arrow c) =>
  StreamWithMemory c p x y ->
  StreamWithMemory c p' x' y' ->
  StreamWithMemory c (p , p') (x,x') (y,y')
tensorS
  (StreamWithMemory f laterf)
  (StreamWithMemory g laterg) =
  StreamWithMemory (proc ((m,n),(x,y)) -> do
     (p,z) <- f -< (m,x)
     (q,w) <- g -< (n,y)
     returnA -< ((p,q),(z,w))) (tensorS laterf laterg)

tensor :: Arrow c => Stream c x y -> Stream c x' y' -> Stream c (x,x') (y,y')
tensor f g = lact lunitinv (tensorS f g)


lact :: (Arrow c) => c n m -> StreamWithMemory c m x y -> StreamWithMemory c n x y
lact f (StreamWithMemory now later) = StreamWithMemory ((f *** id) >>> now) later


fbkS :: (Arrow c) =>
  StreamWithMemory c m (s,x) (s,y) ->
  StreamWithMemory c (m, s) x y
fbkS (StreamWithMemory now later) =
  StreamWithMemory (nowFeedback now) (fbkS later)
 where

   -- Definition 5.7. Feedback operation.
   nowFeedback :: (Arrow c) => c (m,(s,x)) (n,(t,y)) -> c ((m,s),x) ((n,t),y)
   nowFeedback f = associnv >>> f >>> assoc

fbk :: (Arrow c) => Stream c (s,x) (s,y) -> Stream c x y
fbk t = lact (arr (\() -> ((),undefined))) (fbkS t)

idS :: (Arrow c) => Stream c x x
idS = StreamWithMemory (id) idS


lift :: (Arrow c) => c x y -> Stream c x y
lift f = StreamWithMemory (id *** f) (lift f)

liftarr :: (Arrow c) => (x -> y) -> Stream c x y
liftarr s = lift $ arr s

instance (Arrow c) => Category (Stream c) where
  id = idS
  (.) f g = comp g f

instance (Arrow c) => Arrow (Stream c) where
  arr = liftarr
  (***) = tensor

instance (Arrow c) => ArrowLoop (Stream c) where
  loop f = fbk $ sigma >>> f >>> sigma


delay :: (Arrow c) => Stream c x y -> Stream c x y
delay f = StreamWithMemory (id *** undefined)  f




------------
-- ARROWS --
------------
assoc :: Arrow c => c (x,(y,z)) ((x,y),z)
assoc = arr $ \(x,(y,z)) -> ((x,y),z)
assocS :: Arrow c => Stream c (x,(y,z)) ((x,y),z)
assocS = lift assoc

associnv :: Arrow c => c ((x,y),z) (x,(y,z))
associnv = arr $ \((x,y),z) -> (x,(y,z))
associnvS :: Arrow c => Stream c ((x,y),z) (x,(y,z))
associnvS = lift $ associnv

lunit :: Arrow c => c ((),a) a
lunit = arr $ \((),a) -> a
lunitS :: Arrow c => Stream c ((),a) a
lunitS = lift $ lunit

lunitinv :: Arrow c => c a ((),a)
lunitinv = arr $ \a -> ((),a)
lunitinvS :: Arrow c => Stream c a ((),a)
lunitinvS = lift $ lunitinv

runit :: Arrow c => c (a,()) a
runit = arr $ \(a,()) -> a
runitS :: Arrow c => Stream c (a,()) a
runitS = lift $ runit

runitinv :: Arrow c => c a (a,())
runitinv = arr $ \a -> (a,())
runitinvS :: Arrow c => Stream c a (a,())
runitinvS = lift $ runitinv


sigma :: Arrow c => c (x,y) (y,x)
sigma = arr $ \(x,y) -> (y,x)

sigmaS :: Arrow c => Stream c (x,y) (y,x)
sigmaS = lift $ sigma


----------------
-- GENERATORS --
----------------
fby :: (Monad t) => Stream (Kleisli t) (a , a) a
fby = StreamWithMemory (Kleisli $ \((),(x,y)) -> pure ((),x)) (lift (arr snd))

copy :: (Monad t) => Stream (Kleisli t) a (a,a)
copy = lift (proc a -> do returnA -< (a,a))


k0,k1,k2 :: (Arrow c) => Stream c () Int
k0 = lift $ arr (\() -> 0)
k1 = lift $ arr (\() -> 1)
k2 = lift $ arr (\() -> 2)

plus :: (Arrow c) => Stream c (Int,Int) Int
plus = lift $ arr (\(a,b) -> a + b)

wait :: (Arrow c) => Stream c a a
wait = fbk sigmaS

------------
-- SYSTEM --
------------

class (Monad m) => IOMonad m where unsafeRun :: m a -> m a
instance IOMonad IO where unsafeRun = unsafeInterleaveIO
instance IOMonad Identity where unsafeRun = id


runUnsafeWithMemory :: (IOMonad t) => m -> StreamWithMemory (Kleisli t) m a b -> [a] -> t [b]
runUnsafeWithMemory m (StreamWithMemory (Kleisli now) later) (a:as) = do
  (n , b)<- now (m , a)
  l <- unsafeRun $ runUnsafeWithMemory n later as
  pure (b : l)

runUnsafe :: (IOMonad t) => Stream (Kleisli t) a b -> [a] -> t [b]
runUnsafe = runUnsafeWithMemory ()

run :: (IOMonad t) => Stream (Kleisli t) () a -> t [a]
run s = runUnsafe s (repeat ())

------------------------------------------

main :: IO ()
main = return ()
