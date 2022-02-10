-- Arrow Monoidal Streams

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
fibonacci = proc () -> do
  rec
    fib <- fby -< (0 , fib + nextFib)
    waitFib <- wait -< fib
    nextFib <- fby -< (1 , waitFib)
  returnA -< fib


liftEffect a = lift (Kleisli a)

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
comp f g = lact (arr $ \a -> ((),a)) (compS f g)



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
tensor f g = lact (arr $ \a -> ((),a)) (tensorS f g)


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
   nowFeedback f = proc ((m,s),x) -> do
     (n,(t,y)) <- f -< (m,(s,x))
     returnA -< ((n,t),y)

fbk :: (Arrow c) => Stream c (s,x) (s,y) -> Stream c x y
fbk t = lact (arr (\() -> ((),undefined))) (fbkS t)

idS :: (Arrow c) => Stream c x x
idS = StreamWithMemory id idS


lift :: (Arrow c) => c x y -> Stream c x y
lift f = StreamWithMemory (id *** f) (lift f)

instance (Arrow c) => Category (Stream c) where
  id = idS
  (.) f g = comp g f

instance (Arrow c) => Arrow (Stream c) where
  arr s = lift $ arr s
  (***) = tensor

instance (Arrow c) => ArrowLoop (Stream c) where
  loop f = fbk $ proc (a,s) -> do
    (t,b) <- f -< (s,a)
    returnA -< (b,t)

delay :: (Arrow c) => Stream c x y -> Stream c x y
delay f = StreamWithMemory (id *** undefined)  f

----------------
-- GENERATORS --
----------------
fby :: (Arrow c) => Stream c (a , a) a
fby = StreamWithMemory (arr $ \((),(x,y)) -> ((),x)) (lift (arr snd))

wait :: (Arrow c) => Stream c a a
wait = fbk (proc (a,b) -> do returnA -< (b,a))

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
