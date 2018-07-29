{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}

-- | Vector samplers with and without replacement. For best results, use 
-- @System.Random.Mersenne.Pure64@ as the random generator.
-- n indicates the size of the source, k the size of the desired sample.
module Data.Vector.Sample 
    ( sampleNoReplace 
    , sampleNoReplaceReservoir
    , sampleNoReplaceIntSet
    , sampleReplace
    ) where

import Control.Monad (when)
import Control.Monad.Random
import Control.Monad.ST
import Control.Monad.State.Strict
import qualified Data.IntSet as IS
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as MG
import System.Random
import System.Random.Mersenne.Pure64

-- | Sampling without replacement. Uses either a generate-check-retry algorithm or reservoir sampling
-- based on the input.
-- Optimized for @System.Random.Mersenne.Pure64.PureMT@ as the randomness generator.
-- Expected O(n). For deterministic O(n), use @sampleNoReplaceReservoir.
sampleNoReplace :: (RandomGen g, G.Mutable v1 ~ G.Mutable v1, G.Vector v1 Int, G.Vector v1 a)
    => g -- ^ The random generator
    -> Int -- ^ The size of the desired sample
    -> v1 a -- ^ The vector to sample
    -> (v1 a, g) -- ^ The vector to sample and a new random seed
sampleNoReplace !seed !n !v
    | n * 1024 <= l = sampleNoReplaceIntSet seed n v
    | otherwise = sampleNoReplaceReservoir seed n v
    where l = G.length v

-- | Sampling without replacement, using reservoir sampling. 
-- Optimized for @System.Random.Mersenne.Pure64.PureMT@ as the randomness generator.
-- O(n)
sampleNoReplaceReservoir :: (RandomGen g, G.Mutable v1 ~ G.Mutable v1, G.Vector v1 a)
    => g
    -> Int
    -> v1 a
    -> (v1 a, g)
sampleNoReplaceReservoir !seed !n !v = runST $ do
    let (initVals, rest) = G.splitAt n v 
    randVals <- G.thaw initVals --take the first n as the initial sample

    seed' <- execStateT (G.imapM_ (resReplace randVals n) rest) seed --element replacement
    flip (,) seed' <$> G.unsafeFreeze randVals
{-# INLINE sampleNoReplaceReservoir #-}

resReplace !randVals !n !i !x = do
    --replace a value at random with prob. (n / (n + i))
    r <- state . runState $ getUpTo (n + i)
    when (r < n) $
        MG.unsafeWrite randVals r x
{-# INLINE resReplace #-}

-- | Sampling without replacement. Draws indicies at random, redrawing if the index is already seen.
-- Liable to run an extremely long time when the sample size is over half the size of the source vector,
-- but extremely fast when the chance of redrawing is low.
sampleNoReplaceIntSet :: (RandomGen g, G.Vector v Int, G.Vector v a)
    => g
    -> Int
    -> v a
    -> (v a, g)
sampleNoReplaceIntSet !seed !n !v = (G.backpermute v rvs, seed')
    where 
        l = G.length v
        (rvs, (seed', _)) = runState (G.replicateM n (getUpToUq l)) (seed, IS.empty)
{-# INLINE sampleNoReplaceIntSet #-}


-- | Sampling with replacement, through index generation.
-- O(k)
sampleReplace :: (RandomGen g, G.Vector v Int, G.Vector v a)
    => g
    -> Int
    -> v a
    -> (v a, g)
sampleReplace !seed !n !v = (G.backpermute v rvs, seed')
    where
        l = G.length v
        (rvs, seed') = runState (G.replicateM n (getUpTo l)) seed

-- | Gets random numbers from @0..l - 1@, and updates the seed. NIH'd for rewrite rules
getUpTo :: (RandomGen g) => Int -> State g Int
getUpTo !l = state $ randomR (0, l - 1)
{-# NOINLINE getUpTo #-}
{-# RULES "getUpTo/PureMT" getUpTo = getUpToMT #-}

-- | @getUpTo@ specialized to @PureMT@
getUpToMT :: Int -> State PureMT Int
getUpToMT !l = state randomInt

-- | Generates random numbers in @0..l@ until an unseen one is found.
getUpToUq :: (RandomGen g) => Int -> State (g, IS.IntSet) Int
getUpToUq !l = do
    (g, seen) <- get
    let (r, g') = randomR (0, l - 1) g
        seen' = IS.insert r seen
    put (g', seen')
    if IS.member r seen
        then getUpToUq l
        else return r
{-# NOINLINE getUpToUq #-}
{-# RULES "getUpToUq/PureMT" getUpToUq = getUpToUqMT #-}

-- | @getUpToUq@, specialized to @PureMT@
getUpToUqMT :: Int -> State (PureMT, IS.IntSet) Int
getUpToUqMT !l = do
    (g, seen) <- get
    let (r_, g') = randomInt g
        r = r `mod` l
        seen' = IS.insert r seen
    put (g', seen')
    if IS.member r seen
        then getUpToUqMT l
        else return r

