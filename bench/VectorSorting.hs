----------------------------------------------------------------------------
-- |
-- Module      :  FuzzyBench
-- Copyright   :  (c) Sergey Vinokurov 2022
-- License     :  Apache-2.0 (see LICENSE)
-- Maintainer  :  serg.foo@gmail.com
----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}

{-# OPTIONS_GHC -Wno-orphans        #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-uniques -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions -dppr-cols200 -dsuppress-type-signatures -dsuppress-ticks -ddump-to-file #-}

module VectorSorting (main) where

import Debug.Trace qualified
import System.IO.Unsafe
import Unsafe.Coerce
import GHC.IO

import Foreign

import Prelude hiding (pi, last)

import Control.DeepSeq
import Control.Exception (evaluate)
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Bits
import Data.Char
import Data.List qualified as L
import Data.Ord
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Vector.Algorithms.Heap qualified as Heap
import Data.Vector.Algorithms.Insertion qualified as Insertion
import Data.Vector.Algorithms.Tim qualified as Tim
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as GM
import Data.Vector.Storable qualified as S
import Data.Vector.Storable.Mutable qualified as SM
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import System.Environment
import System.Random.Stateful

import Data.FuzzyMatch

import Test.Tasty
import Test.Tasty.Bench
import Test.Tasty.QuickCheck qualified as QC

-- {-# NOINLINE doMatch #-}
-- doMatch :: Int -> U.Vector Int -> Text -> [Text] -> [(Int, Text)]
-- doMatch _ seps needle
--   = L.sortOn (\(score, str) -> (Down score, T.length str))
--   . map (\str -> (fm seps needle str, str))
--
-- {-# NOINLINE fm #-}
-- fm :: U.Vector Int -> Text -> Text -> Int
-- fm seps needle str = mScore (fuzzyMatch (computeHeatMap str seps) needle str)


{-# INLINE partitionBlog #-}
partitionBlog :: (PrimMonad m, Ord a, GM.MVector v a) => Int -> v (PrimState m) a -> m Int
partitionBlog !pi !v = do
  pv <- GM.unsafeRead v pi
  GM.unsafeSwap v pi lastIdx
  pi' <- go pv 0 0
  GM.unsafeSwap v pi' lastIdx
  pure pi'
  where
    !lastIdx = GM.length v - 1

    go !pv i !si | i < lastIdx =
       do iv <- GM.unsafeRead v i
          if iv < pv
            then GM.unsafeSwap v i si >> go pv (i + 1) (si + 1)
            else go pv (i + 1) si
    go _   _  si                = pure si

{-# INLINE qsortBlog #-}
qsortBlog :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortBlog = go
  where
    go v | GM.length v < 2 = pure ()
    go v                   = do
      let !pi = GM.length v `div` 2
      pi' <- partitionBlog pi v
      go (GM.unsafeSlice 0 pi' v)
      go (GM.unsafeSlice (pi' + 1) (GM.length v - (pi' + 1)) v)

{-# INLINE partitionBlog' #-}
partitionBlog' :: (PrimMonad m, Ord a, GM.MVector v a) => Int -> v (PrimState m) a -> m Int
partitionBlog' !pi !v = do
  pv <- GM.unsafeRead v pi
  GM.unsafeSwap v pi lastIdx
  pi' <- go pv 0 0
  GM.unsafeSwap v pi' lastIdx
  pure pi'
  where
    !lastIdx = GM.length v - 1

    go !pv i !si
      | i == lastIdx
      = pure si
      | otherwise
      = do
        iv <- GM.unsafeRead v i
        if iv < pv
        then do
          GM.unsafeSwap v i si
          go pv (i + 1) (si + 1)
        else
          go pv (i + 1) si

{-# INLINE qsortBlog' #-}
qsortBlog' :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortBlog' = go
  where
    go v
      -- | len <  2
      -- = pure ()
      | len <= 16
      = Insertion.sort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0 = 0
            !pi1 = len `div` 2
            !pi2 = len - 1
        pv0 <- GM.unsafeRead v pi0
        pv1 <- GM.unsafeRead v pi1
        pv2 <- GM.unsafeRead v pi2
        let !pi =
              if pv0 > pv1
              then
                if pv0 > pv2
                then if pv1 > pv2 then pi1 else pi2
                else pi0
              else
                if pv1 > pv2
                then if pv0 > pv2 then pi0 else pi2
                else pi1
        pi' <- partitionBlog' pi v
        go (GM.unsafeSlice 0 pi' v)
        let !pi'' = pi' + 1
        go (GM.unsafeSlice pi'' (len - pi'') v)
      where
        len = GM.length v




{-# INLINE partitionOneWay #-}
partitionOneWay :: (PrimMonad m, Ord a, GM.MVector v a) => a -> Int -> v (PrimState m) a -> m Int
partitionOneWay !pv !lastIdx !v = go 0 0
  where
    go !i !j
      | i == lastIdx
      = do
        GM.unsafeSwap v j lastIdx
        pure j
      | otherwise
      = do
        x <- GM.unsafeRead v i
        if x < pv
        then do
          y <- GM.unsafeRead v j
          GM.unsafeWrite v j x
          GM.unsafeWrite v i y
          go (i + 1) (j + 1)
        else
          go (i + 1) j

{-# INLINE qsortOneWay #-}
qsortOneWay :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortOneWay = go
  where
    go v
      -- | len <  2
      -- = pure ()
      | len <= 16
      = do
        Insertion.sort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0 = 0
            !pi1 = len `div` 2
            !pi2 = len - 1
        pv0      <- GM.unsafeRead v pi0
        pv1      <- GM.unsafeRead v pi1
        pv2      <- GM.unsafeRead v pi2
        (pv, pi) <-
          if pv0 > pv1
          then
            -- ... p1 < p0 ...
            if pv0 > pv2
            then
              if pv1 > pv2
              then do
                -- p2 < p1 < p0
                GM.unsafeWrite v pi0 pv2
                GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv1
                pure (pv1, pi1)
              else do
                -- p1 <= p2 < p0
                GM.unsafeWrite v pi0 pv1
                GM.unsafeWrite v pi1 pv0
                -- GM.unsafeWrite v pi2 pv2
                pure (pv2, pi2)
            else do
              --  p1 < p0 <= p2
              GM.unsafeWrite v pi0 pv1
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv0
              pure (pv0, pi0)
          else
            -- ... p0 <= p1 ...
            if pv1 > pv2
            then
              if pv0 > pv2
              then do
                -- p2 < p0 <= p1
                GM.unsafeWrite v pi0 pv2
                -- GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv0
                pure (pv0, pi0)
              else do
                -- p0 <= p2 <= p1
                -- GM.unsafeWrite v pi1 pv2
                -- GM.unsafeWrite v pi2 pv1
                pure (pv2, pi2)
            else do
              -- p0 <= p1 <= p2
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv1
              pure (pv1, pi1)
        pi' <- partitionOneWay pv (len - 1) v
        let !pi''  = pi' + 1
            !left  = GM.unsafeSlice 0 pi' v
            !right = GM.unsafeSlice pi'' (len - pi'') v
        go left
        go right
      where
        len = GM.length v

{-# INLINE partitionTwoWays #-}
partitionTwoWays :: (PrimMonad m, Ord a, GM.MVector v a) => a -> Int -> v (PrimState m) a -> m Int
partitionTwoWays !pv !lastIdx !v =
  -- Debug.Trace.trace ("partitioning size = " ++ show lastIdx) $
  go 0 (lastIdx - 1)
  where
    go !i !j = do
      (i', xi) <- goLT i
      (j', xj) <- goGT j
      if i' < j'
      then do
        GM.unsafeWrite v j' xi
        GM.unsafeWrite v i' xj
        go (i' + 1) (j' - 1)
      else do
        GM.unsafeSwap v i' lastIdx
        pure i'
      where
        goLT !k = do
          x <- GM.unsafeRead v k
          if x < pv && k <= j
          then goLT (k + 1)
          else pure (k, x)
        goGT !k = do
          x <- GM.unsafeRead v k
          if x >= pv && k > i
          then goGT (k - 1)
          else pure (k, x)

{-# INLINE partitionTwoWaysOpt #-}
partitionTwoWaysOpt :: (PrimMonad m, Ord a, GM.MVector v a) => a -> Int -> v (PrimState m) a -> m Int
partitionTwoWaysOpt !pv !lastIdx !v =
  -- Debug.Trace.trace ("partitioning size = " ++ show lastIdx) $
  go 0 lastIdx
  where
    go !i !j = do
      (i', xi) <- goLT i
      (j', xj) <- goGT $ j - 1
      if i' < j'
      then do
        GM.unsafeWrite v j' xi
        GM.unsafeWrite v i' xj
        go (i' + 1) j'
      else
        pure i'
      where
        goLT !k = do
          x <- GM.unsafeRead v k
          if x < pv
          then goLT (k + 1)
          else pure (k, x)
        goGT !k = do
          x <- GM.unsafeRead v k
          if pv < x
          then goGT (k - 1)
          else pure (k, x)



{-# INLINABLE bitonicSort #-}
bitonicSort :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
bitonicSort v = do
  case GM.length v of
    2  -> do
      swap 0 1
    3  -> do
      swap 1 2
      swap 0 2
      swap 0 1
    4  -> do
      swap 0 1
      swap 2 3
      swap 0 2
      swap 1 3
      swap 1 2
    5  -> do
      swap 0 1
      swap 3 4
      swap 2 4
      swap 2 3
      swap 1 4
      swap 0 3
      swap 0 2
      swap 1 3
      swap 1 2
    6  -> do
      swap 1 2
      swap 4 5
      swap 0 2
      swap 3 5
      swap 0 1
      swap 3 4
      swap 2 5
      swap 0 3
      swap 1 4
      swap 2 4
      swap 1 3
      swap 2 3
    7  -> do
      swap 1 2
      swap 3 4
      swap 5 6
      swap 0 2
      swap 3 5
      swap 4 6
      swap 0 1
      swap 4 5
      swap 2 6
      swap 0 4
      swap 1 5
      swap 0 3
      swap 2 5
      swap 1 3
      swap 2 4
      swap 2 3
    8  -> do
      swap 0 1
      swap 2 3
      swap 4 5
      swap 6 7
      swap 0 2
      swap 1 3
      swap 4 6
      swap 5 7
      swap 1 2
      swap 5 6
      swap 0 4
      swap 3 7
      swap 1 5
      swap 2 6
      swap 1 4
      swap 3 6
      swap 2 4
      swap 3 5
      swap 3 4
    9  -> do
      swap 0 1
      swap 3 4
      swap 6 7
      swap 1 2
      swap 4 5
      swap 7 8
      swap 0 1
      swap 3 4
      swap 6 7
      swap 2 5
      swap 0 3
      swap 1 4
      swap 5 8
      swap 3 6
      swap 4 7
      swap 2 5
      swap 0 3
      swap 1 4
      swap 5 7
      swap 2 6
      swap 1 3
      swap 4 6
      swap 2 4
      swap 5 6
      swap 2 3
    10 -> do
      swap 4 9
      swap 3 8
      swap 2 7
      swap 1 6
      swap 0 5
      swap 1 4
      swap 6 9
      swap 0 3
      swap 5 8
      swap 0 2
      swap 3 6
      swap 7 9
      swap 0 1
      swap 2 4
      swap 5 7
      swap 8 9
      swap 1 2
      swap 4 6
      swap 7 8
      swap 3 5
      swap 2 5
      swap 6 8
      swap 1 3
      swap 4 7
      swap 2 3
      swap 6 7
      swap 3 4
      swap 5 6
      swap 4 5
    11 -> do
      swap 0 1
      swap 2 3
      swap 4 5
      swap 6 7
      swap 8 9
      swap 1 3
      swap 5 7
      swap 0 2
      swap 4 6
      swap 8 10
      swap 1 2
      swap 5 6
      swap 9 10
      swap 0 4
      swap 3 7
      swap 1 5
      swap 6 10
      swap 4 8
      swap 5 9
      swap 2 6
      swap 0 4
      swap 3 8
      swap 1 5
      swap 6 10
      swap 2 3
      swap 8 9
      swap 1 4
      swap 7 10
      swap 3 5
      swap 6 8
      swap 2 4
      swap 7 9
      swap 5 6
      swap 3 4
      swap 7 8
    12 -> do
      swap 0 1
      swap 2 3
      swap 4 5
      swap 6 7
      swap 8 9
      swap 10 11
      swap 1 3
      swap 5 7
      swap 9 11
      swap 0 2
      swap 4 6
      swap 8 10
      swap 1 2
      swap 5 6
      swap 9 10
      swap 0 4
      swap 7 11
      swap 1 5
      swap 6 10
      swap 3 7
      swap 4 8
      swap 5 9
      swap 2 6
      swap 0 4
      swap 7 11
      swap 3 8
      swap 1 5
      swap 6 10
      swap 2 3
      swap 8 9
      swap 1 4
      swap 7 10
      swap 3 5
      swap 6 8
      swap 2 4
      swap 7 9
      swap 5 6
      swap 3 4
      swap 7 8
    13 -> do
      swap 1 7
      swap 9 11
      swap 3 4
      swap 5 8
      swap 0 12
      swap 2 6
      swap 0 1
      swap 2 3
      swap 4 6
      swap 8 11
      swap 7 12
      swap 5 9
      swap 0 2
      swap 3 7
      swap 10 11
      swap 1 4
      swap 6 12
      swap 7 8
      swap 11 12
      swap 4 9
      swap 6 10
      swap 3 4
      swap 5 6
      swap 8 9
      swap 10 11
      swap 1 7
      swap 2 6
      swap 9 11
      swap 1 3
      swap 4 7
      swap 8 10
      swap 0 5
      swap 2 5
      swap 6 8
      swap 9 10
      swap 1 2
      swap 3 5
      swap 7 8
      swap 4 6
      swap 2 3
      swap 4 5
      swap 6 7
      swap 8 9
      swap 3 4
      swap 5 6
    14 -> do
      swap 0 1
      swap 2 3
      swap 4 5
      swap 6 7
      swap 8 9
      swap 10 11
      swap 12 13
      swap 0 2
      swap 4 6
      swap 8 10
      swap 1 3
      swap 5 7
      swap 9 11
      swap 0 4
      swap 8 12
      swap 1 5
      swap 9 13
      swap 2 6
      swap 3 7
      swap 0 8
      swap 1 9
      swap 2 10
      swap 3 11
      swap 4 12
      swap 5 13
      swap 5 10
      swap 6 9
      swap 3 12
      swap 7 11
      swap 1 2
      swap 4 8
      swap 1 4
      swap 7 13
      swap 2 8
      swap 5 6
      swap 9 10
      swap 2 4
      swap 11 13
      swap 3 8
      swap 7 12
      swap 6 8
      swap 10 12
      swap 3 5
      swap 7 9
      swap 3 4
      swap 5 6
      swap 7 8
      swap 9 10
      swap 11 12
      swap 6 7
      swap 8 9
    15 -> do
      swap 0 1
      swap 2 3
      swap 4 5
      swap 6 7
      swap 8 9
      swap 10 11
      swap 12 13
      swap 0 2
      swap 4 6
      swap 8 10
      swap 12 14
      swap 1 3
      swap 5 7
      swap 9 11
      swap 0 4
      swap 8 12
      swap 1 5
      swap 9 13
      swap 2 6
      swap 10 14
      swap 3 7
      swap 0 8
      swap 1 9
      swap 2 10
      swap 3 11
      swap 4 12
      swap 5 13
      swap 6 14
      swap 5 10
      swap 6 9
      swap 3 12
      swap 13 14
      swap 7 11
      swap 1 2
      swap 4 8
      swap 1 4
      swap 7 13
      swap 2 8
      swap 11 14
      swap 5 6
      swap 9 10
      swap 2 4
      swap 11 13
      swap 3 8
      swap 7 12
      swap 6 8
      swap 10 12
      swap 3 5
      swap 7 9
      swap 3 4
      swap 5 6
      swap 7 8
      swap 9 10
      swap 11 12
      swap 6 7
      swap 8 9
    16 -> do
      swap 0 1
      swap 2 3
      swap 4 5
      swap 6 7
      swap 8 9
      swap 10 11
      swap 12 13
      swap 14 15
      swap 0 2
      swap 4 6
      swap 8 10
      swap 12 14
      swap 1 3
      swap 5 7
      swap 9 11
      swap 13 15
      swap 0 4
      swap 8 12
      swap 1 5
      swap 9 13
      swap 2 6
      swap 10 14
      swap 3 7
      swap 11 15
      swap 0 8
      swap 1 9
      swap 2 10
      swap 3 11
      swap 4 12
      swap 5 13
      swap 6 14
      swap 7 15
      swap 5 10
      swap 6 9
      swap 3 12
      swap 13 14
      swap 7 11
      swap 1 2
      swap 4 8
      swap 1 4
      swap 7 13
      swap 2 8
      swap 11 14
      swap 5 6
      swap 9 10
      swap 2 4
      swap 11 13
      swap 3 8
      swap 7 12
      swap 6 8
      swap 10 12
      swap 3 5
      swap 7 9
      swap 3 4
      swap 5 6
      swap 7 8
      swap 9 10
      swap 11 12
      swap 6 7
      swap 8 9
    _  -> pure ()
  where
    swap i j = do
      x <- GM.unsafeRead v i
      y <- GM.unsafeRead v j
      when (x > y) $ do
        GM.unsafeWrite v i y
        GM.unsafeWrite v j x

{-# INLINE qsortTwoWays #-}
qsortTwoWays :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortTwoWays = go
  where
    go v
      -- | len <  2
      -- = pure ()
      | len <= 16
      = do
        Insertion.sort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0  = 0
            !pi1  = len `div` 2
            !last = len - 1
            !pi2  = last
        pv0      <- GM.unsafeRead v pi0
        pv1      <- GM.unsafeRead v pi1
        pv2      <- GM.unsafeRead v pi2
        (pv, pi) <-
          if pv0 > pv1
          then
            -- ... p1 < p0 ...
            if pv0 > pv2
            then
              if pv1 > pv2
              then do
                -- p2 < p1 < p0
                GM.unsafeWrite v pi0 pv2
                GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv1
                pure (pv1, pi1)
              else do
                -- p1 <= p2 < p0
                GM.unsafeWrite v pi0 pv1
                GM.unsafeWrite v pi1 pv0
                -- GM.unsafeWrite v pi2 pv2
                pure (pv2, pi2)
            else do
              --  p1 < p0 <= p2
              GM.unsafeWrite v pi0 pv1
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv0
              pure (pv0, pi0)
          else
            -- ... p0 <= p1 ...
            if pv1 > pv2
            then
              if pv0 > pv2
              then do
                -- p2 < p0 <= p1
                GM.unsafeWrite v pi0 pv2
                -- GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv0
                pure (pv0, pi0)
              else do
                -- p0 <= p2 <= p1
                -- GM.unsafeWrite v pi1 pv2
                -- GM.unsafeWrite v pi2 pv1
                pure (pv2, pi2)
            else do
              -- p0 <= p1 <= p2
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv1
              pure (pv1, pi1)
        pi' <- partitionTwoWays pv last v
        let !pi''  = pi' + 1
            !left  = GM.unsafeSlice 0 pi' v
            !right = GM.unsafeSlice pi'' (len - pi'') v
        go left
        go right
      where
        len = GM.length v

{-# INLINE qsortTwoWaysBitonic #-}
qsortTwoWaysBitonic :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortTwoWaysBitonic = go
  where
    go v
      -- | Debug.Trace.trace ("|v| = " ++ show len) $ False = undefined
      -- | len <  2
      -- = pure ()
      | len <= 16
      = do
        bitonicSort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0  = 0
            !pi1  = len `div` 2
            !last = len - 1
            !pi2  = last
        pv0      <- GM.unsafeRead v pi0
        pv1      <- GM.unsafeRead v pi1
        pv2      <- GM.unsafeRead v pi2
        (pv, pi) <-
          if pv0 > pv1
          then
            -- ... p1 < p0 ...
            if pv0 > pv2
            then
              if pv1 > pv2
              then do
                -- p2 < p1 < p0
                GM.unsafeWrite v pi0 pv2
                GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv1
                pure (pv1, pi1)
              else do
                -- p1 <= p2 < p0
                GM.unsafeWrite v pi0 pv1
                GM.unsafeWrite v pi1 pv0
                -- GM.unsafeWrite v pi2 pv2
                pure (pv2, pi2)
            else do
              --  p1 < p0 <= p2
              GM.unsafeWrite v pi0 pv1
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv0
              pure (pv0, pi0)
          else
            -- ... p0 <= p1 ...
            if pv1 > pv2
            then
              if pv0 > pv2
              then do
                -- p2 < p0 <= p1
                GM.unsafeWrite v pi0 pv2
                -- GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv0
                pure (pv0, pi0)
              else do
                -- p0 <= p2 <= p1
                -- GM.unsafeWrite v pi1 pv2
                -- GM.unsafeWrite v pi2 pv1
                pure (pv2, pi2)
            else do
              -- p0 <= p1 <= p2
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv1
              pure (pv1, pi1)
        pi' <- partitionTwoWays pv last v
        let !pi''  = pi' + 1
            !left  = GM.unsafeSlice 0 pi' v
            !right = GM.unsafeSlice pi'' (len - pi'') v
        go left
        go right
      where
        len = GM.length v


{-# INLINE qsortTwoWaysBitonicCutoffHeap #-}
qsortTwoWaysBitonicCutoffHeap :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortTwoWaysBitonicCutoffHeap vector = do
  -- Debug.Trace.traceM $ "threshold = " ++ show threshold
  go vector threshold
  where
    threshold = 64 - countLeadingZeros (GM.length vector)
    go v cutoff
      -- | Debug.Trace.trace ("cutoff = " ++ show cutoff ++ ", |v| = " ++ show len) $ False = undefined
      | len <= 16
      = do
        bitonicSort v
      | cutoff == 0
      = do
        -- Debug.Trace.traceM $ "len = " ++ show len ++ ", v = " ++ show v
        Heap.sort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0  = 0
            !pi1  = len `div` 2
            !last = len - 1
            !pi2  = last
        pv0      <- GM.unsafeRead v pi0
        pv1      <- GM.unsafeRead v pi1
        pv2      <- GM.unsafeRead v pi2
        (pv, pi) <-
          if pv0 > pv1
          then
            -- ... p1 < p0 ...
            if pv0 > pv2
            then
              if pv1 > pv2
              then do
                -- p2 < p1 < p0
                GM.unsafeWrite v pi0 pv2
                GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv1
                pure (pv1, pi1)
              else do
                -- p1 <= p2 < p0
                GM.unsafeWrite v pi0 pv1
                GM.unsafeWrite v pi1 pv0
                -- GM.unsafeWrite v pi2 pv2
                pure (pv2, pi2)
            else do
              --  p1 < p0 <= p2
              GM.unsafeWrite v pi0 pv1
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv0
              pure (pv0, pi0)
          else
            -- ... p0 <= p1 ...
            if pv1 > pv2
            then
              if pv0 > pv2
              then do
                -- p2 < p0 <= p1
                GM.unsafeWrite v pi0 pv2
                -- GM.unsafeWrite v pi1 pv0
                GM.unsafeWrite v pi2 pv0
                pure (pv0, pi0)
              else do
                -- p0 <= p2 <= p1
                -- GM.unsafeWrite v pi1 pv2
                -- GM.unsafeWrite v pi2 pv1
                pure (pv2, pi2)
            else do
              -- p0 <= p1 <= p2
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv1
              pure (pv1, pi1)
        pi' <- partitionTwoWays pv last v
        let !pi''    = pi' + 1
            !left    = GM.unsafeSlice 0 pi' v
            !right   = GM.unsafeSlice pi'' (len - pi'') v
            !cutoff' = cutoff - 1
        go left cutoff'
        go right cutoff'
      where
        len = GM.length v

{-# INLINE qsortTwoWaysBitonicCutoffHeap2 #-}
qsortTwoWaysBitonicCutoffHeap2 :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortTwoWaysBitonicCutoffHeap2 vector = do
  -- Debug.Trace.traceM $ "threshold = " ++ show threshold
  go vector threshold
  where
    threshold = binlog2 (GM.length vector)
    go v cutoff
      -- | Debug.Trace.trace ("cutoff = " ++ show cutoff ++ ", |v| = " ++ show len) $ False = undefined
      | len <= 16
      = do
        bitonicSort v
      | cutoff == 0
      = do
        -- Debug.Trace.traceM $ "len = " ++ show len ++ ", v = " ++ show v
        heapSort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0  = 0
            !pi1  = len `div` 2
            !last = len - 1
            !pi2  = last
        pv0      <- GM.unsafeRead v pi0
        pv1      <- GM.unsafeRead v pi1
        pv2      <- GM.unsafeRead v pi2
        pv       <-
          if pv0 > pv1
          then
            -- ... p1 < p0 ...
            if pv0 > pv2
            then
              if pv1 > pv2
              then do
                -- -- p2 < p1 < p0
                -- GM.unsafeWrite v pi0 pv2
                -- GM.unsafeWrite v pi1 pv0
                -- GM.unsafeWrite v pi2 pv1
                GM.unsafeWrite v pi1 pv2
                GM.unsafeWrite v pi2 pv1
                pure pv1
              else do
                -- -- p1 <= p2 < p0
                -- GM.unsafeWrite v pi0 pv1
                -- GM.unsafeWrite v pi1 pv0
                -- -- GM.unsafeWrite v pi2 pv2
                pure pv2
            else do
              -- --  p1 < p0 <= p2
              -- GM.unsafeWrite v pi0 pv1
              -- GM.unsafeWrite v pi1 pv2
              -- GM.unsafeWrite v pi2 pv0
              GM.unsafeWrite v pi0 pv2
              GM.unsafeWrite v pi2 pv0
              pure pv0
          else
            -- ... p0 <= p1 ...
            if pv1 > pv2
            then
              if pv0 > pv2
              then do
                -- -- p2 < p0 <= p1
                -- GM.unsafeWrite v pi0 pv2
                -- -- GM.unsafeWrite v pi1 pv0
                -- GM.unsafeWrite v pi2 pv0
                GM.unsafeWrite v pi0 pv2
                GM.unsafeWrite v pi2 pv0
                pure pv0
              else do
                -- -- p0 <= p2 <= p1
                -- -- GM.unsafeWrite v pi1 pv2
                -- -- GM.unsafeWrite v pi2 pv1
                pure pv2
            else do
              -- -- p0 <= p1 <= p2
              -- GM.unsafeWrite v pi1 pv2
              -- GM.unsafeWrite v pi2 pv1
              GM.unsafeWrite v pi1 pv2
              GM.unsafeWrite v pi2 pv1
              pure pv1
        pi' <- partitionTwoWays pv last v
        let !pi''    = pi' + 1
            !left    = GM.unsafeSlice 0 pi' v
            !right   = GM.unsafeSlice pi'' (len - pi'') v
            !cutoff' = cutoff - 1
        go left cutoff'
        go right cutoff'
      where
        len = GM.length v


{-# INLINE qsortTwoWaysBitonicCutoffHeap2OptPart #-}
qsortTwoWaysBitonicCutoffHeap2OptPart :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortTwoWaysBitonicCutoffHeap2OptPart vector = do
  -- Debug.Trace.traceM $ "threshold = " ++ show threshold
  go vector threshold
  where
    threshold = binlog2 (GM.length vector)
    go v cutoff
      -- | Debug.Trace.trace ("cutoff = " ++ show cutoff ++ ", |v| = " ++ show len) $ False = undefined
      | len <= 16
      = do
        bitonicSort v
      | cutoff == 0
      = do
        -- Debug.Trace.traceM $ "len = " ++ show len ++ ", v = " ++ show v
        heapSort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0  = 0
            !pi1  = len `div` 2
            !pi2  = len - 1
        pv0 <- GM.unsafeRead v pi0
        pv1 <- GM.unsafeRead v pi1
        pv2 <- GM.unsafeRead v pi2
        let !pv =
              if pv0 > pv1
              then
                -- ... p1 < p0 ...
                if pv0 > pv2
                then
                  if pv1 > pv2
                  then
                    -- p2 < p1 < p0
                    pv1
                  else
                    -- p1 <= p2 < p0
                    pv2
                else
                  -- p1 < p0 <= p2
                  pv0
              else
                -- ... p0 <= p1 ...
                if pv1 > pv2
                then
                  if pv0 > pv2
                  then
                    -- p2 < p0 <= p1
                    pv0
                  else do
                    -- p0 <= p2 <= p1
                    pv2
                else
                -- p0 <= p1 <= p2
                pv1
        pi' <- partitionTwoWaysOpt pv len v
        let !left    = GM.unsafeSlice 0 pi' v
            !right   = GM.unsafeSlice pi' (len - pi') v
            !cutoff' = cutoff - 1
        go left cutoff'
        go right cutoff'
      where
        len = GM.length v


-- __lg(_Size __n)
-- {
--   _Size __k;
--   for (__k = 0; __n != 0; __n >>= 1)
--     ++__k;
--   return __k - 1;
-- }

binlog :: Int -> Int
binlog = go (-1)
  where
    go !k 0 = k
    go  k n = go (k + 1) (n `unsafeShiftR` 1)

{-# INLINE binlog2 #-}
binlog2 :: Int -> Int
binlog2 x = 63 - countLeadingZeros x

{-# INLINE shiftDown #-}
shiftDown :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> Int -> m ()
shiftDown v = go
  where
    !end = GM.length v
    go p
      | c1 < end
      = do
        let !c2 = c1 + 1
        c1Val <- GM.unsafeRead v c1
        (maxIdx, maxVal) <-
          if c2 < end
          then do
            c2Val <- GM.unsafeRead v c2
            pure $ if c1Val > c2Val then (c1, c1Val) else (c2, c2Val)
          else pure (c1, c1Val)
        pVal <- GM.unsafeRead v p
        if maxVal > pVal
        then do
          GM.unsafeWrite v p maxVal
          GM.unsafeWrite v maxIdx pVal
          go maxIdx
        else
          pure ()
      | otherwise
      = pure ()
      where
        !c1 = p * 2 + 1

{-# INLINE heapify #-}
heapify :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
heapify v = do
  go (GM.length v `div` 2)
  where
    go 0 = shiftDown v 0
    go n = shiftDown v n *> go (n - 1)

{-# INLINE heapSort #-}
heapSort :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
heapSort v = do
  heapify v
  go (GM.length v)
  where
    go 0 = pure ()
    go n = do
      let !k = n - 1
      GM.unsafeSwap v 0 k
      shiftDown (GM.unsafeSlice 0 k v) 0
      go k

instance (U.Unbox a, Show a) => Show (U.MVector s a) where
  show :: forall s' a'. (Show a', U.Unbox a') => U.MVector s' a' -> String
  show xs = show (unsafePerformIO $ U.unsafeFreeze (unsafeCoerce xs :: U.MVector RealWorld a') :: U.Vector a')

-- vectorToList :: forall v s a. GM.MVector v a => v s a -> [a]
-- vectorToList xs = G.toList $ unsafePerformIO $ G.unsafeFreeze (unsafeCoerce xs :: v RealWorld a')


{-# NOINLINE qsortBlogUnboxed #-}
qsortBlogUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortBlogUnboxed xs = do
  ys <- U.thaw xs
  qsortBlog ys
  pure ys

{-# NOINLINE qsortBlogUnboxed' #-}
qsortBlogUnboxed' :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortBlogUnboxed' xs = do
  ys <- U.thaw xs
  qsortBlog' ys
  pure ys

{-# NOINLINE qsortOneWayUnboxed #-}
qsortOneWayUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortOneWayUnboxed xs = do
  ys <- U.thaw xs
  qsortOneWay ys
  pure ys

{-# NOINLINE qsortTwoWaysUnboxed #-}
qsortTwoWaysUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortTwoWaysUnboxed xs = do
  ys <- U.thaw xs
  qsortTwoWays ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicUnboxed #-}
qsortTwoWaysBitonicUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortTwoWaysBitonicUnboxed xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonic ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeapUnboxed #-}
qsortTwoWaysBitonicCutoffHeapUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortTwoWaysBitonicCutoffHeapUnboxed xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeap2Unboxed #-}
qsortTwoWaysBitonicCutoffHeap2Unboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortTwoWaysBitonicCutoffHeap2Unboxed xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap2 ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeap2OptPartUnboxed #-}
qsortTwoWaysBitonicCutoffHeap2OptPartUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
qsortTwoWaysBitonicCutoffHeap2OptPartUnboxed xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap2OptPart ys
  pure ys

{-# NOINLINE heapSortUnboxed #-}
heapSortUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
heapSortUnboxed xs = do
  ys <- U.thaw xs
  heapSort ys
  pure ys

{-# NOINLINE timUnboxed #-}
timUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
timUnboxed xs = do
  ys <- U.thaw xs
  Tim.sort ys
  pure ys

{-# NOINLINE heapUnboxed #-}
heapUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
heapUnboxed xs = do
  ys <- U.thaw xs
  Heap.sort ys
  pure ys

{-# NOINLINE insertionUnboxed #-}
insertionUnboxed :: U.Vector Int -> IO (UM.MVector RealWorld Int)
insertionUnboxed xs = do
  ys <- U.thaw xs
  Insertion.sort ys
  pure ys

{-# NOINLINE cppUnboxed #-}
cppUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cppUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cppSort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "cplusplus_sort" cppSort
  :: Ptr Int
  -> Int
  -> IO ()


{-# NOINLINE cQuicksortUnboxed #-}
cQuicksortUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cQuicksortUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cQuicksort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "c_quicksort" cQuicksort
  :: Ptr Int
  -> Int
  -> IO ()


{-# NOINLINE cHeapsortUnboxed #-}
cHeapsortUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cHeapsortUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cHeapsort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "c_heapsort" cHeapsort
  :: Ptr Int
  -> Int
  -> IO ()



{-# NOINLINE cTimsortUnboxed #-}
cTimsortUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cTimsortUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cTimsort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "c_timsort" cTimsort
  :: Ptr Int
  -> Int
  -> IO ()



{-# NOINLINE cSqrtUnboxed #-}
cSqrtUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cSqrtUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cSqrtsort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "c_sqrtsort" cSqrtsort
  :: Ptr Int
  -> Int
  -> IO ()


{-# NOINLINE cGrailUnboxed #-}
cGrailUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cGrailUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cGrailsort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "c_grailsort" cGrailsort
  :: Ptr Int
  -> Int
  -> IO ()

{-# NOINLINE cBitonicUnboxed #-}
cBitonicUnboxed :: S.Vector Int -> IO (SM.MVector RealWorld Int)
cBitonicUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cBitonicsort ptr (SM.length ys)
  pure ys


foreign import ccall unsafe "c_bitonicsort" cBitonicsort
  :: Ptr Int
  -> Int
  -> IO ()





xsInteresting :: U.Vector Int
xsInteresting = U.concat $ replicate 16 $ U.fromList [4, 9, 7, 0, 0, 1, 2, 2, 8, 7, 4, 5, 5, 1, 9, 9]

main :: IO ()
main = do
  let generate n g = U.fromList <$> replicateM n (uniformRM (1 :: Int, 128) g)

  gen       <- newIOGenM $ mkStdGen 1
  -- xsSmall15 <- generate 15 gen
  xsSmall16 <- generate 16 gen
  -- xsSmall17 <- generate 17 gen
  xsMid     <- generate 256 gen
  xsLarge   <- generate 20000 gen

  Test.Tasty.Bench.defaultMain
    (
     -- [ bgroup "bin log"
     --   [ bench "binlog"  $ nf (map binlog) [0..256]
     --   , bench "binlog2" $ nf (map binlog2) [0..256]
     --   ]
     -- ] ++
     [ bgroup (name ++ " " ++ show (U.length xs) ++ " elements")
       [ bench "Quicksort blog"                                                $ whnfAppIO qsortBlogUnboxed xs
       , bench "Quicksort blog'"                                               $ whnfAppIO qsortBlogUnboxed' xs
       , bench "Quicksort one way"                                             $ whnfAppIO qsortOneWayUnboxed xs
       , bench "Quicksort two ways"                                            $ whnfAppIO qsortTwoWaysUnboxed xs
       , bench "Quicksort two ways bitonic"                                    $ whnfAppIO qsortTwoWaysBitonicUnboxed xs
       , bench "Quicksort two ways bitonic with cutoff"                        $ whnfAppIO qsortTwoWaysBitonicCutoffHeapUnboxed xs
       , bench "Quicksort two ways bitonic with cutoff, my heapsort"           $ whnfAppIO qsortTwoWaysBitonicCutoffHeap2Unboxed xs
       , bench "Quicksort two ways bitonic with cutoff, my heapsort, opt part" $ whnfAppIO qsortTwoWaysBitonicCutoffHeap2OptPartUnboxed xs

       , bench "Heap sort"                                                     $ whnfAppIO heapSortUnboxed xs
       , bench "Vector Algorithms tim"                                         $ whnfAppIO timUnboxed xs
       , bench "Vector Algorithms heap"                                        $ whnfAppIO heapUnboxed xs
       , bench "Vector Algorithms insertion"                                   $ whnfAppIO insertionUnboxed xs
       , bench "C++"                                                           $ whnfAppIO cppUnboxed (U.convert xs)
       , bench "C quick_sort"                                                  $ whnfAppIO cQuicksortUnboxed (U.convert xs)

       , bench "Data.List.sort"                                                $ nf L.sort (U.toList xs)
       -- , bench "C heap_sort"                            $ whnfAppIO cHeapsortUnboxed (U.convert xs)
       -- , bench "C tim_sort"                             $ whnfAppIO cTimsortUnboxed (U.convert xs)
       -- , bench "C sqrt_sort"                            $ whnfAppIO cSqrtUnboxed (U.convert xs)
       -- , bench "C grail_sort"                           $ whnfAppIO cGrailUnboxed (U.convert xs)
       -- , bench "C bitonic_sort"                         $ whnfAppIO cBitonicUnboxed (U.convert xs)
       ]
     | (name, xs) <- [("small16", xsSmall16), ("medium", xsMid), ("large", xsLarge), ("interesting", xsInteresting)]
     ] ++
     [
       localOption (QC.QuickCheckTests 10000) $
       testGroup "Correctness"
       [
         QC.testProperty (name ++ " sorts") $
         \xs ->
           let sorted :: U.Vector Int
               sorted = runST $ unsafeIOToST $ do
                 ys <- U.thaw $ U.fromList xs
                 f ys
                 U.freeze ys

               expected = U.fromList (L.sort (xs :: [Int]))
           in
           QC.counterexample (show xs ++ " ->\n" ++ show sorted ++ "\n" ++ show expected) $
           expected == sorted
       | (name, (f :: UM.MVector RealWorld Int -> IO ())) <-
         [ ("qsortOneWay", qsortOneWay)
         , ("qsortTwoWays", qsortTwoWays)
         , ("qsortTwoWaysBitonic", qsortTwoWaysBitonic)
         , ("qsortTwoWaysBitonicCutoffHeap", qsortTwoWaysBitonicCutoffHeap)
         , ("qsortTwoWaysBitonicCutoffHeap2", qsortTwoWaysBitonicCutoffHeap2)
         , ("qsortTwoWaysBitonicCutoffHeap2OptPart", qsortTwoWaysBitonicCutoffHeap2OptPart)
         , ("heapSort", heapSort)
         ]
       ]
     ])

  -- [n] <- getArgs
  --
  -- let needle :: Text
  --     needle = "vector.hs"
  --     seps = U.singleton $ ord '/'
  --
  -- candidates <- T.lines <$> T.readFile "/home/sergey/projects/emacs/projects/emacs-native/candidates.txt"
  -- evaluate $ rnf candidates
  --
  -- let !k = sum $ map (\i -> sum $ map fst $ doMatch i seps needle candidates) [0..read n]
  -- putStrLn $ "k = " ++ show k

  -- let origFuzzyMatch =
  --       L.sortOn (\(score, str) -> (Down score, T.length str)) . map (\str -> (mScore $ fuzzyMatch (computeHeatMap str seps) needle str, str))
  --
  -- defaultMain
  --   [ bench "Original Haskell fuzzy match" $ nf origFuzzyMatch candidates
  --   ]


