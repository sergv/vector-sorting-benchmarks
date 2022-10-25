----------------------------------------------------------------------------
-- |
-- Module      :  FuzzyBench
-- Copyright   :  (c) Sergey Vinokurov 2022
-- License     :  Apache-2.0 (see LICENSE)
-- Maintainer  :  serg.foo@gmail.com
----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wno-orphans            #-}
{-# OPTIONS_GHC -Wno-unused-imports     #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches     #-}
{-# OPTIONS_GHC -Wno-unused-top-binds   #-}

{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-uniques -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions -dppr-cols200 -dsuppress-type-signatures -dsuppress-ticks -ddump-to-file #-}

-- {-# OPTIONS_GHC -ddump-asm -ddump-to-file #-}
-- {-# OPTIONS_GHC -ddump-llvm #-}

module VectorSorting (main) where

import Control.Monad.Reader
import Data.IORef
import Debug.Trace qualified
import GHC.IO
import System.IO.Unsafe
import Unsafe.Coerce

import Prelude hiding (pi, last)

import Control.DeepSeq
import Control.Exception (evaluate)
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Bits
import Data.Char
import Data.Int
import Data.Kind
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

import Test.Tasty
import Test.Tasty.Bench
import Test.Tasty.QuickCheck qualified as QC

import ForeignSorting

class MonadStat (m :: Type -> Type) where
  recordComparison :: m ()
  recordSwap       :: m ()

data Stat = Stat
  { sSwaps :: !Int
  , sCmps  :: !Int
  }

newtype StatM a = StatM { runStatM :: ReaderT (IORef Stat) IO a }
  deriving (Functor, Applicative, Monad, PrimMonad, MonadIO)

-- With index comparisons instead of booleans
-- WARNING: sometimes segfaults with QuickCheck
{-# INLINE selectionSort #-}
selectionSort :: forall m v a. (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
selectionSort v
  | fullStop <= 1
  = pure ()
  | fullStop == 3
  = sort3 v
  | fullStop == 4
  = sort4 v
  | otherwise
  = go 0
  where
    !fullStop = GM.length v
    !end      = GM.length v - 1
    !end2     = end - 1
    !end3     = end - 2
    go :: Int -> m ()
    go !i
      | i >= end
      = pure ()
      | i == end2
      = do
        x1 <- GM.unsafeRead v i
        x2 <- GM.unsafeRead v end
        when (x2 < x1) $ do
          GM.unsafeWrite v i x2
          GM.unsafeWrite v end x1
      | i == end3
      = do
        sort3 (GM.unsafeSlice end3 3 v)
      | otherwise
      = do
        let !ii = i + 1
        x1                          <- GM.unsafeRead v i
        x2                          <- GM.unsafeRead v ii
        (j1, min1, j2, min2, found) <- findMin i x1 ii x2
        when found $ do
          GM.unsafeWrite v i min1
          GM.unsafeWrite v ii min2
          if | j1 == ii -> do
               GM.unsafeWrite v j2 x1
             | j2 == i  -> do
               GM.unsafeWrite v j1 x2
             | otherwise -> do
               GM.unsafeWrite v j1 x1
               GM.unsafeWrite v j2 x2

        go (i + 2)

    findMin :: Int -> a -> Int -> a -> m (Int, a, Int, a, Bool)
    findMin i1 x1 i2 x2
      | x1 < x2
      = goFind x1 i1 x2 i2 False $ i2 + 1
      | otherwise
      = do
        res@(j1, y1, j2, y2, found) <- goFind x2 i2 x1 i1 False $ i2 + 1
        unless found $ do
          GM.unsafeWrite v i1 x2
          GM.unsafeWrite v i2 x1
        pure res
      where
        goFind :: a -> Int -> a -> Int -> Bool -> Int -> m (Int, a, Int, a, Bool)
        goFind min1 !imin1 min2 !imin2 found !j
          | j == fullStop
          = pure (imin1, min1, imin2, min2, found)
          | otherwise
          = do
            y <- GM.unsafeRead v j
            if y < min2
            then do
              if y < min1
              then
                goFind y j min1 imin1 True $ j + 1
              else
                goFind min1 imin1 y j True $ j + 1
            else
              goFind min1 imin1 min2 imin2 found $ j + 1


-- With native booleans
-- {-# INLINE selectionSort #-}
-- selectionSort :: forall m v a. (PrimMonad m, Ord a, GM.MVector v a, Show a) => v (PrimState m) a -> m ()
-- selectionSort v
--   | fullStop <= 1
--   = pure ()
--   | fullStop == 3
--   = sort3 v
--   | fullStop == 4
--   = sort4 v
--   | otherwise
--   = go 0
--   where
--     !fullStop = GM.length v
--     !end      = GM.length v - 1
--     !end2     = end - 1
--     !end3     = end - 2
--     go :: Int -> m ()
--     go !i
--       | i >= end
--       = pure ()
--       | i == end2
--       = do
--         x1 <- GM.unsafeRead v i
--         x2 <- GM.unsafeRead v end
--         when (x2 < x1) $ do
--           GM.unsafeWrite v i x2
--           GM.unsafeWrite v end x1
--       | i == end3
--       = do
--         sort3 (GM.unsafeSlice end3 3 v)
--       | otherwise
--       = do
--         let !ii = i + 1
--         x1                                    <- GM.unsafeRead v i
--         x2                                    <- GM.unsafeRead v ii
--         (j1, ib1, min1, j2, ib2, min2, found) <- findMin i x1 ii x2
--         when found $ do
--           GM.unsafeWrite v i min1
--           GM.unsafeWrite v ii min2
--           -- if | j1 == ii -> do
--           if | ib1 -> do
--                GM.unsafeWrite v j2 x1
--              -- | j2 == i  -> do
--              | ib2 -> do
--                GM.unsafeWrite v j1 x2
--              | otherwise -> do
--                GM.unsafeWrite v j1 x1
--                GM.unsafeWrite v j2 x2
--
--         go (i + 2)
--
--     findMin :: Int -> a -> Int -> a -> m (Int, Bool, a, Int, Bool, a, Bool)
--     findMin i1 x1 i2 x2
--       | x1 < x2
--       = goFind x1 i1 False x2 i2 False False $ i2 + 1
--       | otherwise
--       = do
--         res@(j1, _, y1, j2, _, y2, found) <- goFind x2 i2 True x1 i1 True False $ i2 + 1
--         unless found $ do
--           GM.unsafeWrite v i1 x2
--           GM.unsafeWrite v i2 x1
--         pure res
--       where
--         goFind :: a -> Int -> Bool -> a -> Int -> Bool -> Bool -> Int -> m (Int, Bool, a, Int, Bool, a, Bool)
--         goFind min1 !imin1 ib1 min2 !imin2 ib2 found !j
--           | j == fullStop
--           = pure (imin1, ib1, min1, imin2, ib2, min2, found)
--           | otherwise
--           = do
--             y <- GM.unsafeRead v j
--             if y < min2
--             then do
--               if y < min1
--               then
--                 goFind' y j False min1 imin1 (not ib1) True $ j + 1
--               else
--                 goFind min1 imin1 ib1 y j False True $ j + 1
--             else
--               goFind min1 imin1 ib1 min2 imin2 ib2 found $ j + 1
--
--         goFind' :: a -> Int -> Bool -> a -> Int -> Bool -> Bool -> Int -> m (Int, Bool, a, Int, Bool, a, Bool)
--         goFind' min1 !imin1 ib1 min2 !imin2 ib2 found !j
--           | j == fullStop
--           = pure (imin1, ib1, min1, imin2, ib2, min2, found)
--           | otherwise
--           = do
--             y <- GM.unsafeRead v j
--             if y < min2
--             then do
--               if y < min1
--               then
--                 goFind' y j False min1 imin1 False True $ j + 1
--               else
--                 goFind' min1 imin1 ib1 y j False True $ j + 1
--             else
--               goFind' min1 imin1 ib1 min2 imin2 ib2 found $ j + 1



-- {-# INLINE selectionSort #-}
-- selectionSort :: forall m v a. (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
-- selectionSort v
--   | fullStop <= 1
--   = pure ()
--   | fullStop == 3
--   = sort3 v
--   | fullStop == 4
--   = sort4 v
--   | otherwise
--   = stToPrim (go 0)
--   where
--     !fullStop = GM.length v
--     !end      = GM.length v - 1
--     !end2     = end - 1
--     !end3     = end - 2
--     go :: Int -> ST (PrimState m) ()
--     go !i
--       | i >= end
--       = pure ()
--       | i == end2
--       = do
--         x1 <- GM.unsafeRead v i
--         x2 <- GM.unsafeRead v end
--         when (x2 < x1) $ do
--           GM.unsafeWrite v i x2
--           GM.unsafeWrite v end x1
--       | i == end3
--       = do
--         sort3 (GM.unsafeSlice end3 3 v)
--       | otherwise
--       = do
--         let !ii = i + 1
--         x1 <- GM.unsafeRead v i
--         x2 <- GM.unsafeRead v ii
--         primitive $ \s1 ->
--           case findMin i x1 ii x2 s1 of
--             (# s2, j1, ib1, min1, j2, ib2, min2, found #) ->
--               (`st` s2) (do
--                 when (isTrue# found) $ do
--                   GM.unsafeWrite v i min1
--                   GM.unsafeWrite v ii min2
--                   -- if | j1 == ii -> do
--                   if | isTrue# ib1 -> do
--                        GM.unsafeWrite v j2 x1
--                      -- | j2 == i  -> do
--                      | isTrue# ib2 -> do
--                        GM.unsafeWrite v j1 x2
--                      | otherwise -> do
--                        GM.unsafeWrite v j1 x1
--                        GM.unsafeWrite v j2 x2
--                 go (i + 2))
--
--     st :: forall s b. ST s b -> State# s -> (# State# s, b #)
--     st (ST x) = x
--
--     -- State# s -> (# State# s, a #)
--     findMin :: Int -> a -> Int -> a -> State# (PrimState m) -> (# State# (PrimState m) , Int, Int#, a, Int, Int#, a, Int# #)
--     findMin i1 x1 i2 x2 s1
--       | x1 < x2
--       = goFind x1 i1 0# x2 i2 0# 0# (i2 + 1) s1
--       | otherwise
--       = do
--         case goFind x2 i2 1# x1 i1 1# 0# (i2 + 1) s1  of
--           res@(# s2, j1, ib1, y1, j2, ib2, y2, found #) ->
--             if isTrue# found
--             then
--               case st (GM.unsafeWrite v i1 x2 *> GM.unsafeWrite v i2 x1) s2 of
--                 (# s3, _ #) ->
--                   (# s3, j1, ib1, y1, j2, ib2, y2, found #)
--             else
--               res
--
--     goFind :: a -> Int -> Int# -> a -> Int -> Int# -> Int# -> Int -> State# (PrimState m) -> (# State# (PrimState m) , Int, Int#, a, Int, Int#, a, Int# #)
--     goFind min1 !imin1 ib1 min2 !imin2 ib2 found !j s1
--       | j == fullStop
--       = (# s1, imin1, ib1, min1, imin2, ib2, min2, found #)
--       | otherwise
--       = case st (GM.unsafeRead v j) s1 of
--           (# s2, y #) ->
--             if y < min2
--             then do
--               if y < min1
--               then
--                 goFind' y j 0# min1 imin1 (1# -# ib1) 1# (j + 1) s2
--               else
--                 goFind min1 imin1 ib1 y j 0# 1# (j + 1) s2
--             else
--               goFind min1 imin1 ib1 min2 imin2 ib2 found (j + 1) s2
--
--     goFind' :: a -> Int -> Int# -> a -> Int -> Int# -> Int# -> Int -> State# (PrimState m) -> (# State# (PrimState m) , Int, Int#, a, Int, Int#, a, Int# #)
--     goFind' min1 !imin1 ib1 min2 !imin2 ib2 found !j s1
--       | j == fullStop
--       = (# s1, imin1, ib1, min1, imin2, ib2, min2, found #)
--       | otherwise
--       = case st (GM.unsafeRead v j) s1 of
--           (# s2, y #) ->
--             if y < min2
--             then do
--               if y < min1
--               then
--                 goFind' y j 0# min1 imin1 0# 1# (j + 1) s2
--               else
--                 goFind' min1 imin1 ib1 y j 0# 1# (j + 1) s2
--             else
--               goFind' min1 imin1 ib1 min2 imin2 ib2 found (j + 1) s2

{-# INLINE selectionSortOpt #-}
selectionSortOpt :: forall m v a. (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
selectionSortOpt v = do
  go 0
  where
    !end = GM.length v - 1
    go :: Int -> m ()
    go !i
      | i == end
      = pure ()
      | otherwise
      = findMin i =<< GM.unsafeRead v i

    findMin :: Int -> a -> m ()
    findMin i xi =
      goFindNotFound xi i $ i + 1
      where
        goFindNotFound xk !k !j
          | j == end
          = go (i + 1)
            -- pure (k, acc, found)
          | otherwise
          = do
            xj <- GM.unsafeRead v j
            if xj < xk
            then goFindFound xj j $ j + 1
            else goFindNotFound xk k $ j + 1

        goFindFound xk !k !j
          | j == end
          = do
            GM.unsafeWrite v k xi
            GM.unsafeWrite v i xk
            go (i + 1)
          | otherwise
          = do
            xj <- GM.unsafeRead v j
            if xj < xk
            then goFindFound xj j $ j + 1
            else goFindFound xk k $ j + 1

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
      | len < 17
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
      | len < 17
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

{-# INLINE partitionTwoWaysOptFromTo #-}
partitionTwoWaysOptFromTo
  :: (PrimMonad m, Ord a, GM.MVector v a)
  => a -> v (PrimState m) a -> Int -> Int -> m Int
partitionTwoWaysOptFromTo !pv !v !start !end =
  go start end
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



{-# INLINABLE sort3 #-}
-- | Sorts the elements at the three given indices. The indices are assumed
-- to be given from lowest to highest, so if 'l < m < u' then
-- 'sort3ByIndex cmp a m l u' essentially sorts the median of three into the
-- lowest position in the array.
sort3
  :: (PrimMonad m, GM.MVector v a, Ord a)
  => v (PrimState m) a -> m ()
sort3 xs = do
  a0 <- GM.unsafeRead xs 0
  x1 <- GM.unsafeRead xs 1
  x2 <- GM.unsafeRead xs 2
  if a0 > x1
  then
    if a0 > x2
    then
      if x2 < x1
      then do
        GM.unsafeWrite xs 0 x2
        GM.unsafeWrite xs 2 a0
      else do
         GM.unsafeWrite xs 0 x1
         GM.unsafeWrite xs 1 x2
         GM.unsafeWrite xs 2 a0
    else do
      GM.unsafeWrite xs 0 x1
      GM.unsafeWrite xs 1 a0
  else
    if x1 > x2
    then
      if a0 > x2
      then do
        GM.unsafeWrite xs 0 x2
        GM.unsafeWrite xs 1 a0
        GM.unsafeWrite xs 2 x1
      else do
        GM.unsafeWrite xs 1 x2
        GM.unsafeWrite xs 2 x1
    else
      pure ()

{-# INLINABLE sort4 #-}
-- | Sorts the elements at the four given indices. Like the 2 and 3 element
-- versions, this assumes that the indices are given in increasing order, so
-- it can be used to sort medians into particular positions and so on.
sort4
  :: (PrimMonad m, GM.MVector v a, Ord a)
  => v (PrimState m) a -> m ()
sort4 xs = do
  a0 <- GM.unsafeRead xs 0
  x1 <- GM.unsafeRead xs 1
  x2 <- GM.unsafeRead xs 2
  x3 <- GM.unsafeRead xs 3
  if a0 > x1
  then
    if a0 > x2
    then
      if x1 > x2
      then
        if x1 > x3
        then
          if x2 > x3
          then do
            GM.unsafeWrite xs 0 x3
            GM.unsafeWrite xs 1 x2
            GM.unsafeWrite xs 2 x1
            GM.unsafeWrite xs 3 a0
          else do
            GM.unsafeWrite xs 0 x2
            GM.unsafeWrite xs 1 x3
            GM.unsafeWrite xs 2 x1
            GM.unsafeWrite xs 3 a0
        else
          if a0 > x3
          then do
            GM.unsafeWrite xs 0 x2
            GM.unsafeWrite xs 1 x1
            GM.unsafeWrite xs 2 x3
            GM.unsafeWrite xs 3 a0
          else do
            GM.unsafeWrite xs 0 x2
            GM.unsafeWrite xs 1 x1
            GM.unsafeWrite xs 2 a0
            GM.unsafeWrite xs 3 x3
      else
        if x2 > x3
        then
          if x1 > x3
          then do
            GM.unsafeWrite xs 0 x3
            GM.unsafeWrite xs 1 x1
            GM.unsafeWrite xs 2 x2
            GM.unsafeWrite xs 3 a0
          else do
            GM.unsafeWrite xs 0 x1
            GM.unsafeWrite xs 1 x3
            GM.unsafeWrite xs 2 x2
            GM.unsafeWrite xs 3 a0
        else
          if a0 > x3
          then do
            GM.unsafeWrite xs 0 x1
            GM.unsafeWrite xs 1 x2
            GM.unsafeWrite xs 2 x3
            GM.unsafeWrite xs 3 a0
          else do
            GM.unsafeWrite xs 0 x1
            GM.unsafeWrite xs 1 x2
            GM.unsafeWrite xs 2 a0
            -- GM.unsafeWrite xs 3 x3
    else
      if a0 > x3
      then
        if x1 > x3
        then do
          GM.unsafeWrite xs 0 x3
          -- GM.unsafeWrite xs 1 x1
          GM.unsafeWrite xs 2 a0
          GM.unsafeWrite xs 3 x2
        else do
          GM.unsafeWrite xs 0 x1
          GM.unsafeWrite xs 1 x3
          GM.unsafeWrite xs 2 a0
          GM.unsafeWrite xs 3 x2
      else
        if x2 > x3
        then do
          GM.unsafeWrite xs 0 x1
          GM.unsafeWrite xs 1 a0
          GM.unsafeWrite xs 2 x3
          GM.unsafeWrite xs 3 x2
        else do
          GM.unsafeWrite xs 0 x1
          GM.unsafeWrite xs 1 a0
          -- GM.unsafeWrite xs 2 x2
          -- GM.unsafeWrite xs 3 x3
  else
    if x1 > x2
    then
      if a0 > x2
      then
        if a0 > x3
        then
          if x2 > x3
          then do
            GM.unsafeWrite xs 0 x3
            GM.unsafeWrite xs 1 x2
            GM.unsafeWrite xs 2 a0
            GM.unsafeWrite xs 3 x1
          else do
            GM.unsafeWrite xs 0 x2
            GM.unsafeWrite xs 1 x3
            GM.unsafeWrite xs 2 a0
            GM.unsafeWrite xs 3 x1
        else
          if x1 > x3
          then do
            GM.unsafeWrite xs 0 x2
            GM.unsafeWrite xs 1 a0
            GM.unsafeWrite xs 2 x3
            GM.unsafeWrite xs 3 x1
          else do
            GM.unsafeWrite xs 0 x2
            GM.unsafeWrite xs 1 a0
            GM.unsafeWrite xs 2 x1
            -- GM.unsafeWrite xs 3 x3
      else
        if x2 > x3
        then
          if a0 > x3
          then do
            GM.unsafeWrite xs 0 x3
            GM.unsafeWrite xs 1 a0
            -- GM.unsafeWrite xs 2 x2
            GM.unsafeWrite xs 3 x1
          else do
            -- GM.unsafeWrite xs 0 a0
            GM.unsafeWrite xs 1 x3
            -- GM.unsafeWrite xs 2 x2
            GM.unsafeWrite xs 3 x1
        else
          if x1 > x3
          then do
            -- GM.unsafeWrite xs 0 a0
            GM.unsafeWrite xs 1 x2
            GM.unsafeWrite xs 2 x3
            GM.unsafeWrite xs 3 x1
          else do
            -- GM.unsafeWrite xs 0 a0
            GM.unsafeWrite xs 1 x2
            GM.unsafeWrite xs 2 x1
            -- GM.unsafeWrite xs 3 x3
    else
      if x1 > x3
      then
        if a0 > x3
        then do
          GM.unsafeWrite xs 0 x3
          GM.unsafeWrite xs 1 a0
          GM.unsafeWrite xs 2 x1
          GM.unsafeWrite xs 3 x2
        else do
          -- GM.unsafeWrite xs 0 a0
          GM.unsafeWrite xs 1 x3
          GM.unsafeWrite xs 2 x1
          GM.unsafeWrite xs 3 x2
      else
        if x2 > x3
        then do
          -- GM.unsafeWrite xs 0 a0
          -- GM.unsafeWrite xs 1 x1
          GM.unsafeWrite xs 2 x3
          GM.unsafeWrite xs 3 x2
        else do
          -- GM.unsafeWrite xs 0 a0
          -- GM.unsafeWrite xs 1 x1
          -- GM.unsafeWrite xs 2 x2
          -- GM.unsafeWrite xs 3 x3
          pure ()

{-# INLINABLE bitonicSort #-}
bitonicSort :: (PrimMonad m, Ord a, GM.MVector v a) => Int -> v (PrimState m) a -> m ()
bitonicSort n v = do
  case n of
    2  ->
      swap 0 1
    3  ->
      -- swap 1 2
      -- swap 0 2
      -- swap 0 1
      sort3 v
    4  ->
      -- swap 0 1
      -- swap 2 3
      -- swap 0 2
      -- swap 1 3
      -- swap 1 2
      sort4 v
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
      | len < 17
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
      | len < 17
      = do
        bitonicSort len v
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
      | len < 17
      = do
        bitonicSort len v
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

{-# INLINE qsortTwoWaysBitonicCutoffHeapsortMyOwn #-}
qsortTwoWaysBitonicCutoffHeapsortMyOwn :: (PrimMonad m, Ord a, GM.MVector v a) => v (PrimState m) a -> m ()
qsortTwoWaysBitonicCutoffHeapsortMyOwn vector =
  go vector threshold
  where
    !threshold = binlog2 (GM.length vector)
    go v cutoff
      | len < 17
      = bitonicSort len v
      | cutoff == 0
      = heapSort v
      | otherwise = do
        let pi0, pi1, pi2 :: Int
            !pi0  = 0
            !pi1  = len `div` 2
            !last = len - 1
            !pi2  = last
        pv0 <- GM.unsafeRead v pi0
        pv1 <- GM.unsafeRead v pi1
        pv2 <- GM.unsafeRead v pi2
        pv  <-
          if pv0 > pv1
          then
            -- ... p1 < p0 ...
            if pv0 > pv2
            then
              if pv1 > pv2
              then do
                -- p2 < p1 < p0
                GM.unsafeWrite v pi1 pv2
                GM.unsafeWrite v pi2 pv1
                pure pv1
              else do
                -- p1 <= p2 < p0
                pure pv2
            else do
              --  p1 < p0 <= p2
              GM.unsafeWrite v pi0 pv2
              GM.unsafeWrite v pi2 pv0
              pure pv0
          else
            -- ... p0 <= p1 ...
            if pv1 > pv2
            then
              if pv0 > pv2
              then do
                -- p2 < p0 <= p1
                GM.unsafeWrite v pi0 pv2
                GM.unsafeWrite v pi2 pv0
                pure pv0
              else do
                -- p0 <= p2 <= p1
                pure pv2
            else do
              -- p0 <= p1 <= p2
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
qsortTwoWaysBitonicCutoffHeap2OptPart !vector = do
  -- Debug.Trace.traceM $ "threshold = " ++ show threshold
  go vector threshold
  where
    threshold = binlog2 (GM.length vector)
    go !v cutoff
      -- | Debug.Trace.trace ("cutoff = " ++ show cutoff ++ ", |v| = " ++ show len) $ False = undefined
      | len < 17
      = do
        bitonicSort len v
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
                  else
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



{-# NOINLINE qsortBlogUnboxedInt64 #-}
qsortBlogUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortBlogUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortBlog ys
  pure ys

{-# NOINLINE qsortBlogUnboxedInt64' #-}
qsortBlogUnboxedInt64' :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortBlogUnboxedInt64' xs = do
  ys <- U.thaw xs
  qsortBlog' ys
  pure ys

{-# NOINLINE qsortOneWayUnboxedInt64 #-}
qsortOneWayUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortOneWayUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortOneWay ys
  pure ys

{-# NOINLINE qsortTwoWaysUnboxedInt64 #-}
qsortTwoWaysUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortTwoWaysUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortTwoWays ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicUnboxedInt64 #-}
qsortTwoWaysBitonicUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortTwoWaysBitonicUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonic ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeapUnboxedInt64 #-}
qsortTwoWaysBitonicCutoffHeapUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortTwoWaysBitonicCutoffHeapUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedInt64 #-}
qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeapsortMyOwn ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedInt64 #-}
qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedInt64 xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap2OptPart ys
  pure ys

{-# NOINLINE heapSortUnboxedInt64 #-}
heapSortUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
heapSortUnboxedInt64 xs = do
  ys <- U.thaw xs
  heapSort ys
  pure ys

{-# NOINLINE timUnboxedInt64 #-}
timUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
timUnboxedInt64 xs = do
  ys <- U.thaw xs
  Tim.sort ys
  pure ys

{-# NOINLINE heapUnboxedInt64 #-}
heapUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
heapUnboxedInt64 xs = do
  ys <- U.thaw xs
  Heap.sort ys
  pure ys

{-# NOINLINE mySelectionSortUnboxedInt64 #-}
mySelectionSortUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
mySelectionSortUnboxedInt64 xs = do
  ys <- U.thaw xs
  selectionSort ys
  pure ys

{-# NOINLINE mySelectionSortOptUnboxedInt64 #-}
mySelectionSortOptUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
mySelectionSortOptUnboxedInt64 xs = do
  ys <- U.thaw xs
  selectionSortOpt ys
  pure ys

{-# NOINLINE insertionUnboxedInt64 #-}
insertionUnboxedInt64 :: U.Vector Int64 -> IO (UM.MVector RealWorld Int64)
insertionUnboxedInt64 xs = do
  ys <- U.thaw xs
  Insertion.sort ys
  pure ys



{-# NOINLINE cppUnboxedInt64 #-}
cppUnboxedInt64 :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cppUnboxedInt64 xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cppSortInt64 ptr (SM.length ys)
  pure ys

{-# NOINLINE cQuicksortUnboxedInt64 #-}
cQuicksortUnboxedInt64 :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cQuicksortUnboxedInt64 xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cQuicksortInt64 ptr (SM.length ys)
  pure ys


{-# NOINLINE cHeapsortUnboxed #-}
cHeapsortUnboxed :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cHeapsortUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cHeapsortInt64 ptr (SM.length ys)
  pure ys



{-# NOINLINE cTimsortUnboxed #-}
cTimsortUnboxed :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cTimsortUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cTimsortInt64 ptr (SM.length ys)
  pure ys



{-# NOINLINE cSqrtUnboxed #-}
cSqrtUnboxed :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cSqrtUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cSqrtsortInt64 ptr (SM.length ys)
  pure ys


{-# NOINLINE cGrailUnboxed #-}
cGrailUnboxed :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cGrailUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cGrailsortInt64 ptr (SM.length ys)
  pure ys

{-# NOINLINE cBitonicUnboxed #-}
cBitonicUnboxed :: S.Vector Int64 -> IO (SM.MVector RealWorld Int64)
cBitonicUnboxed xs = do
  ys <- S.thaw xs
  SM.unsafeWith ys $ \ptr -> cBitonicsortInt64 ptr (SM.length ys)
  pure ys




{-# NOINLINE qsortBlogUnboxedPair #-}
qsortBlogUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortBlogUnboxedPair xs = do
  ys <- U.thaw xs
  qsortBlog ys
  pure ys

{-# NOINLINE qsortBlogUnboxedPair' #-}
qsortBlogUnboxedPair' :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortBlogUnboxedPair' xs = do
  ys <- U.thaw xs
  qsortBlog' ys
  pure ys

{-# NOINLINE qsortOneWayUnboxedPair #-}
qsortOneWayUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortOneWayUnboxedPair xs = do
  ys <- U.thaw xs
  qsortOneWay ys
  pure ys

{-# NOINLINE qsortTwoWaysUnboxedPair #-}
qsortTwoWaysUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortTwoWaysUnboxedPair xs = do
  ys <- U.thaw xs
  qsortTwoWays ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicUnboxedPair #-}
qsortTwoWaysBitonicUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortTwoWaysBitonicUnboxedPair xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonic ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeapUnboxedPair #-}
qsortTwoWaysBitonicCutoffHeapUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortTwoWaysBitonicCutoffHeapUnboxedPair xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedPair #-}
qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedPair xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeapsortMyOwn ys
  pure ys

{-# NOINLINE qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedPair #-}
qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedPair xs = do
  ys <- U.thaw xs
  qsortTwoWaysBitonicCutoffHeap2OptPart ys
  pure ys

{-# NOINLINE heapSortUnboxedPair #-}
heapSortUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
heapSortUnboxedPair xs = do
  ys <- U.thaw xs
  heapSort ys
  pure ys

{-# NOINLINE timUnboxedPair #-}
timUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
timUnboxedPair xs = do
  ys <- U.thaw xs
  Tim.sort ys
  pure ys

{-# NOINLINE heapUnboxedPair #-}
heapUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
heapUnboxedPair xs = do
  ys <- U.thaw xs
  Heap.sort ys
  pure ys

{-# NOINLINE mySelectionSortUnboxedPair #-}
mySelectionSortUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
mySelectionSortUnboxedPair xs = do
  ys <- U.thaw xs
  selectionSort ys
  pure ys

{-# NOINLINE mySelectionSortOptUnboxedPair #-}
mySelectionSortOptUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
mySelectionSortOptUnboxedPair xs = do
  ys <- U.thaw xs
  selectionSortOpt ys
  pure ys

{-# NOINLINE insertionUnboxedPair #-}
insertionUnboxedPair :: U.Vector (Int32, Int32) -> IO (UM.MVector RealWorld (Int32, Int32))
insertionUnboxedPair xs = do
  ys <- U.thaw xs
  Insertion.sort ys
  pure ys







xsInteresting :: U.Vector Int
xsInteresting = U.concat $ replicate 16 $ U.fromList [4, 9, 7, 0, 0, 1, 2, 2, 8, 7, 4, 5, 5, 1, 9, 9]

newtype SortFunc = SortFunc { unSortFunc :: forall s. UM.MVector s Int -> ST s () }

main :: IO ()
main = do
  let generate n g = U.fromList <$> replicateM n (uniformRM (1 :: Int, 128) g)

  str <- T.readFile "/home/sergey/projects/emacs/projects/emacs-native/candidates.txt"

  let fi64 :: Integral a => a -> Int64
      fi64 = fromIntegral
      candidates :: [U.Vector Int64]
      candidates
        = map (U.fromList . zipWith (\(n :: Int) (c :: Int) -> (fi64 c `unsafeShiftL` 32) .|. fi64 n) [0..] . map ord . T.unpack)
        $ T.lines str
  let candidatesPair :: [U.Vector (Int32, Int32)]
      candidatesPair
        = map (U.fromList . zipWith (\n c -> (fromIntegral c, fromIntegral n)) [0..] . map ord . T.unpack)
        $ T.lines str

  putStrLn $ "length candidates = " ++ show (length candidates)

  gen       <- newIOGenM $ mkStdGen 1
  -- xsSmall15 <- generate 15 gen
  let n :: Int
      n = 1000
  xsSmall16 <- replicateM n $ generate 16 gen
  -- xsSmall17 <- generate 17 gen
  xsMid100  <- replicateM n $ generate 100 gen
  xsMid     <- replicateM n $ generate 256 gen
  xsLarge   <- replicateM n $ generate 20000 gen

  Test.Tasty.Bench.defaultMain
    (
     -- [ bgroup "bin log"
     --   [ bench "binlog"  $ nf (map binlog) [0..256]
     --   , bench "binlog2" $ nf (map binlog2) [0..256]
     --   ]
     -- ] ++
     [ bgroup ("Int64 " ++ name ++ " " ++ show (U.length (head xs)) ++ " elements")
       [ bench "Quicksort blog"                                                $ nfAppIO (traverse qsortBlogUnboxedInt64) xs
       , bench "Quicksort blog'"                                               $ nfAppIO (traverse qsortBlogUnboxedInt64') xs
       , bench "Quicksort one way"                                             $ nfAppIO (traverse qsortOneWayUnboxedInt64) xs
       , bench "Quicksort two ways"                                            $ nfAppIO (traverse qsortTwoWaysUnboxedInt64) xs
       , bench "Quicksort two ways bitonic"                                    $ nfAppIO (traverse qsortTwoWaysBitonicUnboxedInt64) xs
       , bench "Quicksort two ways bitonic with cutoff"                        $ nfAppIO (traverse qsortTwoWaysBitonicCutoffHeapUnboxedInt64) xs
       , bench "Quicksort two ways bitonic with cutoff, my heapsort"           $ nfAppIO (traverse qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedInt64) xs
       , bench "Quicksort two ways bitonic with cutoff, my heapsort, opt part" $ nfAppIO (traverse qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedInt64) xs

       , bench "My heap sort"                                                  $ nfAppIO (traverse heapSortUnboxedInt64) xs
       -- , bench "My selection sort"                                             $ nfAppIO (traverse mySelectionSortUnboxedInt64) xs
       -- , bench "My selection sort opt"                                         $ nfAppIO (traverse mySelectionSortOptUnboxedInt64) xs
       -- , bench "Vector Algorithms tim"                                         $ nfAppIO (traverse timUnboxedInt64) xs
       , bench "Vector Algorithms heap"                                        $ nfAppIO (traverse heapUnboxedInt64) xs
       -- , bench "Vector Algorithms insertion"                                   $ nfAppIO (traverse insertionUnboxedInt64) xs
       , bench "C++"                                                           $ nfAppIO (traverse cppUnboxedInt64) (map U.convert xs)
       , bench "C quick_sort"                                                  $ nfAppIO (traverse cQuicksortUnboxedInt64) (map U.convert xs)

       -- , bench "Data.List.sort"                                                $ nf (map L.sort) (map U.toList xs)
       -- , bench "C heap_sort"                            $ whnfAppIO cHeapsortUnboxed (U.convert xs)
       -- , bench "C tim_sort"                             $ whnfAppIO cTimsortUnboxed (U.convert xs)
       -- , bench "C sqrt_sort"                            $ whnfAppIO cSqrtUnboxed (U.convert xs)
       -- , bench "C grail_sort"                           $ whnfAppIO cGrailUnboxed (U.convert xs)
       -- , bench "C bitonic_sort"                         $ whnfAppIO cBitonicUnboxed (U.convert xs)
       ]
     | (name, xs) <-
         [ ("candidates", candidates)
         -- , ("small16", xsSmall16)
         -- , ("medium100", xsMid100)
         -- , ("medium", xsMid)
         -- , ("large", xsLarge)
         -- , ("interesting", [xsInteresting])
         ]
     ] ++
     [ bgroup ("(Int32, Int32) " ++ name ++ " " ++ show (U.length (head xs)) ++ " elements")
       [ bench "Quicksort blog"                                                $ nfAppIO (traverse qsortBlogUnboxedPair) xs
       , bench "Quicksort blog'"                                               $ nfAppIO (traverse qsortBlogUnboxedPair') xs
       , bench "Quicksort one way"                                             $ nfAppIO (traverse qsortOneWayUnboxedPair) xs
       , bench "Quicksort two ways"                                            $ nfAppIO (traverse qsortTwoWaysUnboxedPair) xs
       , bench "Quicksort two ways bitonic"                                    $ nfAppIO (traverse qsortTwoWaysBitonicUnboxedPair) xs
       , bench "Quicksort two ways bitonic with cutoff"                        $ nfAppIO (traverse qsortTwoWaysBitonicCutoffHeapUnboxedPair) xs
       , bench "Quicksort two ways bitonic with cutoff, my heapsort"           $ nfAppIO (traverse qsortTwoWaysBitonicCutoffHeapsortMyOwnUnboxedPair) xs
       , bench "Quicksort two ways bitonic with cutoff, my heapsort, opt part" $ nfAppIO (traverse qsortTwoWaysBitonicCutoffHeap2OptPartUnboxedPair) xs

       , bench "My heap sort"                                                  $ nfAppIO (traverse heapSortUnboxedPair) xs
       -- , bench "My selection sort"                                             $ nfAppIO (traverse mySelectionSortUnboxedPair) xs
       -- , bench "My selection sort opt"                                         $ nfAppIO (traverse mySelectionSortOptUnboxedPair) xs
       -- , bench "Vector Algorithms tim"                                         $ nfAppIO (traverse timUnboxedPair) xs
       , bench "Vector Algorithms heap"                                        $ nfAppIO (traverse heapUnboxedPair) xs
       -- , bench "Vector Algorithms insertion"                                   $ nfAppIO (traverse insertionUnboxedPair) xs

       -- , bench "C++"                                                           $ nfAppIO (traverse cppUnboxedPair) (map U.convert xs)
       -- , bench "C quick_sort"                                                  $ nfAppIO (traverse cQuicksortUnboxedPair) (map U.convert xs)

       -- , bench "Data.List.sort"                                                $ nf (map L.sort) (map U.toList xs)
       -- , bench "C heap_sort"                            $ whnfAppIO cHeapsortUnboxed (U.convert xs)
       -- , bench "C tim_sort"                             $ whnfAppIO cTimsortUnboxed (U.convert xs)
       -- , bench "C sqrt_sort"                            $ whnfAppIO cSqrtUnboxed (U.convert xs)
       -- , bench "C grail_sort"                           $ whnfAppIO cGrailUnboxed (U.convert xs)
       -- , bench "C bitonic_sort"                         $ whnfAppIO cBitonicUnboxed (U.convert xs)
       ]
     | (name, xs) <-
         [ ("candidates pair", candidatesPair)
         ]
     ] ++
     [
       localOption (QC.QuickCheckTests 100000) $
       testGroup "Correctness"
       [
         QC.testProperty (name ++ " sorts") $
         \xs ->
           let sorted :: U.Vector Int
               sorted = runST $ do
                 ys <- U.thaw $ U.fromList xs
                 unSortFunc f ys
                 U.freeze ys

               expected = U.fromList (L.sort (xs :: [Int]))
           in
           QC.counterexample (show xs ++ " ->\n" ++ show sorted ++ "\n" ++ show expected) $
           expected == sorted
       | (name, (f :: SortFunc)) <-
         [ ("qsortOneWay", SortFunc qsortOneWay)
         , ("qsortTwoWays", SortFunc qsortTwoWays)
         , ("qsortTwoWaysBitonic", SortFunc qsortTwoWaysBitonic)
         , ("qsortTwoWaysBitonicCutoffHeap", SortFunc qsortTwoWaysBitonicCutoffHeap)
         , ("qsortTwoWaysBitonicCutoffHeapsortMyOwn", SortFunc qsortTwoWaysBitonicCutoffHeapsortMyOwn)
         , ("qsortTwoWaysBitonicCutoffHeap2OptPart", SortFunc qsortTwoWaysBitonicCutoffHeap2OptPart)
         -- , ("selectionSort", SortFunc selectionSort)
         -- , ("selectionSortOpt", SortFunc selectionSortOpt)
         , ("heapSort", SortFunc heapSort)
         ]
       ]
     ])


