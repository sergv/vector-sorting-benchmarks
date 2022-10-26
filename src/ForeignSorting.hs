----------------------------------------------------------------------------
-- |
-- Module      :  ForeignSorting
-- Copyright   :  (c) Sergey Vinokurov 2022
-- License     :  Apache-2.0 (see LICENSE)
-- Maintainer  :  serg.foo@gmail.com
----------------------------------------------------------------------------

module ForeignSorting
  ( cppSortInt64
  , cQuicksortInt64
  , cHeapsortInt64
  , cTimsortInt64
  , cSqrtsortInt64
  , cGrailsortInt64
  , cBitonicsortInt64
  ) where

import Data.Int
import Foreign

foreign import ccall unsafe "cplusplus_sort" cppSortInt64
  :: Ptr Int64
  -> Int
  -> IO ()

foreign import ccall unsafe "c_quicksort" cQuicksortInt64
  :: Ptr Int64
  -> Int
  -> IO ()

foreign import ccall unsafe "c_heapsort" cHeapsortInt64
  :: Ptr Int64
  -> Int
  -> IO ()

foreign import ccall unsafe "c_timsort" cTimsortInt64
  :: Ptr Int64
  -> Int
  -> IO ()

foreign import ccall unsafe "c_sqrtsort" cSqrtsortInt64
  :: Ptr Int64
  -> Int
  -> IO ()

foreign import ccall unsafe "c_grailsort" cGrailsortInt64
  :: Ptr Int64
  -> Int
  -> IO ()

foreign import ccall unsafe "c_bitonicsort" cBitonicsortInt64
  :: Ptr Int64
  -> Int
  -> IO ()
