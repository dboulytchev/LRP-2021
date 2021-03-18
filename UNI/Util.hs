module Util where

farthest :: (a -> Maybe a) -> a -> a
farthest f = go where
  go a = maybe a go (f a)
{-# INLINE farthest #-}

nothingIfDoesNotChange :: Eq a => (a -> a) -> a -> Maybe a
nothingIfDoesNotChange s a = let sa = s a in if sa == a then Nothing else Just sa

farthestDNC :: Eq a => (a -> a) -> a -> a
farthestDNC s = farthest (nothingIfDoesNotChange s)
