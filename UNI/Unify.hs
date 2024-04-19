-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import qualified Term as T
import qualified Test.QuickCheck as QC

import Term ((<+>))

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s t@(T.V _) | t' <- T.apply s t
                 , t /= t'
                 = walk s t'
walk _ t = t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs v = elem v . T.fv

-- Unification generic function. Takes a substitution
-- and two terms and returns an optional MGU
unify :: T.Subst -> T.T -> T.T -> Maybe T.Subst
unify s p q = u (walk s p) (walk s q) where

    u (T.V x) t@(T.V y) | x == y    = Just s
                        | otherwise = Just $ T.add s x t
    u (T.V v) t | occurs v t = Nothing
                | otherwise  = Just $ T.add s v t
    u p q@(T.V _) = u q p
    u (T.C x ps) (T.C y qs) | x /= y = Nothing
                            | length ps /= length qs = Nothing
                            | otherwise =
                                let us = zipWith (\p q s -> (s <+>) <$> unify s p q) ps qs in
                                foldr (>=>) return us s

-- An infix version of unification
-- with empty substitution
infix 4 ===

(===) :: T.T -> T.T -> Maybe T.Subst
(===) = unify T.empty

-- A quickcheck property
checkUnify :: (T.T, T.T) -> Bool
checkUnify (t, t') =
  case t === t' of
    Nothing -> True
    Just s  -> T.apply s t == T.apply s t'

-- This check should pass:
-- qcEntry = QC.quickCheck $ QC.withMaxSuccess 10000 $ (\x -> checkUnify x)
qcEntry = QC.quickCheck $ QC.withMaxSuccess 1000 $ (\ x -> QC.within 1000000 $ checkUnify x)

