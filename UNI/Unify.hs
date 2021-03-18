-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Term as T
import qualified Test.QuickCheck as QC

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s t@(T.V v) = maybe t (walk s) (T.lookup s v)
walk _ t = t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs v = elem v . T.fv

-- Unification generic function. Takes an optional
-- substitution and two terms and returns an optional
-- MGU
unify :: T.Subst -> T.T -> T.T -> Maybe T.Subst
unify s t1 t2 = go (walk s t1) (walk s t2) where
  go (T.V v1) (T.V v2)
    | v1 == v2 = Just s
  go (T.V v1) w2
    | not $ occurs v1 w2 = Just $ T.add s v1 w2
  go w1 (T.V v2)
    | not $ occurs v2 w1 = Just $ T.add s v2 w1
  go (T.C cons1 args1) (T.C cons2 args2)
    | cons1 == cons2 && (length args1 == length args2)
    = foldM unifyUncur s (zip args1 args2)
    where unifyUncur s (t1, t2) = unify s t1 t2
  go _ _ = Nothing

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
qcEntry = QC.quickCheck $ QC.withMaxSuccess 10000 $ (\ x -> QC.within 1000000 $ checkUnify x)
