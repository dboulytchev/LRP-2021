-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import qualified Data.Map        as Map
import qualified Term            as T
import qualified Test.QuickCheck as QC

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s (T.V x) = case s Map.!? x of
  Just t  -> walk s t
  Nothing -> T.V x
walk _ t = t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs x (T.V y)    = x == y
occurs x (T.C _ ts) = any (occurs x) ts

-- Unification generic function. Takes an optional
-- substitution and two terms and returns an optional
-- MGU
unify :: Maybe T.Subst -> T.T -> T.T -> Maybe T.Subst
unify Nothing _ _ = Nothing
unify (Just s) t1 t2 = case (walk s t1, walk s t2) of
  (T.V x1, T.V x2) | x1 == x2 -> Just s
  (T.V x1, q2) -> Just $ Map.insert x1 q2 s
  (q1, T.V x2) -> Just $ Map.insert x2 q1 s
  (T.C c1 ts1, T.C c2 ts2)
    | c1 == c2 && length ts1 == length ts2
    -> foldl (\acc (q1, q2) -> unify acc q1 q2) (Just s) (zip ts1 ts2)
  _ -> Nothing

-- An infix version of unification
-- with empty substitution
infix 4 ===

(===) :: T.T -> T.T -> Maybe T.Subst
(===) = unify (Just T.empty)

-- A quickcheck property
checkUnify :: (T.T, T.T) -> Bool
checkUnify (t, t') =
  case t === t' of
    Nothing -> True
    Just s  -> T.apply s t == T.apply s t'

-- This check should pass:
qcEntry = QC.quickCheck $ QC.withMaxSuccess 1000 $ QC.within 1000000 . checkUnify
