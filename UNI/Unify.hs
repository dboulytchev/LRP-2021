-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import qualified Term as T
import qualified Test.QuickCheck as QC

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s t@(T.V v) = case T.lookup s v of
  Just t' -> walk s t'
  Nothing -> t
walk s t = t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs v t = v `elem` (T.fv t)

-- Unification generic function. Takes an optional
-- substitution and two terms and returns an optional
-- MGU
unify :: Maybe T.Subst -> T.T -> T.T -> Maybe T.Subst
unify s' t1 t2 = s' >>= (\ s ->
  let t1' = walk s t1 in let t2' = walk s t2 in
  case t1' of
    T.V v -> case t2' of
      T.V u | u == v -> s'
      t | not (occurs v t) -> Just (T.add s v t)
      _ -> Nothing
    t@(T.C c1 ts1) -> case t2' of 
      T.V u | not (occurs u t) -> Just (T.add s u t)
      T.C c2 ts2 | c1 == c2 -> foldl (\ acc (t1', t2') -> unify acc t1' t2') s' (zip ts1 ts2)
      _ -> Nothing
  )

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
qcEntry = QC.quickCheck $ QC.withMaxSuccess 1000 $ (\ x -> QC.within 1000000 $ checkUnify x)
    
