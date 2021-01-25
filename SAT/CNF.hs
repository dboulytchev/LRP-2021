-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import Formula
import Data.List
import Control.Monad.State.Lazy
import Test.QuickCheck

-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]

toList :: F -> CNF
toList (a :/\: b) = toList a ++ toList b 
toList c@(a :\/: b) = [toListC c] where
  toListC (a :\/: b) = toListC a ++ toListC b
  toListC (Var v) = [v]
  toListC (Neg (Var v)) = [-v]
toList (Var v) = [[v]]
toList (Neg (Var v)) = [[-v]]

tseytin :: F -> Int -> (CNF, Var, Int)
tseytin f maxVar = case f of
  (Var v) -> ([], v, maxVar)
  (Neg (Var v)) -> ([], -v, maxVar)
  (a :/\: b) -> helper (\ x y -> x :/\: y) a b
  (a :\/: b) -> helper (\ x y -> x :\/: y) a b
  (a :<=>: b) -> helper (\ x y -> x :<=>: y) a b
  (a :=>: b) -> helper (\ x y -> x :=>: y) a b
  (Neg a) -> let (res, x, maxVar') = tseytin a maxVar in (res, -x, maxVar')
  where helper op a b = let (res1, x, maxVar') = tseytin a maxVar in 
                        let (res2, y, maxVar'') = tseytin b maxVar' in 
                        let v = maxVar'' + 1 in
                        ((toList $ Formula.toCNF $ (Var v) :<=>: (op (Var x) (Var y))) ++ res1 ++ res2, v, v)

-- Tseitin's conversion
toCNF :: F -> CNF
toCNF f = let (x, v, _) = tseytin f (maxVar f) in ([v]):x

-- The inverse conversion
fromCNF (h : tl) = foldl (\ acc c -> acc :/\: fromClause c) (fromClause h) tl where
  fromClause (h : tl)  = foldl (\ acc v -> acc :\/: fromVar v) (fromVar h) tl
  fromVar n | n < 0     = Neg $ Var (-n)
            | otherwise = Var n

-- The equisatisfability of Tseitin's conversion
equisaT :: F -> Bool
equisaT f = Formula.equisat f (fromCNF $ CNF.toCNF f)

-- Tseitin's conversion gives a CNF
isCNF :: F -> Bool
isCNF = Formula.isCNF . fromCNF . CNF.toCNF 
