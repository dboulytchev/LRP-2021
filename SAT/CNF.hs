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

toCNF' :: Var -> Formula.F -> (Var, CNF, Var)
toCNF' next f = case f of
  Var n -> (n, [], next)
  Neg g ->
    let (vg, cs, vf) = toCNF' next g in
      (vf, cs ++ [[-vg, -vf], [vg, vf]], vf + 1)
  g :/\: h ->
    rec2 g h (\vg vh vf ->
      [[-vg, -vh, vf], [vg, -vf], [vh, -vf]])
  g :\/: h ->
    rec2 g h (\vg vh vf ->
      [[vg, vh, -vf], [-vg, vf], [-vh, vf]])
  g :<=>: h ->
    rec2 g h (\vg vh vf ->
      [[-vg, -vh, vf], [vg, vh, vf], [vg, -vh, -vf], [-vg, vh, -vf]])
  g :=>: h ->
    rec2 g h (\vg vh vf ->
      [[-vg, vh, -vf], [vg, vf], [-vh, vf]])
  where
    rec2 g h gen =
      let (vg, csF, n1) = toCNF' next g
          (vh, csG, vf) = toCNF' n1 h in
        (vf, csF ++ csG ++ gen vg vh vf, vf + 1)


-- Tseitin's conversion
toCNF :: Formula.F -> CNF
toCNF (Var n) = [[n]]
toCNF f =
  let (top, cs, _) = toCNF' (maxVar f + 1) f in
    cs ++ [[top]]


-- The inverse conversion
fromCNF :: CNF -> Formula.F
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
