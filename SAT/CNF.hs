-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import           Control.Monad.State.Lazy
import           Formula

-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]

-- Tseitin's conversion
toCNF :: F -> CNF
toCNF f = let (cnf, x) = evalState (go f) (maxVar f + 1) in ([x] : cnf)
  where
    go :: F -> State Var (CNF, Var)
    go (Var x) = do pure ([], x)
    go (Neg expr) = do
      (cnf, x) <- go expr
      pure (cnf, -x)
    go (a :/\: b) = do
      (ca, x) <- go a
      (cb, y) <- go b
      z <- newVar
      -- x y z | z == x && y
      -- 0 0 0 | 1
      -- 0 0 1 | 0
      -- 0 1 0 | 1
      -- 0 1 1 | 0
      -- 1 0 0 | 1
      -- 1 0 1 | 0
      -- 1 1 0 | 0
      -- 1 1 1 | 1
      -- [[x, y, -z], [x, -y, -z], [-x, y, -z], [-x, -y, z]]
      let cc = [[x, -z], [y, -z], [-x, -y, z]]
      pure (cc ++ ca ++ cb, z)
    go (a :\/: b) = do
      (ca, x) <- go a
      (cb, y) <- go b
      z <- newVar
      -- x y z | z == x || y
      -- 0 0 0 | 1
      -- 0 0 1 | 0
      -- 0 1 0 | 0
      -- 0 1 1 | 1
      -- 1 0 0 | 0
      -- 1 0 1 | 1
      -- 1 1 0 | 0
      -- 1 1 1 | 1
      -- [[x, y, -z], [x, -y, z], [-x, y, z], [-x, -y, z]]
      let cc = [[x, y, -z], [-x, z], [-y, z]]
      pure (cc ++ ca ++ cb, z)
    go (a :<=>: b) = do
      (ca, x) <- go a
      (cb, y) <- go b
      z <- newVar
      -- x y z | z == (x == y)
      -- 0 0 0 | 0
      -- 0 0 1 | 1
      -- 0 1 0 | 1
      -- 0 1 1 | 0
      -- 1 0 0 | 1
      -- 1 0 1 | 0
      -- 1 1 0 | 0
      -- 1 1 1 | 1
      -- [[x, y, z], [x, -y, -z], [-x, y, -z], [-x, -y, z]]
      let cc = [[x, y, z], [x, -y, -z], [-x, y, -z], [-x, -y, z]]
      pure (cc ++ ca ++ cb, z)
    go (a :=>: b) = do
      (ca, x) <- go a
      (cb, y) <- go b
      z <- newVar
      -- x y z | z == (x -> y)
      -- 0 0 0 | 0
      -- 0 0 1 | 1
      -- 0 1 0 | 0
      -- 0 1 1 | 1
      -- 1 0 0 | 1
      -- 1 0 1 | 0
      -- 1 1 0 | 0
      -- 1 1 1 | 1
      -- [[x, y, z], [x, -y, z], [-x, y, -z], [-x, -y, z]]
      let cc = [[x, z], [-x, y, -z], [-x, -y, z]]
      pure (cc ++ ca ++ cb, z)

    newVar :: State Var Var
    newVar = do
      x <- get
      put (x + 1)
      pure (x + 1)

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
