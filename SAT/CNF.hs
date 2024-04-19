-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import Formula
import Data.List
import Control.Monad.State
import Control.Monad.Writer

import qualified Fix

-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]

data F' f
    = Var' Var
    | Neg' f
    | f :|/\|: f
    | f :|\/|: f
    | f :|=>|: f
    | f :|<=>|: f
    deriving (Show, Read, Eq, Ord, Functor)


-- Tseitin's conversion
toCNF :: F -> CNF
toCNF = result where

    result f =
        let sw = Fix.hylo phi toF'Psi f in
        let w = evalStateT sw $ maximum $ fv f in
        let (x, cnf) = runWriter w in
        [x]:cnf

    newVar :: MonadState Int m => m Var
    newVar = state $ \x -> let x' = x + 1 in (x', x')

    phi :: (MonadState Int m, MonadWriter CNF m) => Fix.Algebra F' (m Var)
    phi (Var' v) = return v
    phi (Neg' f) = do f <- f
                      v <- newVar
                      tell [[v, f], [-v, -f]]
                      return v
    phi (f :|/\|: g) = do f <- f
                          g <- g
                          v <- newVar
                          tell [[v, -f, -g], [-v, f], [-v, g]]
                          return v
    phi (f :|\/|: g) = do f <- f
                          g <- g
                          v <- newVar
                          tell [[v, -f], [v, -g], [-v, f, g]]
                          return v
    phi (f :|=>|: g) = do f <- f
                          g <- g
                          v <- newVar
                          tell [[v, f], [v, -g], [-v, -f, g]]
                          return v
    phi (f :|<=>|: g) = do f <- f
                           g <- g
                           v <- newVar
                           tell [[v, f, g], [v, -f, -g], [-v, f, -g], [-v, -f, g]]
                           return v

fromF'Phi :: Fix.Algebra F' F
fromF'Phi (Var' v) = Var v
fromF'Phi (Neg' x) = Neg x
fromF'Phi (f :|/\|: g) = f :/\: g
fromF'Phi (f :|\/|: g) = f :\/: g
fromF'Phi (f :|=>|: g) = f :=>: g
fromF'Phi (f :|<=>|: g) = f :<=>: g

toF'Psi :: Fix.Coalgebra F' F
toF'Psi (Var v) = Var' v
toF'Psi (Neg x) = Neg' x
toF'Psi (f :/\: g) = f :|/\|: g
toF'Psi (f :\/: g) = f :|\/|: g
toF'Psi (f :=>: g) = f :|=>|: g
toF'Psi (f :<=>: g) = f :|<=>|: g

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
