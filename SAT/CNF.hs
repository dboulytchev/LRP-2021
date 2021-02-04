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

clauseToCNF :: F -> CNF
clauseToCNF f = clauseToCNF' $ Formula.toCNF f where
    clauseToCNF' (Var v) = [[v]]
    clauseToCNF' (Neg (Var v)) = [[-v]]
    clauseToCNF' (p :/\: q) = clauseToCNF' p ++ clauseToCNF' q
    clauseToCNF' q = [innerToCNF q] where
        innerToCNF (Var v) = [v]
        innerToCNF (Neg (Var v)) = [-v]
        innerToCNF (p :\/: q) = innerToCNF p ++ innerToCNF q

expand :: (F -> F -> F) -> F -> F -> Var -> (CNF, Var, Var)
expand op p q nextv = ((clauseToCNF ((Var var2) :<=>: (op (Var cnt1) (Var cnt2)))) ++ res1 ++ res2, var2, var2 + 1) where
    (res2, cnt2, var2) = toCNF' q var1
    (res1, cnt1, var1) = toCNF' p nextv

toCNF' :: F -> Var -> (CNF, Var, Var)
toCNF' (Var v) nextv = ([], v, nextv)
toCNF' (Neg (Var v)) nextv = ([], -v, nextv)
toCNF' (p :/\: q) nextv = expand (\x y -> x :/\: y) p q nextv
toCNF' (p :\/: q) nextv = expand (\x y -> x :\/: y) p q nextv
toCNF' (p :<=>: q) nextv = expand (\x y -> x :<=>: y) p q nextv
toCNF' (p :=>: q) nextv = expand (\x y -> x :=>: y) p q nextv
toCNF' (Neg p) nextv = (res, -cntv, newv) where (res, cntv, newv) = toCNF' p nextv

-- Tseitin's conversion
toCNF :: F -> CNF
toCNF f = [[cntv]] ++ res where (res, cntv, nextv) = toCNF' f (maxVar f + 1)

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
