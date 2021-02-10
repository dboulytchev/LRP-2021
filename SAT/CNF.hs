-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import Formula
import Data.List
import Control.Monad.State.Lazy


-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]



--   A trivial formula is one of the form:
--   `s * t' where s and t are positive literals,
--    * is a binary operation
--   or `Neg x' where x is a positive literal.


--   `trivialCNF` converts formulas of the `p_i <==> tf` form
--   (where `p_i` is a fresh propositional variable
--   and `tf` is a trivial formula)
--   to CNF representation.
--   It throws a error for all the other formulas.
trivialCNF :: (Var, F) -> CNF
trivialCNF (a, tf) = case tf of
      -- a <=> (p & q)  ~~~  (¬a ∨ p) ∧ (¬a ∨ q) ∧ (a ∨ ¬p ∨ ¬q)
      (Var p) :/\: (Var q) -> [[-a, p],
                               [-a, q],
                               [a, -p, -q]]

      -- a <=> (p | q)  ~~~  (¬a ∨ p ∨ q) ∧ (a ∨ ¬p) ∧ (a ∨ ¬q)
      (Var p) :\/: (Var q) -> [[-a, p, q],
                               [-p, a],
                               [-q, a]]

      -- a <=> (p <=> q)  ~~~  (¬a ∨ ¬p ∨ q) ∧ (¬a ∨ p ∨ ¬q) ∧ (a ∨ ¬p ∨ ¬q) ∧ (a ∨ p ∨ q)
      (Var p) :<=>: (Var q) -> [[-a, -p, q],
                                [-a, p, -q],
                                [a, -p, -q],
                                [a, p, q]]

      -- a <=> (p => q) ~~~  (a ∧ ¬p) ∨ (a ∧ q) ∨ (¬a ∧ p ∧ ¬q)
      (Var p) :=>: (Var q) -> [[a, -p],
                               [a, q],
                               [-a, p, -q]]

      -- a <=> ¬b       ~~~ (¬a ∨ ¬b) ∧ (a ∨ b)
      Neg (Var b) -> [[-a, -b], [a, b]]

      _ -> error $ "Formula " ++ show tf ++ " is not trivial"


-- State: max variable index and current set of equasions
type TsState = (Var, [(Var, F)])

-- Get a fresh variable
getFresh :: State TsState Var
getFresh = do
  (v, eqs) <- get
  put (v + 1, eqs)
  return $ v + 1

-- Remember the equation: freshVar <=> trivF
-- assuming that trivF is a trivial formula
addEq :: Var -> F -> State TsState ()
addEq freshVar trivF = do
  (v, eqs) <- get
  put (maximum [v, freshVar, maxVar trivF],
       (freshVar, trivF) : eqs)

-- Tseitin's conversion
toCNF :: F -> CNF
toCNF f = let (v, eqs) = execState (go f) (maxVar f, []) in [v] : (eqs >>= trivialCNF)
  where
    go (Var x)     = return x
    go (x :/\:  y) = goBin x y (:/\:)
    go (x :\/:  y) = goBin x y (:\/:)
    go (x :<=>: y) = goBin x y (:<=>:)
    go (x :=>:  y) = goBin x y (:=>:)
    go (Neg x)     = do
      x' <- go x
      freshVar <- getFresh
      addEq freshVar (Neg $ Var x')
      return freshVar

    goBin x y binOp = do
      x' <- go x
      y' <- go y
      freshVar <- getFresh
      addEq freshVar (Var x' `binOp` Var y')
      return freshVar

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
