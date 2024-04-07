import Term as T
import Unify

-- Predicate names
type Pred = Int

-- Atomic formula
type A = (Pred, [T.T])

-- Horn clause
type H = (A, [A])

-- Program
type P = [H]

-- Configuration
--   1. A whole source program
--   2. A stack of states each of which is
--      1. a tail of a program to match against
--      2. current substitution
--      3. current goal

type C = (P, [(P, T.Subst, [A])])

-- NB: lift over state monad to implement
--     variable renaming in the current program!

-- Top-level evaluator: takes
--   1. a program
--   2. a query
eval :: P -> [A] -> [T.Subst]
eval p q = evalRec (p, [(p, T.empty, q)])

-- Recursive evalutor
evalRec (p, (t, s, []) : tl) = s : evalRec (p, tl)
evalRec (p, (t, s, (atom, terms) : as) : tl) = undefined