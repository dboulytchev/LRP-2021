import Term as T
import Unify as U

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

-- Rename a program so that all variables in it are not 
-- interlapping with a given substitution: takes
--   1. a substitution
--   2. source program
--   3. part of the program that needs to be renamed
renameProgramHelper :: T.Subst -> P -> P -> P
renameProgramHelper = undefined

-- Recursive evalutor
evalRec :: C -> [T.Subst]
evalRec (p, [(t, s, [])])                           = [s]
evalRec (p, (t, s, []) : tl)                        = s : evalRec (p, tl)
evalRec (p, (t, s, goal@((atom, terms) : as)) : tl) = 
  case t of
    [] -> evalRec (p, tl)
    ((newAtom, predTerms), predAtoms) : programTail -> 
      if newAtom /= atom then 
        evalRec (p, (programTail, s, goal) : tl)
      else let renamedT           = renameProgramHelper s p t in
           let renamedPredAtoms   = snd (head renamedT)       in
           let renamedPredTerms   = snd (fst (head renamedT)) in
           let renamedProgramTail = tail renamedT             in
           case unifyLists (Just s) renamedPredTerms terms of
             Nothing  -> evalRec (p, (programTail, s, goal) : tl)
             Just mgu -> evalRec (p, (p, mgu, renamedPredAtoms ++ as) : ((programTail, s, goal) : tl))
                                                
