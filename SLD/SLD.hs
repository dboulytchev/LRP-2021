import Term as T
import Unify as U
import Data.Map as Map

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

-- Rename a horn clause so that all variables in it are 
-- not interlapping with a given substitution: takes
--   1. a substitution
--   2. source program
--   3. horn clause that needs to be renamed
renameHornHelper :: T.Subst -> P -> H -> H
renameHornHelper s p = renameHornWith (getRenamingShift s p) where
  myInfTy :: Int
  myInfTy = 2000000000
  getRenamingShift :: T.Subst -> P -> Int 
  getRenamingShift s p = if T.empty == s then getProgramShift p else max (getProgramShift p) (fst $ Map.findMax s)
  getProgramShift :: P -> Int
  getProgramShift []              = 0
  getProgramShift ((ts, as):rest) = max (getMaxIndex (ts : as)) (getProgramShift rest)
  getMinIndex :: [A] -> Int
  getMinIndex []             = myInfTy
  getMinIndex ((_, ts):rest) = min (minimum (getMinInd <$> ts)) (getMinIndex rest)
  getMinInd :: T.T -> Int
  getMinInd (C _ []) = myInfTy
  getMinInd (C _ ts) = minimum (getMinInd <$> ts)
  getMinInd (V var)  = var
  getMaxIndex :: [A] -> Int
  getMaxIndex []             = 0
  getMaxIndex ((_, ts):rest) = max (maximum (getMaxInd <$> ts)) (getMaxIndex rest)
  getMaxInd :: T.T -> Int
  getMaxInd (C _ []) = 0
  getMaxInd (C _ ts) = maximum (getMaxInd <$> ts)
  getMaxInd (V var)  = var
  renameHornWith :: Int -> H -> H
  renameHornWith startsFrom (ts, as) = let res = renameHornWithHelper startsFrom (getMinIndex (ts : as)) (ts : as) in
                                       (head res, tail res)
  renameHornWithHelper :: Int -> Int -> [A] -> [A]
  renameHornWithHelper startsFrom delta []             = []
  renameHornWithHelper startsFrom delta ((a, ts):rest) = (a, renameTermWith startsFrom delta <$> ts)
                                                         : renameHornWithHelper startsFrom delta rest
  renameTermWith :: Int -> Int -> T.T -> T.T
  renameTermWith startsFrom delta (V var)  = V (var - delta + startsFrom + 1)
  renameTermWith startsFrom delta (C c ts) = C c (renameTermWith startsFrom delta <$> ts)

-- Recursive evalutor
evalRec :: C -> [T.Subst]
evalRec (p, [])                                     = []
evalRec (p, (t, s, []) : tl)                        = s : evalRec (p, tl)
evalRec (p, (t, s, goal@((atom, terms) : as)) : tl) = 
  case t of
    [] -> evalRec (p, tl)
    h@((newAtom, predTerms), predAtoms) : programTail -> 
      let newStack = (programTail, s, goal) : tl in
      if newAtom /= atom then 
        evalRec (p, newStack)
      else let renamedT           = renameHornHelper s p h in
           let renamedPredAtoms   = snd renamedT           in
           let renamedPredTerms   = snd (fst renamedT)     in
           case unifyLists (Just s) terms renamedPredTerms of
             Nothing  -> evalRec (p, newStack)
             Just mgu -> evalRec (p, (p, mgu, renamedPredAtoms ++ as) : newStack)
                                                
