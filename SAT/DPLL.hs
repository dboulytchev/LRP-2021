{-# LANGUAGE ScopedTypeVariables #-}

-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Devis-Putnam-Davis–Putnam–Logemann–Loveland algorithm
-- for propositional satisfability

import           CNF
import           Control.Exception
import           Control.Monad
import           Data.List               (find)
import           Data.Set                (Set)
import qualified Data.Set                as Set
import qualified Formula
import           System.Random
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

-- A partial assignment (valuation): a *consistent* set of
-- chosen literals (i.e. it can not contain l and ~l simultaneously).
type Val = Set Formula.Var

-- Convert valuation-as-set into a valuation-as-function
-- for property-based testing
toVal :: Val -> Formula.Val
toVal =
  Set.foldl
    (\ v l -> Formula.extend v (abs l) $ l > 0)
    Formula.empty

-- An exception to throw when an inconsistent choice of literals is encountered
data UnSat = UnSat deriving Show

instance Exception UnSat

-- A helper functions: catches the UnSat exception and
-- converts its into an empty list
withUnSat :: IO [a] -> IO [a]
withUnSat action = catch action (\ (_ :: UnSat) -> return [])

-- Unit propagation. Takes a formula and returns a pair of reduced formula and partial assignment
-- (a set of chosen literals).
-- If there a unit clause (i.e. a clause containing a single literal, say, l) choose this literal
-- and propagate the choice through the rest of the formula: if there is a clause containing l,
-- remove this clause completely (since it is satisfied by the choice of l); if a clause
-- contains ~l, remove all the occurencies of ~l in this clause (since ~l is set to false by the
-- choice of l). Note: unit propagation should be iterated until a fixpoint since a propagation
-- w.r.t. one literal can open the possibilities for unit propagations w.r.t. another. Note also,
-- unit propagation can result in an inconsistent assignment which has to be detected and
-- handled properly by throwing the UnSat exception.
propagateUnitLiterals :: CNF -> IO (CNF, Val)
propagateUnitLiterals f = do
  let (cnf, xs) = doIterate f
  if any null cnf
    then throw UnSat
    else pure (cnf, xs)

  where
    doIterate :: CNF -> (CNF, Val)
    doIterate cnf = case step cnf of
      Just (cnf', x) -> let (cnf'', xs) = doIterate cnf' in (cnf'', Set.insert x xs)
      Nothing        -> (cnf, mempty)

    step :: CNF -> Maybe (CNF, Formula.Var)
    step cnf = do
      x <- findVar cnf
      pure (substitute x cnf, x)

    substitute :: Formula.Var -> CNF -> CNF
    substitute x = filter (notElem x) . map (filter (/= -x))

    findVar :: CNF -> Maybe Formula.Var
    findVar []        = Nothing
    findVar ([x] : _) = Just x
    findVar (_ : xs)  = findVar xs

-- Pure literal propagation. Takes a formula, returns reduced formula and partial
-- assignment.
-- A literal is *pure* if all its occurrencies in the formula has the same polarity.
-- A pure literal can be chosen with no conflicts and all containing it clauses can
-- be removed.
propagatePureLiterals :: CNF -> (CNF, Val)
propagatePureLiterals = doIterate
  where
    doIterate :: CNF -> (CNF, Val)
    doIterate cnf = case step cnf of
      Just (cnf', x) -> let (cnf'', xs) = doIterate cnf' in (cnf'', Set.insert x xs)
      Nothing        -> (cnf, mempty)

    step :: CNF -> Maybe (CNF, Formula.Var)
    step cnf = do
      x <- findPure cnf
      pure (substitute x cnf, x)

    substitute :: Formula.Var -> CNF -> CNF
    substitute x = filter (notElem x)

    findPure :: CNF -> Maybe Formula.Var
    findPure cnf = find (`isPureIn` cnf) (join cnf)

    isPureIn :: Formula.Var -> CNF -> Bool
    isPureIn x = all (notElem (-x))

-- Subsumed clauses elimination. Takes a formula, returns a reduced formula.
-- A clause c is subsumed by c' iff all literals from c' occur in c (in other
-- words, c contains c' plus some other literals. If c' is satisfied, c
-- also is satisfied, and, thus, can be removed. Subsumed clauses elimination
-- can not lead to conflicts.
eliminateSubsumedClauses :: CNF -> CNF
eliminateSubsumedClauses [] = []
eliminateSubsumedClauses (c : cs') =
  if any (`subsumes` c) cs
    then cs
    else c : filter (not . subsumes c) cs
  where
    cs = eliminateSubsumedClauses cs'
    subsumes a b = all (`elem` b) a

-- Chooses a random (well, pseudo-random) literal of the formula for
-- the branching. Returns a pair of literals for the same variable
-- with different polarities to branch on.
chooseRandomLiteral :: CNF -> IO (Formula.Var, Formula.Var)
chooseRandomLiteral f = do
  ci <- getStdRandom (randomR (0 :: Int, length f - 1 :: Int))
  let clause = f !! ci
  li <- getStdRandom (randomR (0 :: Int, length clause - 1 :: Int))
  let lit = clause !! li
  return (lit, -lit)

-- Applies a valuation to reduce a formula. Takes a valuation and
-- a formula, returns a pair --- a flag indicating if the fomula
-- has changed and a new formula. As some clauses can be eliminated
-- in a given valuation, the function can throw UnSat exception.
applyValuation :: Val -> CNF -> IO (Bool, CNF)
applyValuation s = foldl (\ acc c ->
            do
              (f, acc) <- acc
              case foldl (\ c' l ->
                            do (c', f) <- c'
                               if Set.member l s then Nothing
                               else if Set.member (-l) s
                                    then return (c', True)
                                    else return (l : c', f)
                         ) (Just ([], False)) c of
                Just ([], _)  -> throw UnSat
                Just (c', f') -> return (f' || f, c' : acc)
                Nothing       -> return (True, acc)
        ) (return (False, []))

-- Branching on a literal.
-- Branching step chooses an arbitrary variable and considers
-- two cases with this variable set to True and to False. The
-- result is a list of pairs of reduced formulas and partial
-- assignments. Since some assignments can lead to insonsistency,
-- the list can be empty.
branch :: CNF -> IO [(CNF, Val)]
branch f = do
  (l1, l2) <- chooseRandomLiteral f
  f1  <- apply l1 f
  f2  <- apply l2 f
  return $ f1 ++ f2
  where
    apply :: Formula.Var -> CNF -> IO [(CNF, Val)]
    apply v f =
      let v' = Set.singleton v in
      withUnSat $ do (_, f') <- applyValuation v' f
                     return [(f', v')]

-- DPLL main infrastructure.
-- It eagerly repeats unit propagation / pure literal propagation / subsumed clauses elimination
-- and then (if the results still unclear) performes branching and repeats itself for
-- all branching outcomes.
dpll :: CNF -> IO [Val]
dpll f = iterate f Set.empty  where
  iterate :: CNF -> Val -> IO [Val]
  iterate f v =
    withUnSat $ do (f', v' ) <- propagateUnitLiterals f
                   let (f'', v'') = propagatePureLiterals f'
                   let f'''       = eliminateSubsumedClauses f''
                   let v'''       = v `Set.union` v' `Set.union` v''
                   case f''' of
                     [] -> return [v''']
                     _  -> do bs <- branch f'''
                              foldl (\ acc (f, v) -> do
                                       acc <- acc
                                       val <- iterate f (Set.union v''' v)
                                       return $ val ++ acc
                                    ) (return []) bs

-- QuickCheck property. Takes a formula, converts it into CNF,
-- solves with DPLL and checks, that the assignment satisifies the formula.
-- If no assignments found, checks, that the formula unsatisfiable.
check :: Formula.F -> Property
check f =
  let cnf = CNF.toCNF   f   in
  let f'  = fromCNF cnf in
  monadicIO $ do vals <- run $ dpll cnf
                 return $ case vals of
                          [] -> null $ Formula.solve f'
                          _  -> all (\ v -> Formula.eval (toVal v) f') vals

-- Entry function. Performs property-based testing.
main :: IO ()
main = do
 quickCheck (mapSize (const 10) check)
