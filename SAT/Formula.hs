-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Generic-shape propositional formulas.

module Formula where

import Data.Maybe
import Data.List
import Test.QuickCheck

-- The type for variables
type Var = Int -- positive, otherwise an ambiguity occurs with negative variables

-- The type for variable valuations; some variable values may be
-- irrelevant, hence Maybe
type Val = Var -> Maybe Bool

-- Empty (undefined) valuation
empty :: Val
empty _ = Nothing

-- Extend a valuation v with a new binding
extend :: Val -> Var -> Bool -> Val
extend v n b x | x == n    = Just b
               | otherwise = v x

-- The type for propositional formulas
data F = Var Var   | -- variable
         Neg F     | -- negation
         F :/\: F  | -- conjunction
         F :\/: F  | -- disjunction
         F :=>: F  | -- implication
         F :<=>: F   -- equivalence
 deriving Show

-- QuickCheck instantiation for formulas
-- Don't know how to restrict the number of variables yet
numVar = 10

-- "Arbitrary" instantiation for formulas
instance Arbitrary F where
  shrink (Neg f) = f : [Neg g | g <- shrink f]
  shrink (Var _) = []
  shrink f       =
    let (c, p, q) = case f of
          p :/\:  q -> ((:/\:) , p, q)
          p :\/:  q -> ((:\/:) , p, q)
          p :<=>: q -> ((:<=>:), p, q)
          p :=>:  q -> ((:=>:) , p, q)
    in
    [Var 1, p, q] ++ [c p' q' | (p', q') <- shrink (p, q)]
  arbitrary = sized f where
    f :: Int -> Gen F
    f 0 = (resize numVar arbitrary :: Gen (Positive Int)) >>= return . Var . getPositive
    f n = oneof [f (n-1) >>= return . Neg,
                 do
                   fm <- f m
                   fk <- f k
                   elements [fm :/\: fk, fm :\/: fk, fm :<=>: fk, fm :=>: fk]
                ] where
      m = div n 2
      k = m + mod n 2

-- A sorted list of variables for a formula
fv :: F -> [Var]
fv f = sort $ nub $ fvacc [] f where
  fvacc acc (Var n)     = n : acc
  fvacc acc (Neg f)     = fvacc acc f
  fvacc acc (m :/\:  n) = fvacc (fvacc acc m) n
  fvacc acc (m :\/:  n) = fvacc (fvacc acc m) n
  fvacc acc (m :=>:  n) = fvacc (fvacc acc m) n
  fvacc acc (m :<=>: n) = fvacc (fvacc acc m) n

-- A list of all possible valuations for a formula
allVals :: F -> [Val]
allVals f = allValsVars $ fv f where
  allValsVars []       = []
  allValsVars (v : vs) = concat [[extend val v True, extend val v False] | val <- allValsVars vs]

-- The maximal number of variable
maxVar :: F -> Var
maxVar = maxVar' 0 where
  maxVar'  n (Var m)     = max m n
  maxVar'  n (Neg f)     = maxVar' n f
  maxVar'  n (m :/\:  p) = maxVar' (maxVar' n m) p
  maxVar'  n (m :\/:  p) = maxVar' (maxVar' n m) p
  maxVar'  n (m :=>:  p) = maxVar' (maxVar' n m) p
  maxVar'  n (m :<=>: p) = maxVar' (maxVar' n m) p

-- Evaluation w.r.t. a valuation; always returns a boolean value
eval :: Val -> F -> Bool
eval v f = fromJust $ eval' v f where
  eval' v (Var n)     = v n
  eval' v (Neg n)     = eval' v n >>= return . not
  eval' v (m :/\: n)  =
    case (eval' v m, eval' v n) of
      (Just False, _         ) -> Just False
      (_         , Just False) -> Just False
      (Just True , Just True ) -> Just True
      _                        -> Nothing
  eval' v (m :\/: n) =
    case (eval' v m, eval' v n) of
      (Just True , _         ) -> Just True
      (_         , Just True ) -> Just True
      (Just False, Just False) -> Just False
      _                        -> Nothing
  eval' v (m :<=>: n) = return $ eval' v m == eval' v n
  eval' v (m :=>:  n) =
    case eval' v m of
      Nothing    -> eval' v n
      Just False -> Just True
      _          -> eval' v n

-- Naively finds all satisfying valuations
solve :: F -> [Val]
solve = solve' empty True where
  solve' v b (Var n) =
    case v n of
      Just b' -> if b == b' then [v] else []
      Nothing -> [extend v n b]
  solve' v b (Neg l)       = solve' v (not b) l
  solve' v b (l1 :/\: l2) =
    if b
    then concat [solve' v' b l2 | v' <- solve' v b l1]
    else solve' v b l1 ++ solve' v b l2
  solve' v b (l1 :\/:  l2) = solve' v b (Neg (Neg l1 :/\: Neg l2))
  solve' v b (l1 :=>:  l2) = solve' v b (Neg l1 :\/: l2)
  solve' v b (l1 :<=>: l2) = solve' v b ((Neg l1 :\/: l2) :/\: (Neg l2 :\/: l1))

-- Check an equivalence in a naive way
checkEquiv :: F -> F -> Bool
checkEquiv f g =
  let vars = fv f in
  vars == fv g &&
  and [eval val f == eval val g | val <- allVals f]

-- Checks if all valuations in a given set are, indeed, satisfying;
-- returns a boolean result
checkSAT :: F -> [Val] -> Bool
checkSAT f vals = and [eval v f | v <- vals]

-- Naively transforms a formula into CNF (with potentially
-- exponential grow)
toCNF (f :=>:  g) = toCNF (Neg f :\/: g)
toCNF (f :<=>: g) = toCNF ((f :=>: g) :/\: (g :=>: f))
toCNF (f :/\: g)  = toCNF f :/\: toCNF g
toCNF (f :\/: g)  = distribute (toCNF f) (toCNF g) where
  distribute c            (g1 :/\: g2) = (distribute c g1) :/\: (distribute c g2)
  distribute f@(_ :/\: _)  c           = distribute c f
  distribute f             g           = f :\/: g
toCNF f@(Neg (Var _)) = f
toCNF (Neg f)     = toCNF $ neg f where
  neg f@(Var _)     = Neg f
  neg (Neg (Neg f)) = neg f
  neg (Neg f)       = f
  neg (f :/\: g)    = neg f :\/: neg g
  neg (f :\/: g)    = neg f :/\: neg g
  neg (f :=>: g)    = neg (Neg f :\/: g)
  neg (f :<=>: g)   = neg $ (f :=>: g) :/\: (g :=>: f)
toCNF f = f

-- Some QuickCheck properties
-- `solve` solves
solveSolves :: F -> Bool
solveSolves f = checkSAT f $ solve f

-- Equisatsfability
equisat :: F -> F -> Bool
equisat f g =
  case (solve f, solve g) of
    (_ : _, _ : _) -> True
    ([], [])       -> True
    _              -> False

-- if an argument in CNF
isCNF :: F -> Bool
isCNF (f :/\: g) = and [isCNF f, isCNF g]
isCNF (f :\/: g) = and [isClause f, isClause g] where
  isClause (f :\/:  g) = and [isClause f, isClause g]
  isClause (Neg (Var _)) = True
  isClause (Var _)       = True
  isClause _             = False
isCNF (Neg (Var _)) = True
isCNF (Var _)       = True
isCNF _             = False

-- toCNF f <=> f
toCNFequiv :: F -> Bool
toCNFequiv f = checkEquiv f (toCNF f)
