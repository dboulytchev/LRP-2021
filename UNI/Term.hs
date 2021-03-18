-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Terms.

module Term where

import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.List
import Test.QuickCheck
import Debug.Trace

import Data.Maybe
import Data.Semigroup

-- Type synonyms for constructor and variable names
type Cst = Int
type Var = Int

-- A type for terms: either a constructor applied to subterms
-- or a variable
data T = C Cst [T] | V Var deriving (Show, Eq)

-- Free variables for a term; returns a sorted list
fv :: T -> [Var]
fv = nub . sort . fv' [] where
  fv' acc (V   x  ) = x : acc
  fv' acc (C _ sub) = foldl fv' acc sub

-- QuickCheck instantiation for formulas
-- Don't know how to restrict the number of variables/constructors yet
numVar = 10
numCst = 10

-- "Arbitrary" instantiation for terms
instance Arbitrary T where
  shrink (V _)        = []
  shrink (C cst subs) = subs ++ [ C cst subs' | subs' <- shrink subs ]
  arbitrary = sized f where
    f :: Int -> Gen T
    f 0 = V <$> num numVar
    f 1 = do cst <- num numCst
             return $ C cst []
    f n = do m   <- pos (n - 1)
             ms  <- split n m
             cst <- num numCst
             sub <- mapM f ms
             return $ C cst sub
    num   n   = (resize n arbitrary :: Gen (NonNegative Int)) >>= return . getNonNegative
    pos   n   = (resize n arbitrary :: Gen (Positive    Int)) >>= return . getPositive
    split m n = iterate [] m n
    iterate acc rest 1 = return $ rest : acc
    iterate acc rest i = do k <- num rest
                            iterate (k : acc) (rest - k) (i-1)

-- A type for a substitution: a (partial) map from
-- variable names to terms. Note, this represents not
-- neccessarily idempotent substitution
type Subst = Map.Map Var T

-- Empty substitution
empty :: Subst
empty = Map.empty

-- Lookups a substitution
lookup :: Subst -> Var -> Maybe T
lookup = flip Map.lookup

-- Adds in a substitution
add :: Subst -> Var -> T -> Subst
add s v t = Map.insert v t s

-- The length of the substitution domain
size :: Subst -> Int
size = Map.size


applyOnce :: Subst -> T -> T
applyOnce s t@(V x)   = fromMaybe t (Term.lookup s x)
applyOnce s (C c sub) = C c (applyOnce s <$> sub)

-- compose a (one-time) substitution with itself
expand :: Subst -> Subst
expand s = Map.map (applyOnce s) s

expandN :: Int -> Subst -> Subst
expandN n = appEndo $ stimes n (Endo expand)

-- Apply a substitution to a term
apply :: Subst -> T -> T
apply s = applyOnce $ expandN (size s) s



-- Occurs check: checks if a substitution contains a circular binding

-- Here we exploit the fact that the length of the minimal cycle is no bigger
-- than the number of verticies (even those with positive outdegree i.e. size s)
-- Thus, if we apply the single-step-substitution to itself (size n) times, we
-- either stabilize or produce an immediate reference from variable to itself
-- (occursImmediate)
occurs :: Subst -> Bool
occurs s = any occursImmediate expanded
  where
    occursImmediate s' = any (\(x, t) -> x `elem` fv t) $ Map.assocs s'
    expanded = take (size s) (iterate expand s)

-- Well-formedness: checks if a substitution does not contain
-- circular bindings
wf :: Subst -> Bool
wf = not . occurs

-- A composition of substitutions; the substitutions are
-- assumed to be well-formed
infixl 6 <+>

(<+>) :: Subst -> Subst -> Subst
s <+> p = Map.union (Map.map (apply p) s) p

-- A condition for substitution composition s <+> p: dom (s) \cap ran (p) =
-- \emptyset
compWF :: Subst -> Subst -> Bool
compWF s p = Set.disjoint (Map.keysSet s) (Set.fromList $ fv =<< Map.elems p)

-- A property: for all substitutions s, p and for all terms t
--     (t s) p = t (s <+> p)
checkSubst :: (Subst, Subst, T) -> Bool
checkSubst (s, p, t) =
  not (wf s) || not (wf p) || not (compWF s p) || (apply p . apply s $ t) == apply (s <+> p) t

-- This check should pass:
qcEntry = quickCheck $ withMaxSuccess 1000 $ (\ x -> within 1000000 $ checkSubst x)
