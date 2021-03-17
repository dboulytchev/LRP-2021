-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Terms.

module Term where

import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.List
import Test.QuickCheck
import Debug.Trace
import Util (farthestDNC)
import Data.Maybe

-- Type synonyms for constructor and variable names
type Cst = Int
type Var = Int

-- A type for terms: either a constructor applied to subterms
-- or a variable
data T = C Cst [T] | V Var deriving (Show, Eq)

-- Free variables for a term; returns a sorted list
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
    f 0 = num numVar >>= return . V
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

apply1 :: Subst -> T -> T
apply1 s t = case t of
    C c ts -> C c (map (apply1 s) ts)
    V v -> (case Term.lookup s v of
      Nothing -> V v
      Just t -> t)

-- Apply a substitution to a term
apply :: Subst -> T -> T
apply s = farthestDNC (apply1 s)

-- Occurs check: checks if a substitution contains a circular
-- binding
occurs :: Subst -> Bool
occurs s =
  let a = Map.map fv s in
  let fix = farthestDNC extend a in
  any (\a -> a `elem` fromJust (Map.lookup a fix)) (Map.keys fix)
  where
    extend a = Map.map (\x -> sort $ foldr Data.List.union x (map (\t -> maybe [] id (Map.lookup t a)) x)) a

-- Well-formedness: checks if a substitution does not contain
-- circular bindings
wf :: Subst -> Bool
wf = not . occurs

-- A composition of substitutions; the substitutions are
-- assumed to be well-formed
infixl 6 <+>

(<+>) :: Subst -> Subst -> Subst
s <+> p = Map.union (Map.map (apply1 p) s) p

-- A condition for substitution composition s <+> p: dom (s) \cup ran (p) = \emptyset
compWF :: Subst -> Subst -> Bool
compWF s p = null $ Set.intersection (Map.keysSet s) (foldr Set.union Set.empty (map (Set.fromList . fv) (Map.elems p)))

-- A property: for all substitutions s, p and for all terms t
--     (t s) p = t (s <+> p)
checkSubst :: (Subst, Subst, T) -> Bool
checkSubst (s, p, t) =
  not (wf s) || not (wf p) || not (compWF s p) || (apply p . apply s $ t) == apply (s <+> p) t

-- This check should pass:
qcEntry = quickCheck $ withMaxSuccess 1000 $ (\ x -> within 1000000 $ checkSubst x)
