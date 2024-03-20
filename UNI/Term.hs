-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Terms.

module Term where

import           Data.List       (nub, sort)
import qualified Data.Map        as Map
import           Test.QuickCheck

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
    f 0 = V <$> num numVar
    f 1 = do cst <- num numCst
             return $ C cst []
    f n = do m   <- pos (n - 1)
             ms  <- split n m
             cst <- num numCst
             sub <- mapM f ms
             return $ C cst sub
    num   n   = getNonNegative <$> (resize n arbitrary :: Gen (NonNegative Int))
    pos   n   = getPositive    <$> (resize n arbitrary :: Gen (Positive    Int))
    iterate acc rest 1 = return $ rest : acc
    iterate acc rest i = do k <- num rest
                            iterate (k : acc) (rest - k) (i-1)
    split = iterate []

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

-- Apply a substitution to a term
apply :: Subst -> T -> T
apply subst (V x) = case Term.lookup subst x of
  Just t  -> t
  Nothing -> V x
apply subst (C c ts) = C c $ apply subst <$> ts

-- Occurs check: checks if a substitution contains a circular
-- binding
occurs :: Subst -> Bool
occurs = any (\(x, t) -> elem x $ fv t) . Map.toList

-- Well-formedness: checks if a substitution does not contain
-- circular bindings
wf :: Subst -> Bool
wf = not . occurs

-- A composition of substitutions; the substitutions are
-- assumed to be well-formed
infixl 6 <+>

(<+>) :: Subst -> Subst -> Subst
s <+> p = s <> p

-- A condition for substitution composition s <+> p: dom (s) \cup ran (p) = \emptyset
compWF :: Subst -> Subst -> Bool
compWF p s = not $ any (\x -> elem x $ ran p) $ Map.keys s
  where
    ran = nub . sort . concatMap (fv . snd) . Map.toList

-- A property: for all substitutions s, p and for all terms t
--     (t s) p = t (s <+> p)
checkSubst :: (Subst, Subst, T) -> Bool
checkSubst (s, p, t) =
  not (wf s) || not (wf p) || not (compWF s p) || (apply p . apply s $ t) == apply (s <+> p) t

-- This check should pass:
qcEntry = quickCheck $ withMaxSuccess 1000 $ within 1000000 . checkSubst
