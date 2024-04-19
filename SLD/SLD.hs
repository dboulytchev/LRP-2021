module Main where

import qualified Data.Map as Map
import Control.Monad.State

import qualified Term as T
import Unify


-- Predicate names
type Pred = Int

-- Atomic formula
type A = (Pred, [T.T])

-- Horn clause
data H = A :- [A]

-- Program
type P = [H]

-- Configuration
--   1. A whole source program
--   2. A stack of states each of which is
--      1. a tail of a program to match against
--      2. current substitution
--      3. current goal

type St = [(P, T.Subst, [A])]
type C = (P, St)

-- NB: lift over state monad to implement
--     variable renaming in the current program!

-- Top-level evaluator: takes
--   1. a program
--   2. a query
eval :: P -> [A] -> [T.Subst]
eval p q = let mv = maximum $ q >>= snd >>= T.fv
           in fst <$> Map.split (mv + 1) <$> evalRec (p, [(p, T.empty, q)]) mv

freshVar :: MonadState T.Var m => m T.T
freshVar = state $ \v -> let v' = v + 1 in (T.V v', v')

refreshs'
    :: (MonadState T.Var m, Foldable t)
    => (T.Subst -> a -> m (T.Subst, a))
    -> T.Subst -> t a -> m (T.Subst, [a])
refreshs' refresh s = ((reverse <$>) <$>) . foldM (\(s, ts) -> fmap ((: ts) <$>) . refresh s) (s, [])

refresh :: MonadState T.Var m => T.Subst -> T.T -> m (T.Subst, T.T)
refresh s (T.V v) | Just t' <- Map.lookup v s = return (s, t')
                  | otherwise                 = (\t' -> (Map.insert v t' s, t')) <$> freshVar
refresh s (T.C c ts) = (T.C c <$>) <$> refreshs s ts

refreshs :: (MonadState T.Var m, Foldable t) => T.Subst -> t T.T -> m (T.Subst, [T.T])
refreshs = refreshs' refresh

refreshA :: MonadState T.Var m => T.Subst -> A -> m (T.Subst, A)
refreshA s (x, ts) = ((x ,) <$>) <$> refreshs s ts

refreshAs :: (MonadState T.Var m, Foldable t) => T.Subst -> t A -> m (T.Subst, [A])
refreshAs = refreshs' refreshA

refreshH :: MonadState T.Var m => H -> m H
refreshH (t :- ts) = (\(t':ts') -> t' :- ts') <$> snd <$> refreshAs T.empty (t:ts)

-- Recursive evalutor
evalRec :: C -> T.Var -> [T.Subst]
evalRec (p, st) = evalState (evalRec' st) where

    evalRec' :: MonadState T.Var m => St -> m [T.Subst]
    evalRec' [] = pure []
    evalRec' ((_, s, []):st) = (s :) <$> evalRec' st
    evalRec' (([], _, _:_):st) = evalRec' st
    evalRec' ((h@((hx, _) :- _):p', s, g@((x, ts):g')):st)
        | x /= hx = evalRec' $ (p', s, g):st
        | otherwise = refreshH h >>= \((_, hts) :- hb) -> case unify s (T.C 0 hts) (T.C 0 ts) of
            Just s' -> evalRec' $ (p, s', hb <> g'):(p', s, g):st
            Nothing -> evalRec' $ (p', s, g):st

{-
add(z, X, X).
add(s(X), Y, s(Z)) :- add(X, Y, Z).

mul(z, X, z).
mul(s(X), Y, Z) :- add(W, Y, Z), mul(X, Y, W).
-}

_X = T.V 1
_Y = T.V 2
_Z = T.V 3
_W = T.V 4

z = T.C 1 []
s x = T.C 2 [x]

add (x, y, z) = (1, [x, y, z])
mul (x, y, z) = (2, [x, y, z])

prog :: P
prog =
    [ add(z, _X, _X) :- []
    , add(s(_X), _Y, s(_Z)) :- [add(_X, _Y, _Z)]
    , mul(z, _X, z) :- []
    , mul(s(_X), _Y, _Z) :- [add(_W, _Y, _Z), mul(_X, _Y, _W)]
    ]

main = mapM_ print $ eval prog [mul(_X, s(_X), s(s(s(s(_Y)))))]
