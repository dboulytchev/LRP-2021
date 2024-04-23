{-# LANGUAGE TupleSections #-}

module SLD where

import           Control.Monad.State.Lazy (MonadState (get, put), State,
                                           evalState, runState)
import qualified Data.Map                 as Map
import qualified Term                     as T (Subst, T (C, V), Var, fv,
                                                lookup)
import qualified Unify                    as U

-- Predicate names
type Pred = Int

-- Atomic formula
type A = (Pred, [T.T])

-- Horn clause
type H = (A, [A])

-- Program
type P = [H]

-- NB: lift over state monad to implement
--     variable renaming in the current program!

-- Top-level evaluator: takes
--   1. a program
--   2. a query
eval :: P -> [A] -> [T.Subst]
eval p q = interestingAnswer where
  interestingAnswer = fst . Map.split nx <$> reducedAnswer
  reducedAnswer = (\s -> reduceToCtor s <$> s) <$> initAnswer
  initAnswer = evalState (evalRec p q p mempty) nx
  nx = newVar q

reduceToCtor :: T.Subst -> T.T -> T.T
reduceToCtor subst (T.V x) = case T.lookup subst x of
  Just t  -> reduceToCtor subst t
  Nothing -> T.V x
reduceToCtor subst (T.C c ts) = T.C c $ reduceToCtor subst <$> ts

evalRec :: P -> [A] -> P -> T.Subst -> State T.Var [T.Subst]
evalRec _ [] _ subst   = pure [subst]
evalRec _ (_ : _) [] _ = pure []
evalRec fullProgram ((gc, gts) : goals) (clause : clauses) subst = do
  ((sc, sts), body) <- renameVarsHornClause clause
  let path2 = evalRec fullProgram ((gc, gts) : goals) clauses subst
  case U.unify (Just subst) (T.C gc gts) (T.C sc sts) of
    Just subst1 -> do
      res1 <- evalRec fullProgram (body ++ goals) fullProgram subst1
      res2 <- path2
      pure $ res1 ++ res2
    Nothing     -> path2

newVar :: [A] -> T.Var
newVar q = maximum (q >>= snd >>= T.fv) + 1

renameVarsHornClause :: H -> State T.Var H
renameVarsHornClause h = do
  x <- get
  let (hh, (y, _)) = runState (renameVarsHornClause_ h) (x, mempty)
  put y
  pure hh

renameVarsHornClause_ :: H -> State (T.Var, Map.Map T.Var T.Var) H
renameVarsHornClause_ (signature, conditions) = do
  newSignature <- renameVarsAtom signature
  newConditions <- mapM renameVarsAtom conditions
  pure (newSignature, newConditions)

renameVarsAtom :: A -> State (T.Var, Map.Map T.Var T.Var) A
renameVarsAtom (p, terms) = (p,) <$> mapM renameVarsTerm terms

renameVarsTerm :: T.T -> State (T.Var, Map.Map T.Var T.Var) T.T
renameVarsTerm (T.V x)    = T.V <$> renameOneVar x
renameVarsTerm (T.C c ts) = T.C c <$> mapM renameVarsTerm ts

renameOneVar :: T.Var -> State (T.Var, Map.Map T.Var T.Var) T.Var
renameOneVar x = do
  (y, m) <- get
  case Map.lookup x m of
    Just z -> pure z
    Nothing -> do
      put (y + 1, Map.insert x y m)
      pure y

-- Examples
_A, _B, _C, _U, _V, _W, _X, _Y, _Z :: T.T
_A = T.V 9
_B = T.V 8
_C = T.V 7
_U = T.V 6
_V = T.V 5
_W = T.V 4
_X = T.V 1
_Y = T.V 2
_Z = T.V 3

_0 :: T.T
_0 = T.C 0 []

suc :: T.T -> T.T
suc k = T.C 1 [k]

nat :: Int -> T.T
nat 0 = _0
nat k | k > 0 = suc $ nat $ k - 1
      | otherwise = error "Negative number"

_1, _2, _3, _4, _5, _6, _7, _8, _9 :: T.T
_1 = suc _0
_2 = suc _1
_3 = suc _2
_4 = suc _3
_5 = suc _4
_6 = suc _5
_7 = suc _6
_8 = suc _7
_9 = suc _8

_peano, _add, _sub, _eq, _lt, _le, _mul :: Pred
_peano = 0
_eq = 1
_lt = 2
_le = 3
_add = 4
_sub = 5
_mul = 6

prog1 :: P
prog1 =
    [ ((_peano, [_0]), [])
    , ((_peano, [suc _X]), [(_peano, [_X])])
    , ((_eq, [_0, _0]), [])
    , ((_eq, [suc _X, suc _Y]), [(_eq, [_X, _Y])])
    , ((_lt, [_0, suc _Y]), [])
    , ((_lt, [suc _X, suc _Y]), [(_lt, [_X, _Y])])
    , ((_le, [_0, _Y]), [])
    , ((_le, [suc _X, suc _Y]), [(_le, [_X, _Y])])
    , ((_add, [_0, _X, _X]), [])
    , ((_add, [suc _X, _Y, suc _Z]), [(_add, [_X, _Y, _Z])])
    , ((_sub, [_X, _Y, _Z]), [(_add, [_Y, _Z, _X])])
    , ((_mul, [_X, _0, _0]), [])
    , ((_mul, [_X, suc _Y, _Z]), [(_mul, [_X, _Y, _W]), (_add, [_X, _W, _Z])])
    ]

query1, query2, query3, query4 :: [A]
query1 = [(_add, [_X, _Y, _5])]
query2 = [(_mul, [_X, _Y, _6])] -- Will not finish
query3 = [(_add, [_X, _Y, _5]), (_add, [_Y, _X, _4])]
query4 = [(_sub, [_X, _Y, _1])] -- Obviously will not finish

-- >>> eval prog1 query1
-- [fromList [(1,_0),(2,_5)],fromList [(1,_1),(2,_4)],fromList [(1,_2),(2,_3)],fromList [(1,_3),(2,_2)],fromList [(1,_4),(2,_1)],fromList [(1,_5),(2,_0)],fromList [(1,_5),(2,_0)]]

-- >>> eval prog1 query3
-- []
