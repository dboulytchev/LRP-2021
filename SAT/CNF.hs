-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import Formula
import Data.List
import Control.Monad.State.Lazy

import Debug.Trace

-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]

-- Tseitin's conversion
toCNF :: F -> CNF
toCNF f = let fs = toFs f in
          let (Var k) = head fs in 
          ([k]):(concatMap toCNFSingle (tail fs))

toCNFSingle :: F -> CNF
toCNFSingle (Var x :<=>: Var y) = [[-x, y], [x, -y]]
toCNFSingle (Var x :<=>: Neg (Var y)) = [[-x, -y], [x, y]]
toCNFSingle (Var x :<=>: (Var y :/\: Var z)) = [[x, -y, -z], [-x, y], [-x, z]]
toCNFSingle (Var x :<=>: (Var y :\/: Var z)) = [[-x, y, z], [x, -y], [x, -z]]
toCNFSingle (Var x :<=>: (Var y :<=>: Var z)) = [[x, -y, -z], [x, y, z], [-x, y, -z], [-x, -y, z]]
toCNFSingle (Var x :<=>: (Var y :=>: Var z)) = [[-x, -y, z], [x, y], [x, -z]]

getMaxNumber :: F -> Int
getMaxNumber (Var x) = x
getMaxNumber (Neg f) = getMaxNumber f
getMaxNumber (f1 :/\: f2) = max (getMaxNumber f1) (getMaxNumber f2)
getMaxNumber (f1 :\/: f2) = max (getMaxNumber f1) (getMaxNumber f2)
getMaxNumber (f1 :<=>: f2) = max (getMaxNumber f1) (getMaxNumber f2)
getMaxNumber (f1 :=>: f2) = max (getMaxNumber f1) (getMaxNumber f2)


toFs :: F -> [F]
toFs f = evalState (do
    (fs, i, f') <- toFsAux f
    return $ (Var i):((Var i) :<=>: f'):fs) (getMaxNumber f)

getFresh :: State Int Int
getFresh = state (\st -> (st + 1, st + 1))

toFsAux :: F -> State Int ([F], Int, F)
toFsAux (Var x) = return ([], x, Var x)

toFsAux (Neg f) = do
    (fs, i, f') <- toFsAux f
    let fs' = ((Var i) :<=>: f'):fs
    i' <- getFresh
    return (fs', i', Neg (Var i))

toFsAux (f1 :/\: f2) = do
    (fs1, i1, f1') <- toFsAux f1
    (fs2, i2, f2') <- toFsAux f2
    let fs' = ((Var i1) :<=>: f1'):((Var i2) :<=>: f2'):(fs1 ++ fs2)
    i' <- getFresh
    return (fs', i', (Var i1) :/\: (Var i2))

toFsAux (f1 :\/: f2) = do
    (fs1, i1, f1') <- toFsAux f1
    (fs2, i2, f2') <- toFsAux f2
    let fs' = ((Var i1) :<=>: f1'):((Var i2) :<=>: f2'):(fs1 ++ fs2)
    i' <- getFresh
    return (fs', i', (Var i1) :\/: (Var i2))

toFsAux (f1 :<=>: f2) = do
    (fs1, i1, f1') <- toFsAux f1
    (fs2, i2, f2') <- toFsAux f2
    let fs' = ((Var i1) :<=>: f1'):((Var i2) :<=>: f2'):(fs1 ++ fs2)
    i' <- getFresh
    return (fs', i', (Var i1) :<=>: (Var i2))

toFsAux (f1 :=>: f2) = do
    (fs1, i1, f1') <- toFsAux f1
    (fs2, i2, f2') <- toFsAux f2
    let fs' = ((Var i1) :<=>: f1'):((Var i2) :<=>: f2'):(fs1 ++ fs2)
    i' <- getFresh
    return (fs', i', (Var i1) :=>: (Var i2))
        

-- The inverse conversion
fromCNF (h : tl) = foldl (\ acc c -> acc :/\: fromClause c) (fromClause h) tl where
  fromClause (h : tl)  = foldl (\ acc v -> acc :\/: fromVar v) (fromVar h) tl
  fromVar n | n < 0     = Neg $ Var (-n)
            | otherwise = Var n

-- The equisatisfability of Tseitin's conversion
equisaT :: F -> Bool
equisaT f = Formula.equisat f (fromCNF $ CNF.toCNF f)

fromPart :: [F] -> F
fromPart (x : xs) = foldl (\acc c -> acc :/\: c) x xs

equisaTPart :: F -> Bool
equisaTPart f = Formula.equisat f (fromPart $ CNF.toFs f)

-- Tseitin's conversion gives a CNF
isCNF :: F -> Bool
isCNF = Formula.isCNF . fromCNF . CNF.toCNF 
