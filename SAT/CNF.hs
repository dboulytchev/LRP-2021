-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import Formula
import Data.List
import Control.Monad.State.Lazy

-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]

-- Tseitin's conversion
toCNF :: Formula.F -> CNF
toCNF f = formulaCNFToListCNF $ fst $ tseitinTransform f $ Formula.maxVar f + 1 where
  tseitinTransform :: Formula.F -> Var -> (Formula.F, Var)
  tseitinTransform f@(Var var)       mxVr = (f, var)
  tseitinTransform f@(Neg (Var var)) mxVr = (f, -var)
  tseitinTransform (Neg origF)       mxVr = (fst $ tseitinTransform (Neg (Var mxVr) :<=>: origF) (mxVr + 1), mxVr)
  tseitinTransform (l :/\:  r)       mxVr = let (lhsF, lhsV) = tseitinTransform l (mxVr + 1) in
                                            let (rhsF, rhsV) = tseitinTransform r (max (mxVr + 1) $ Formula.maxVar lhsF + 1) in
                                            (Var mxVr :/\: Formula.toCNF (Var mxVr :<=>: (Var lhsV :/\: Var rhsV)) 
                                                      :/\: lhsF 
                                                      :/\: rhsF
                                            , mxVr)
  tseitinTransform (l :\/:  r)       mxVr = let (lhsF, lhsV) = tseitinTransform l (mxVr + 1) in
                                            let (rhsF, rhsV) = tseitinTransform r (max (mxVr + 1) $ Formula.maxVar lhsF + 1) in
                                            (Var mxVr :/\: Formula.toCNF (Var mxVr :<=>: (Var lhsV :\/: Var rhsV)) 
                                                      :/\: lhsF 
                                                      :/\: rhsF
                                            , mxVr)
  tseitinTransform (l :<=>: r)       mxVr = let (lhsF, lhsV) = tseitinTransform l (mxVr + 1) in
                                            let (rhsF, rhsV) = tseitinTransform r (max (mxVr + 1) $ Formula.maxVar lhsF + 1) in
                                            (Var mxVr :/\: Formula.toCNF (Var mxVr :<=>: (Var lhsV :<=>: Var rhsV)) 
                                                      :/\: lhsF 
                                                      :/\: rhsF
                                              , mxVr)
  tseitinTransform (l :=>:  r)       mxVr = let (lhsF, lhsV) = tseitinTransform l (mxVr + 1) in
                                            let (rhsF, rhsV) = tseitinTransform r (max (mxVr + 1) $ Formula.maxVar lhsF + 1) in
                                            (Var mxVr :/\: Formula.toCNF (Var mxVr :<=>: (Var lhsV :=>: Var rhsV)) 
                                                      :/\: lhsF 
                                                      :/\: rhsF
                                            , mxVr)
  formulaCNFToListCNF :: Formula.F -> CNF
  formulaCNFToListCNF (Var var)       = [[var]]
  formulaCNFToListCNF (Neg (Var var)) = [[-var]]
  formulaCNFToListCNF (l :\/: r)      = [head (formulaCNFToListCNF l) ++ head (formulaCNFToListCNF r)]
  formulaCNFToListCNF (l :/\: r)      = formulaCNFToListCNF l ++ formulaCNFToListCNF r


-- The inverse conversion
fromCNF :: CNF -> Formula.F
fromCNF (h : tl) = foldl (\ acc c -> acc :/\: fromClause c) (fromClause h) tl where
  fromClause (h : tl)  = foldl (\ acc v -> acc :\/: fromVar v) (fromVar h) tl
  fromVar n | n < 0     = Neg $ Var (-n)
            | otherwise = Var n

-- The equisatisfability of Tseitin's conversion
equisaT :: F -> Bool
equisaT f = Formula.equisat f (fromCNF $ CNF.toCNF f)

-- Tseitin's conversion gives a CNF
isCNF :: F -> Bool
isCNF = Formula.isCNF . fromCNF . CNF.toCNF 
