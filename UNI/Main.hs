module Main where

import qualified Term as T
import qualified Unify as U


main = do
    putStrLn "Check Term.(<+>)"
    T.qcEntry

    putStrLn "Check Unify.unify"
    U.qcEntry
