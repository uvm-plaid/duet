module Main where

import UVMHS
import Duet

main ∷ IO ()
main = do
  pprint $ ppHeader "PARSING"
  s ← read "examples/e.duet"
  ts ← stream ^$ tokenizeIO tokDuet $ tokens s
  e ← parseIO (pSkip tokSkip $ pFinal $ parSExp ED_W) ts
  pprint $ runSM dø dø $ inferSens e
