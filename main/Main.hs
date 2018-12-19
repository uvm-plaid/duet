module Main where

import UVMHS
import Duet

main ∷ IO ()
main = do
  pprint $ ppHeader "READING"
  flushOut
  s ← read "examples/e.duet"
  pprint $ ppHeader "TOKENIZING"
  flushOut
  ts ← stream ^$ tokenizeIO tokDuet $ tokens s
  pprint $ ppHeader "PARSING"
  flushOut
  e ← parseIO (pSkip tokSkip $ pFinal $ parSExp ED_W) ts
  pprint $ ppHeader "TYPE CHECKING"
  flushOut
  let r = runSM dø dø $ inferSens e
  pprint $ ppHeader "DONE"
  flushOut
  pprint r
  flushOut
