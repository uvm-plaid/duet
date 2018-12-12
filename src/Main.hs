module Main where

import UVMHS
import Duet

main ∷ IO ()
main = do
  pprint $ ppHeader "PARSING"
  s ← read "examples/e.duet"
  ts ← stream ^$ tokenizeIO tokDuet $ tokens s
  parseIOMain (pSkip tokSkip (pFinal parSExp)) ts
