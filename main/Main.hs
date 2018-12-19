module Main where

import UVMHS
import Duet

main ∷ IO ()
main = do
  (tohs ∘ list) ^⋅ args ≫= \case
    ["parse",fn] → do
      pprint $ ppHeader "READING"
      s ← read fn
      pprint $ ppHeader "TOKENIZING"
      ts ← stream ^$ tokenizeIO tokDuet $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      parseIOMain (pSkip tokSkip $ pFinal $ parSExp ED_W) ts
    ["check",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← stream ^$ tokenizeIO tokDuet $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      e ← parseIO (pSkip tokSkip $ pFinal $ parSExp ED_W) ts
      do pprint $ ppHeader "TYPE CHECKING" ; flushOut
      let r = runSM dø dø $ inferSens e
      do pprint $ ppHeader "DONE" ; flushOut
      do pprint r ; flushOut
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"

