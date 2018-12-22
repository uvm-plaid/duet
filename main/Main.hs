module Main where

import UVMHS
import Duet

initEnv = dict [ var "sign" ↦ (ℝT :⊸: (ι 1 :* ℝT))
               ] ⩌ dø

main ∷ IO ()
main = do
  (tohs ∘ list) ^⋅ args ≫= \case
    ["parse",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      parseIOMain (pSkip tokSkip $ pFinal $ parSExp ED_W) $ stream ts
    ["check",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      e ← parseIO (pSkip tokSkip $ pFinal $ parSExp ED_W) $ stream ts
      do pprint $ ppHeader "TYPE CHECKING" ; flushOut
      let r = runSM dø initEnv $ inferSens e
      do pprint $ ppHeader "DONE" ; flushOut
      do pprint r ; flushOut
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"

