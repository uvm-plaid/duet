module Main where

import UVMHS
import Duet

initEnv ∷ 𝕏 ⇰ Type p RNF
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
      case splitOn𝕊 "." fn of
        n :& "ed" :& "duet" :& Nil →
          parseIOMain (pSkip tokSkip $ pFinal $ parSExp ED_W) $ stream ts
        n :& "renyi" :& "duet" :& Nil →
          parseIOMain (pSkip tokSkip $ pFinal $ parSExp RENYI_W) $ stream ts
        n :& "zcdp" :& "duet" :& Nil →
          parseIOMain (pSkip tokSkip $ pFinal $ parSExp ZC_W) $ stream ts
    ["check",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      -- TODO: this is silly!
      case splitOn𝕊 "." fn of
        n :& "ed" :& "duet" :& Nil → do
          e ← parseIO (pSkip tokSkip $ pFinal $ parSExp ED_W) $ stream ts
          do pprint $ ppHeader "TYPE CHECKING" ; flushOut
          let r = runSM dø initEnv $ inferSens e
          do pprint $ ppHeader "DONE" ; flushOut
          do pprint r ; flushOut
        n :& "renyi" :& "duet" :& Nil → do
          e ← parseIO (pSkip tokSkip $ pFinal $ parSExp RENYI_W) $ stream ts
          do pprint $ ppHeader "TYPE CHECKING" ; flushOut
          let r = runSM dø initEnv $ inferSens e
          do pprint $ ppHeader "DONE" ; flushOut
          do pprint r ; flushOut
        n :& "zcdp" :& "duet" :& Nil → do
          e ← parseIO (pSkip tokSkip $ pFinal $ parSExp ZC_W) $ stream ts
          do pprint $ ppHeader "TYPE CHECKING" ; flushOut
          let r = runSM dø initEnv $ inferSens e
          do pprint $ ppHeader "DONE" ; flushOut
          do pprint r ; flushOut
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"

