module Main where

import UVMHS
import Duet

initEnv ∷ 𝕏 ⇰ Type RNF
initEnv = dict [ var "sign" ↦ (ℝT :⊸: (ι 1 :* ℝT))
               ] ⩌ dø

parseMode ∷ 𝕊 → Ex_C PRIV_C PRIV_W
parseMode s = case splitOn𝕊 "." s of
  _ :& "ed" :& "duet" :& Nil → Ex_C ED_W
  _ :& "renyi" :& "duet" :& Nil → Ex_C RENYI_W
  _ :& "zcdp" :& "duet" :& Nil → Ex_C ZC_W
  _ → error "BAD FILE NAME"

main ∷ IO ()
main = do
  (tohs ∘ list) ^⋅ args ≫= \case
    ["parse",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      unpack_C (parseMode fn) $ \ mode → 
        parseIOMain (pSkip tokSkip $ pFinal $ parSExp mode) $ stream ts
    ["check",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      unpack_C (parseMode fn) $ \ mode → do
        e ← parseIO (pSkip tokSkip $ pFinal $ parSExp mode) $ stream ts
        do pprint $ ppHeader "TYPE CHECKING" ; flushOut
        let r = runSM dø initEnv $ inferSens e
        do pprint $ ppHeader "DONE" ; flushOut
        do pprint r ; flushOut
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"

