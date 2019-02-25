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
        let r = runSM dø initEnv dø $ inferSens e
        do pprint $ ppHeader "DONE" ; flushOut
        do pprint r ; flushOut
    ["run",fn] → do
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      unpack_C (parseMode fn) $ \ mode → do
        e ← parseIO (pSkip tokSkip $ pFinal $ parPExp mode) $ stream ts
        do pprint $ ppHeader "TYPE CHECKING" ; flushOut
        let τ = runPM dø initEnv dø $ inferPriv e
        do pprint $ ppHeader "RUNNING" ; flushOut
        r ← peval dø (extract e)
        do pprint $ ppHeader "DONE" ; flushOut
        ys ← read "data_short/ffys.csv"
        xs ← read "data_short/ffxs.csv"

        let ysms = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\r\n" ys
        let xsms = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\r\n" xs
        let ks = (50 :* 50 :* 0.1 :* 10 :* 1.0 :* 1.0 :* Nil)
        let xsm = csvToMatrix (list xsms)
        let ysm = csvToMatrix (list ysms)
        let as = list [xsm, ysm, RealV 0.1, NatV 10, RealV 1.0, RealV 1.0, RealV 2.0]
        case r of
          PFunV xs e γ → do
            r' ← peval (assoc (zip xs as) ⩌ γ) e
            pprint r'

        -- r' ← peval dø AppPE $ e ks as

        do pprint r ; flushOut

        -- do pprint r' ; flushOut

    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"
