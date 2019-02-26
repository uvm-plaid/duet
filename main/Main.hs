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

buildArgs ∷ 𝐿 (Type r) → 𝐿 𝕊 → IO (𝐿 Val)
buildArgs Nil Nil = return Nil
buildArgs (τ:&τs) (a:&as) = case τ of
  (𝕄T _ _ _ _) → do
    csvs ← read a
    let csvss = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\r\n" csvs
    let csvm = csvToMatrix (list csvss)
    r ← buildArgs τs as
    return $ csvm :& r
  ℕT → do
    r ← buildArgs τs as
    return $ NatV (read𝕊 a) :& r
  ℕˢT _ → do
    r ← buildArgs τs as
    return $ NatV (read𝕊 a) :& r
  ℝT → do
    r ← buildArgs τs as
    return $ RealV (read𝕊 a) :& r
  ℝˢT _ → do
    r ← buildArgs τs as
    return $ RealV (read𝕊 a) :& r
  _ → error $ "unexpected arg type in main"
buildArgs _ _ = error "number of args provided does not match function signature"


drop :: ℕ -> IO (𝐼 𝕊) -> IO (𝐼 𝕊)
drop x as = do
  as' ← as
  case list as' of
    Nil → return empty𝐼
    (_ :& ys) → do
      case x ≡ 1 of
        True → return $ iter ys
        False → drop (x-1) (return (iter ys))

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
    "run":fn:_ → do
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
        do pprint r ; flushOut
        fnargs ← drop 2 args
        case τ of
          Inr rv → do
            case rv of
              _ :* (_ :* PArgs pargs) :⊸⋆: _ → do
                let τs = map fst pargs
                as ← buildArgs τs (list fnargs)
                case r of
                  PFunV xs e₁ γ → do
                    r' ← peval (assoc (zip xs as) ⩌ γ) e₁
                    pprint r'
                    pprint $ ppHeader "DONE" ; flushOut
                  _ → error "expected pλ at top level"
              _ → error "expected pλ at top level"
          _ → error "typechecking phase encountered an error"
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"
