module Main where

import UVMHS
import Duet

initEnv ∷ 𝕏 ⇰ Type RNF
initEnv = dict [ var "sign" ↦ (ℝT :⊸: (ι 1 :* ℝT))
               ] ⩌ dø

parseMode ∷ 𝕊 → Ex_C PRIV_C PRIV_W
parseMode s = case splitOn𝕊 "." s of
  _ :& "eps" :& "duet" :& Nil → Ex_C EPS_W
  _ :& "ed" :& "duet" :& Nil → Ex_C ED_W
  _ :& "renyi" :& "duet" :& Nil → Ex_C RENYI_W
  _ :& "tcdp" :& "duet" :& Nil → Ex_C TC_W
  _ :& "zcdp" :& "duet" :& Nil → Ex_C ZC_W
  _ → error "BAD FILE NAME"

-- TODO: detect line endings or make an arg
buildArgs ∷ (Pretty r) ⇒ 𝐿 (Type r) → 𝐿 𝕊 → IO (𝐿 Val)
buildArgs Nil Nil = return Nil
buildArgs (τ:&τs) (a:&as) = case τ of
  -- TODO: currently the assumption is to read in RealVs
  (𝕄T _ _ _ (RexpME r τ)) → do
    csvs ← read a
    let csvss = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" csvs
    let csvm = csvToMatrix (list csvss)
    r ← buildArgs τs as
    return $ csvm :& r
  (𝕄T _ _ _ (ConsME τ m)) → do
    csvs ← read a
    let csvss = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" csvs
    let csvm = csvToDF (list csvss) (schemaToTypes (ConsME τ m))
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

intercalate ∷ 𝕊 → 𝐿 𝕊 → 𝕊
intercalate sep arr = case arr of
  Nil -> ""
  (x :& Nil) -> x
  (x :& xs) -> x ⧺ sep ⧺ intercalate sep xs

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
        e ← parseIO (pSkip tokSkip $ pFinal $ parPExp mode) $ stream ts
        do pprint $ ppHeader "TYPE CHECKING" ; flushOut
        let r = runPM dø initEnv dø $ inferPriv e
        do pprint $ ppHeader "DONE" ; flushOut
        do pprint r ; flushOut
    "lr-accuracy":xsfn:ysfn:mdfn:[] → do
      do pprint $ ppHeader "ACCURACY TEST" ; flushOut
      csvs₁ ← read mdfn
      let csvss₁ = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" csvs₁
      let csvmd :: Model = flatten $ csvToMatrix𝔻 $ list csvss₁
      csvs₂ ← read xsfn
      let csvss₂ = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" csvs₂
      let csvxs :: Matrix 𝔻 = csvToMatrix𝔻 $ list csvss₂
      csvs₃ ← read ysfn
      let csvss₃ = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" csvs₃
      let csvys :: Model = flatten $ csvToMatrix𝔻 $ list csvss₃
      let r = accuracy csvxs csvys csvmd
      write "out/acc.csv" (intercalate "," (map show𝕊 (list [(fst r),(snd r)])))
      pprint r
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
        do pprint τ ; flushOut
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
                  PFunV xs (ExPriv (Ex_C e₁)) γ → do
                    r' ← peval (assoc (zip xs as) ⩌ γ) e₁
                    case r' of
                      MatrixV m → do
                        pprint r'
                        write "out/model.csv" (intercalate "\n" (map (intercalate ",") (mapp (show𝕊 ∘ urv) (toLists m))))
                      _ → do pprint r'
                    pprint $ ppHeader "DONE" ; flushOut
                  _ → error "expected pλ at top level"
              _ → error "expected pλ at top level"
          _ → error "typechecking phase encountered an error"
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"
