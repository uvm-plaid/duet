module Main where

import Duet

initEnv ∷ 𝕏 ⇰ Type RNF
initEnv = dict 
  [ var "sign" ↦ ((Nil :* ℝT) :⊸: (ι 1 :* ℝT))
  -- , var "pmmap" ↦ (A@p ⊸⋆ B) ⊸∞ M[c,ℓ|m,n]A@(mnp) ⊸⋆ M[U,ℓ|m,n]B
  ]

parseMode ∷ 𝕊 → Ex_C PRIV_C PRIV_W
parseMode s = case list $ splitOn𝕊 "." s of
  _ :& "eps" :& "duet" :& Nil → Ex_C EPS_W
  _ :& "ed" :& "duet" :& Nil → Ex_C ED_W
  _ :& "renyi" :& "duet" :& Nil → Ex_C RENYI_W
  _ :& "tcdp" :& "duet" :& Nil → Ex_C TC_W
  _ :& "zcdp" :& "duet" :& Nil → Ex_C ZC_W
  _ → error "BAD FILE NAME"

parseMatrix𝔻  ∷ 𝕊 → ExMatrix 𝔻
parseMatrix𝔻 s = unID $ do
  traceM "PARSING MATRIX…"
  let dss ∷ 𝐼 (𝐼 𝔻)
      dss = map (map read𝕊 ∘ iter ∘ splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" s
      dss' ∷ 𝐿 (𝐿 𝔻)
      dss' = list $ map list dss
  xu dss' $ \ m → do
    traceM "DONE"
    return $ ExMatrix $ xvirt m

-- TODO: detect line endings or make an arg
buildArgs ∷ (Pretty r) ⇒ 𝐿 (Type r) → 𝐿 𝕊 → IO (𝐿 Val)
buildArgs Nil Nil = return Nil
buildArgs (τ:&τs) (a:&as) = case τ of
  -- TODO: currently the assumption is to read in RealVs
  (𝕄T _ _ _ (RexpME r τ)) → do
    s ← read a
    case parseMatrix𝔻 s of
      ExMatrix m →  do
        let m' = MatrixV $ ExMatrix $ map RealV m
        r ← buildArgs τs as
        return $ m' :& r
  (𝕄T _ _ _ (ConsME τ m)) → do
    csvs ← read a
    let csvss = map (splitOn𝕊 ",") $ filter (\x → not (isEmpty𝕊 x)) $ splitOn𝕊 "\n" csvs
    let csvm = csvToDF (list $ map list csvss) (schemaToTypes (ConsME τ m))
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
        e ← parseIO (pSkip tokSkip $ pFinal $ parSExp mode) $ stream ts
        do pprint $ ppHeader "TYPE CHECKING" ; flushOut
        let r = runSM dø initEnv dø $ inferSens e
        do pprint $ ppHeader "DONE" ; flushOut
        do pprint r ; flushOut
    "lr-accuracy":xsfn:ysfn:mdfn:[] → do
      do pprint $ ppHeader "ACCURACY TEST" ; flushOut
      sxs ← read xsfn
      sys ← read ysfn
      smd ← read mdfn
      case (parseMatrix𝔻 sxs,parseMatrix𝔻 sys,parseMatrix𝔻 smd) of
        (ExMatrix mxs,ExMatrix mys,ExMatrix mmd) → do
          let xs ∷ ExMatrix 𝔻
              xs = ExMatrix mxs
              ys ∷ DuetVector 𝔻
              ys = list mys
              md ∷ DuetVector 𝔻
              md = list mmd
              (r :* w) = accuracy xs ys md
          write "out/acc.csv" (intercalate "," (map show𝕊 (list [r,w])))
          pprint (r,w)
          pprint $ concat [ pretty (100.0 × dbl r / dbl (r+w)) , ppText "%" ]
    "run":fn:_ → do
      -- make this spit out concrete privacy costs based on the input
      do pprint $ ppHeader "READING" ; flushOut
      s ← read fn
      do pprint $ ppHeader "TOKENIZING" ; flushOut
      ts ← tokenizeIO tokDuet $ stream $ list $ tokens s
      do pprint $ ppHeader "PARSING" ; flushOut
      unpack_C (parseMode fn) $ \ mode → do
        e ← parseIO (pSkip tokSkip $ pFinal $ parSExp mode) $ stream ts
        do pprint $ ppHeader "TYPE CHECKING" ; flushOut
        let τ = runSM dø initEnv dø $ inferSens e
        do pprint τ ; flushOut
        do pprint $ ppHeader "RUNNING" ; flushOut
        let r = seval dø (extract e)
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
                        write "out/model.csv" (intercalate "\n" (map (intercalate ",") (mapp (show𝕊 ∘ urv) (toRows m))))
                      _ → do pprint r'
                    pprint $ ppHeader "DONE" ; flushOut
                  _ → error "expected pλ at top level"
              _ → error "expected pλ at top level"
          _ → error "typechecking phase encountered an error"
    _ → do
      pprint $ ppHeader "USAGE"
      out $ "duet parse <file>"
      out $ "duet check <file>"
