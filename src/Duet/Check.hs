{-# LANGUAGE PartialTypeSignatures #-}

module Duet.Check where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF
import Duet.Quantity

freeBvs :: Type r → 𝑃 𝕏
freeBvs (ℕˢT _) = pø
freeBvs (ℝˢT _) = pø
freeBvs ℕT = pø
freeBvs ℝT = pø
freeBvs (𝕀T _) = pø
freeBvs 𝔹T = pø
freeBvs 𝕊T = pø
freeBvs (𝔻𝔽T Nil) = pø
freeBvs (𝔻𝔽T (x :& xs)) = freeBrcrdvs x ∪ freeBvs (𝔻𝔽T xs)
freeBvs (BagT _ _ τ) = freeBvs τ
freeBvs (SetT τ) = freeBvs τ
freeBvs (RecordT Nil) = pø
freeBvs (RecordT (x :& xs)) = freeBrcrdvs x ∪ freeBvs (RecordT xs)
freeBvs (𝕄T _ _ _ me) = freeBmexp me
freeBvs (𝔻T τ) = freeBvs τ
freeBvs (τ₁ :+: τ₂) = freeBvs τ₁ ∪ freeBvs τ₂
freeBvs (τ₁ :×: τ₂) = freeBvs τ₁ ∪ freeBvs τ₂
freeBvs (τ₁ :&: τ₂) = freeBvs τ₁ ∪ freeBvs τ₂
freeBvs ((_ :* τ₁) :⊸: (_ :* τ₂)) = freeBvs τ₁ ∪ freeBvs τ₂
freeBvs (pargs :⊸⋆: τ) = freeBlpargvs pargs ∪ freeBvs τ
freeBvs (BoxedT σ τ) = keys σ ∪ freeBvs τ

freeBmexp :: (MExp r) → 𝑃 𝕏
freeBmexp me = case me of
  EmptyME → pø
  VarME _ → pø
  ConsME τ me₁ → freeBvs τ ∪ freeBmexp me₁
  AppendME me₁ me₂  → freeBmexp me₁ ∪ freeBmexp me₂
  RexpME _ τ → freeBvs τ

freeBrcrdvs :: 𝕊 ∧ Type r → 𝑃 𝕏
freeBrcrdvs (_ :* x) = freeBvs x

freeBlpargvs :: 𝐿 (𝕏 ∧ Kind) ∧ PArgs r → 𝑃 𝕏
freeBlpargvs (_ :* pargs) = unpackBpargs pargs

unpackBpargs :: PArgs r → 𝑃 𝕏
unpackBpargs e = case e of
  PArgs tps -> freeBpargs tps

freeBpargs :: 𝐿 (Type r ∧ Priv p r) → 𝑃 𝕏
freeBpargs Nil = pø
freeBpargs (x :& xs) = freeBpargs xs ∪ freeBparg x

freeBparg :: Type r ∧ Priv p r → 𝑃 𝕏
freeBparg (x :* _) = freeBvs x

getConsMAt :: (MExp r) → ℕ → (Type r)
getConsMAt EmptyME _ = error "matrix/dataframe column index error"
getConsMAt (ConsME τ _) 0 = τ
getConsMAt (ConsME _ m) n = (getConsMAt m (n-1))
getConsMAt _ _ = error "expected ConsME"

joinConsMs :: (MExp r) → (MExp r) → (MExp r)
joinConsMs (ConsME τ me₁) me₂ = (ConsME τ (joinConsMs me₁ me₂))
joinConsMs EmptyME me = me
joinConsMs _ _ = error "joinConsMs error: expected ConsME or EmptyME"

data TypeError = TypeError
  { typeErrorTerm ∷ Doc
  , typeErrorContext ∷ (𝕏 ⇰ Type RNF)
  , typeErrorType ∷ Type RNF
  , typeErrorExpected ∷ 𝐿 𝕊
  }
makePrettyRecord ''TypeError

data Context = Context
  { contextKind ∷ 𝕏 ⇰ Kind
  , contextType ∷ 𝕏 ⇰ Type RNF
  , contextMExp ∷ 𝕏 ⇰ MExp RNF
  }
makeLenses ''Context
makePrettyRecord ''Context

newtype SM (p ∷ PRIV) a = SM { unSM ∷ ReaderT Context (WriterT (𝕏 ⇰ Sens RNF) (ErrorT TypeError ID)) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (𝕏 ⇰ Sens RNF))

mkSM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → TypeError ∨ ((𝕏 ⇰ Sens RNF) ∧ a)) → SM p a
mkSM f = SM $ ReaderT $ \ (Context δ γ ᴍ) → WriterT $ ErrorT $ ID $ f δ γ ᴍ

runSM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → SM p a → TypeError ∨ ((𝕏 ⇰ Sens RNF) ∧ a)
runSM δ γ ᴍ = unID ∘ unErrorT ∘ unWriterT ∘ runReaderT (Context δ γ ᴍ) ∘ unSM

newtype PM (p ∷ PRIV) a = PM { unPM ∷ ReaderT Context (WriterT (𝕏 ⇰ Priv p RNF) (ErrorT TypeError ID)) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (𝕏 ⇰ Priv p RNF))

mkPM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → TypeError ∨ ((𝕏 ⇰ Priv p RNF) ∧ a)) → PM p a
mkPM f = PM $ ReaderT $ \ (Context δ γ ᴍ) → WriterT $ ErrorT $ ID $ f δ γ ᴍ

--      kind env   type env    expression   type error    sens costs     expressions' type
--         ⌄⌄         ⌄⌄           ⌄⌄         ⌄⌄             ⌄⌄            ⌄⌄
runPM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → PM p a → TypeError ∨ ((𝕏 ⇰ Priv p RNF) ∧ a)
runPM δ γ ᴍ = unID ∘ unErrorT ∘ unWriterT ∘ runReaderT (Context δ γ ᴍ) ∘ unPM

smFromPM ∷ PM p a → SM p a
smFromPM xM = mkSM $ \ δ γ ᴍ → mapInr (mapFst $ map $ Sens ∘ truncate Inf ∘ unPriv) $ runPM δ γ ᴍ xM

pmFromSM ∷ SM p a → PM p a
pmFromSM xM = mkPM $ \ δ γ ᴍ → mapInr (mapFst $ map $ Priv ∘ truncate Inf ∘ unSens) $ runSM δ γ ᴍ xM

mapPPM ∷ (Priv p₁ RNF → Priv p₂ RNF) → PM p₁ a → PM p₂ a
mapPPM f xM = mkPM $ \ δ γ ᴍ → mapInr (mapFst $ map f) $ runPM δ γ ᴍ xM

inferKind ∷ RExpPre → SM p Kind
inferKind = \case
  VarRE x → do
    δ ← askL contextKindL
    case δ ⋕? x of
      Some κ → return κ
      None → error "kinding failure: kind variable lookup error"
  NatRE _ → return $ ℕK
  NNRealRE _ → return $ ℝK
  MaxRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → error "TYPE ERROR"
  MinRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → error "TYPE ERROR"
  PlusRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → error "TYPE ERROR"
  TimesRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → error "TYPE ERROR"
  DivRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    case (κ₁,κ₂) of
      (ℝK,ℝK) → return ℝK
      _ → error "TYPE ERROR"
  RootRE e → do
    κ ← inferKind $ extract e
    case κ of
      ℝK → return ℝK
      _ → error "TYPE ERROR"
  LogRE e → do
    κ ← inferKind $ extract e
    case κ of
      ℝK → return ℝK
      _ → error "TYPE ERROR"
  MinusRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → error "TYPE ERROR"

-- this will be written monadically
checkType ∷ ∀ p. (PRIV_C p) ⇒ Type RExp → SM p 𝔹
checkType τA = case τA of
  ℕˢT η → do
    κ ← inferKind $ extract η
    return $ κ ⊑ ℕK
  ℝˢT η → do
    κ ← inferKind $ extract η
    return $ κ ⊑ ℝK
  ℕT → return True
  ℝT → return True
  𝕀T η → do
    κ ← inferKind $ extract η
    return $ κ ⊑ ℕK
  𝔹T → return True
  𝕊T → return True
  𝔻𝔽T _ → undefined
  BagT _ℓ _c τ → checkType τ
  SetT τ → checkType τ
  RecordT _ → undefined
  𝕄T _ℓ _c rows me → do
    case (rows, me) of
      ((RexpRT r₁), (RexpME r₂ τ)) → do
        κ₁ ← inferKind $ extract r₁
        κ₂ ← inferKind $ extract r₂
        a ← checkType τ
        return $ and [a,κ₁ ⊑ ℕK,κ₂ ⊑ ℕK]
      ((RexpRT r), _) → do
        κ ← inferKind $ extract r
        return $ κ ⊑ ℕK
      _ → return True
  𝔻T τ → checkType τ
  τ₁ :+: τ₂ → do
    a ← checkType τ₁
    b ← checkType τ₂
    return $ a ⩓ b
  τ₁ :×: τ₂ → do
    a ← checkType τ₁
    b ← checkType τ₂
    return $ a ⩓ b
  τ₁ :&: τ₂ → do
    a ← checkType τ₁
    b ← checkType τ₂
    return $ a ⩓ b
  (ακs :* τ₁) :⊸: (s :* τ₂) → do
    a ← checkType τ₁
    b ← checkType τ₂
    let c = a ⩓ b
    case s of
      Sens Inf → return $ True ⩓ c
      Sens (Quantity r) → do
        κ ← inferKind $ extract r
        return $ (⩓) c $ κ ⊑ ℝK
      _ → return False
  (ακs :* PArgs (τps ∷ 𝐿 (Type RExp ∧ Priv p' RExp))) :⊸⋆: τ → do
   mapEnvL contextKindL (\ δ → assoc ακs ⩌ δ) $ do
     _ :* _a ← hijack $  checkType τ
     map and $ mapM checkTypeP τps
  BoxedT _σ τ → checkType τ

checkTypeP ∷ ∀ p₁ p₂. (PRIV_C p₁) ⇒ (Type RExp ∧ Priv p₂ RExp) → SM p₁ 𝔹
checkTypeP (τ :* p) = do
  a ← checkType τ
  b ← checkKindP p
  case (a ⩓ b) of
    False → throw (error "kinding error" ∷ TypeError)
    True → return $ True

checkKindP :: ∀ p₁ p₂. Priv p₂ RExp → SM p₁ 𝔹
checkKindP p = case p of
  Priv (Quantity (EDPriv ε δ)) → do
    κ₁ ← inferKind $ extract ε
    κ₂ ← inferKind $ extract δ
    return $ and [κ₁ ⊑ ℝK,κ₂ ⊑ ℝK]
  -- TODO: account for other privacy variants
  _ → return True

inferSens ∷ (PRIV_C p) ⇒ SExpSource p → SM p (Type RNF)
inferSens eA = case extract eA of
  ℕˢSE n → return $ ℕˢT $ ι n
  ℝˢSE d → return $ ℝˢT $ ι d
  DynSE e → do
    τ ← inferSens e
    case τ of
      ℕˢT _η → return ℕT
      ℝˢT _η → return ℝT
      𝕀T _η → return ℕT
      _ → undefined -- TypeError
  ℕSE _n → return $ ℕT
  ℝSE _d → return $ ℝT
  RealSE e → do
    τ ← inferSens e
    case τ of
      ℕT → return ℝT
      ℕˢT η → return $ ℝˢT η
      _ → undefined -- TypeError
  MaxSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ ⊔ η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ ⊔ η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ ⊔ η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  MinSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ ⊓ η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ ⊓ η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ ⊓ η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  PlusSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ + η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ + η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ + η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → error $ concat
            [ "Plus error: "
            , pprender $ (τ₁ :* τ₂)
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  TimesSE e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℕˢT $ η₁ × η₂
      (ℝˢT η₁,ℝˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℝˢT $ η₁ × η₂
      (𝕀T η₁,𝕀T η₂) →   do tell $ σ₁ ⧺ σ₂ ; return $ 𝕀T $ η₁ × η₂
      (ℕˢT η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵  σ₂
        return ℕT
      (ℕT,ℕˢT η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      (ℝˢT η₁,ℝT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return ℝT
      (ℝT,ℝˢT η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℝT
      (𝕀T η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return ℕT
      (ℕT,𝕀T η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      (ℕT,ℕT) → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (ℝT,ℝT) → do tell $ σ₁ ⧺ σ₂ ; return ℝT
      (𝔻T ℝT,𝔻T ℝT) → do tell $ σ₁ ⧺ σ₂ ; return $ 𝔻T ℝT
      _ → error $ "Times error: " ⧺ (pprender $ (τ₁ :* τ₂))
  DivSE e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (ℝˢT η₁,ℝˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℝˢT $ η₁ / η₂
      (ℝˢT _η₁,ℝT) → do
        tell $ σ₁ ⧺ top ⨵ σ₂
        return $ ℝT
      (ℝT,ℝˢT η₂) → do
        tell $ ι (one / η₂) ⨵ σ₁ ⧺ σ₂
        return $ ℝT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  RootSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ rootRNF η
      ℝT → do tell $ top ⨵ σ ; return ℝT
      𝔻T ℝT → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  LogSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ logRNF η
      ℝT → do tell $ top ⨵ σ ; return ℝT
      𝔻T ℝT → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  ModSE e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT _η₁,ℕˢT _η₂) → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (𝕀T _η₁,𝕀T _η₂)   → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (ℕˢT η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return ℕT
      (ℕT,ℕˢT η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      -- TODO: check that this is ok
      (𝕀T η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return $ 𝕀T η₁
      (ℕT,𝕀T η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      (ℕT,ℕT) → do tell $ top ⨵ σ₁ ⧺ σ₂ ; return ℕT
      _ → error $ "Mod error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeError
  MinusSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℝˢT _η₁,ℝˢT _η₂) → return ℝT
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → error $ "Minus error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeError
  MCreateSE ℓ e₁ e₂ x₁ x₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT ηₘ,ℕˢT ηₙ) → do
        σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ 𝕀T ηₘ,x₂ ↦ 𝕀T ηₙ] ⩌ γ) $ inferSens e₃
        let σ₃' = without (pow [x₁,x₂]) σ₃
        tell $ ι (ηₘ × ηₙ) ⨵ σ₃'
        return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME ηₙ τ₃)
      _ → undefined -- TypeError
  -- CSVtoMatrixSE f τ → do
  --   case map normalizeRExp (extract τ) of
  --     (𝕄T _ℓ _c StarRT (RexpME r τ₁')) → return (𝕄T _ℓ _c StarRT (RexpME r τ₁'))
  --     _ → error $ "CSVtoMatrixSE error: " ⧺ (pprender $ (f :* τ)) -- TypeError
  MIndexSE e₁ e₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    case (τ₁,τ₂,τ₃) of
      (𝕄T _ℓ _c (RexpRT ηₘ) (RexpME r τ),𝕀T ηₘ',𝕀T ηₙ') | (ηₘ' ≤ ηₘ) ⩓ (ηₙ' ≤ r) → return τ
      -- dataframe etc.
      (𝕄T _ℓ _c (RexpRT _ηₘ) (ConsME τ m), _ηₘ', ℕˢT (NatRNF ηₙ')) → return $ getConsMAt (ConsME τ m) ηₙ'
      (𝕄T _ℓ _c StarRT (RexpME r τ),𝕀T _ηₘ',𝕀T ηₙ') | (ηₙ' ≤ r) → return τ
      (𝕄T _ℓ _c StarRT (ConsME τ m), _ηₘ',ℕˢT (NatRNF ηₙ')) → return $ getConsMAt (ConsME τ m) ηₙ'
      -- had error: duet: ⟨⟨𝕄 [L∞ U|1,n] ℝ,ℕ⟩,ℕ⟩
      _ → error $ "Index error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃)) -- TypeError
  MUpdateSE e₁ e₂ e₃ e₄ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    τ₄ ← inferSens e₄
    case (τ₁,τ₂,τ₃,τ₄) of
      -- TODO: why does this check fail for FW?
      (𝕄T ℓ c ηₘ (RexpME r τ),𝕀T _ηₘ',𝕀T ηₙ',τ') | {-(ηₘ' ≤ ηₘ) ⩓ -}(ηₙ' ≤ r) ⩓ (τ ≡ τ') →
                                          return $ 𝕄T ℓ c ηₘ (RexpME r τ)
      _ → error $ "Update error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄)) -- TypeError
  MRowsSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      𝕄T _ℓ _c (RexpRT ηₘ) _ηₙ → return $ ℕˢT ηₘ
      𝕄T _ℓ _c StarRT _ηₙ → do
        tell σ
        return $ ℕT
      _ → undefined -- TypeSource Error
  MColsSE e → do
    _ :* τ ← hijack $ inferSens e
    case τ of
      𝕄T _ℓ _c _ηₘ (RexpME r _τ') → return $ ℕˢT r
      _ → undefined -- TypeSource Error
  MClipSE ℓ e → do
    τ ← inferSens e
    case τ of
      𝕄T ℓ' _c ηₘ (RexpME r τ') | τ' ≡ (𝔻T ℝT) → return $ 𝕄T ℓ' (NormClip ℓ) ηₘ (RexpME r τ')
      𝕄T ℓ' _c ηₘ (RexpME r τ') | τ' ≡ (ℝT) → return $ 𝕄T ℓ' (NormClip ℓ) ηₘ (RexpME r (𝔻T ℝT))
      _ → undefined -- TypeSource Error
  MConvertSE e → do
    τ ← inferSens e
    case τ of
      𝕄T _ℓ (NormClip ℓ) ηₘ (RexpME r τ') | τ' ≡ 𝔻T ℝT → return $ 𝕄T ℓ UClip ηₘ (RexpME r ℝT)
      --QUESTION: is this ok? - CA
      𝕄T ℓ _c ηₘ (RexpME r τ') | τ' ≡ 𝔻T ℝT → return $ 𝕄T ℓ UClip ηₘ (RexpME r ℝT)
      _ → undefined -- TypeSource Error
  MLipGradSE _g e₁ e₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    tell $ top ⨵ σ₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    σ₃ :* τ₃ ← hijack $ inferSens e₃
    case (τ₁,τ₂,τ₃) of
      -- _ → error "TODO"
      (𝕄T _ℓ₁ _c₁ ( RexpRT rₘ₁ ) (RexpME r₁ τ₁'),𝕄T _ℓ₂ (NormClip ℓ) ( RexpRT rₘ₂ ) (RexpME r₂ τ₂'),𝕄T _ℓ₃ _c₃ ( RexpRT rₘ₃ ) (RexpME r₃ τ₃'))
        | meets
          [ τ₁' ≡ ℝT
          , τ₂' ≡ 𝔻T ℝT
          , τ₃' ≡ 𝔻T ℝT
          , rₘ₁ ≡ one
          , r₃ ≡ one
          , r₁ ≡ r₂
          , rₘ₂ ≡ rₘ₃
          ]
        → do tell $ ι (ι 1 / rₘ₂) ⨵ (σ₂ ⧺ σ₃)
             return $ 𝕄T ℓ UClip (RexpRT one) (RexpME r₁ ℝT)
      _ → error $ "Lipschitz grad error: " ⧺ (pprender (τ₁ :* τ₂ :* τ₃))
  MUnbGradSE _g e₁ e₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    tell $ top ⨵ σ₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    σ₃ :* τ₃ ← hijack $ inferSens e₃
    case (τ₁,τ₂,τ₃) of
      -- _ → error "TODO"
      (𝕄T _ℓ₁ _c₁ ( RexpRT rₘ₁ ) (RexpME r₁ τ₁'),𝕄T _ℓ₂ _c₂ ( RexpRT rₘ₂ ) (RexpME r₂ τ₂'),𝕄T _ℓ₃ _c₃ ( RexpRT rₘ₃ ) (RexpME r₃ τ₃'))
        | meets
          [ τ₁' ≡ ℝT
          , τ₂' ≡ 𝔻T ℝT
          , τ₃' ≡ 𝔻T ℝT
          , rₘ₁ ≡ one
          , r₃ ≡ one
          , r₁ ≡ r₂
          , rₘ₂ ≡ rₘ₃
          ]
        → do tell $ ι (ι 1 / rₘ₂) ⨵ (σ₂ ⧺ σ₃)
             return $ 𝕄T LInf UClip (RexpRT one) (RexpME r₁ $ 𝔻T ℝT)
      _ → undefined -- TypeSource Error
  MMapSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ _c (RexpRT ηₘ) (RexpME r τ₁') → do
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ ι (ηₘ × r) ⨵ σ₂'
        return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME r τ₂)
      _  → undefined -- TypeSource Error
  MTimesSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (𝕄T ℓ c (RexpRT η₁) (RexpME r₁ τ₁'),𝕄T _ _ (RexpRT η₂) (RexpME r₂ τ₂'))
        | (τ₁' ≡ τ₂') ⩓ (r₁ ≡ η₂) → do
          return $ 𝕄T ℓ c (RexpRT η₁) (RexpME r₂ τ₁')
      _  → error $ "matrix multiplication error"
  MTransposeSE e₁ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ _c (RexpRT η₁) (RexpME r₁ τ₁') → do
        tell $ ι η₁ ⨵ σ₁
        return $ 𝕄T ℓ UClip (RexpRT r₁) (RexpME η₁ τ₁')
      _  → error $ "matrix transpose error"
  JoinSE e₁ e₂ e₃ e₄ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    τ₄ ← inferSens e₄
    case (τ₁,τ₂,τ₃,τ₄) of
      (𝕄T _ _ _ me₁, ℕˢT (NatRNF η₁),𝕄T _ _ _ me₂, ℕˢT (NatRNF η₂))
        | (getConsMAt me₁ η₁) ≡ (getConsMAt me₂ η₂) → do
          return $ 𝕄T LInf UClip StarRT (joinConsMs me₁ me₂)
      _  → error $ "join₁ failed" ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄))
  BMapSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      BagT ℓ _c τ₁' → do
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ σ₂'
        return $ BagT ℓ UClip τ₂
      _  → undefined -- TypeSource Error
  MMap2SE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (𝕄T ℓ₁ _c₁ (RexpRT r₁) (RexpME r₂ τ₁'),𝕄T ℓ₂ _c₂ (RexpRT r₁') (RexpME r₂' τ₂'))
        | meets
          [ ℓ₁ ≡ ℓ₂
          , r₁ ≡ r₁'
          , r₂ ≡ r₂'
          , τ₁' ≡ τ₂'
          ]
        → do σ₃ :* τ₃ ←
               hijack $
               mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁',x₂ ↦ τ₂'] ⩌ γ) $
               inferSens e₃
             let (ς₁ :* σ₃') = ifNone (zero :* σ₃) $ dview x₁ σ₃
                 (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
             tell $ ς₁ ⨵ σ₁
             tell $ ς₂ ⨵ σ₂
             tell $ ι (r₁ × r₂) ⨵ σ₃''
             return $ 𝕄T ℓ₁ UClip (RexpRT r₁) (RexpME r₂ τ₃)
      _ → error $ "Map2 error: " ⧺ (pprender $ (τ₁ :* τ₂))
  BMap2SE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (BagT ℓ₁ _c₁ τ₁',BagT ℓ₂ _c₂ τ₂')
        | ℓ₁ ≡ ℓ₂
        → do σ₃ :* τ₃ ←
               hijack $
               mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁',x₂ ↦ τ₂'] ⩌ γ) $
               inferSens e₃
             let (ς₁ :* σ₃') = ifNone (zero :* σ₃) $ dview x₁ σ₃
                 (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
             tell $ ς₁ ⨵ σ₁
             tell $ ς₂ ⨵ σ₂
             tell $ σ₃''
             return $ BagT ℓ₁ UClip τ₃
      _ → error $ "Map2 error: " ⧺ (pprender $ (τ₁ :* τ₂))
  VarSE x → do
    γ ← askL contextTypeL
    case γ ⋕? x of
      None → error $ concat
            [ "Variable lookup error: failed to find " ⧺ (pprender x) ⧺ " in the environment:\n"
            , pprender γ
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
      Some τ → do
        tell (x ↦ ι 1.0)
        return τ
  LetSE x e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferSens e₂
    let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
    let fvs = freeBvs τ₂
    let isClosed = (fvs ∩ single𝑃 x) ≡ pø
    case isClosed of
      False → error $ "Let type/scoping error in return expression of type: " ⧺ (pprender τ₂)
      True → do
        tell $ ς ⨵ σ₁
        tell σ₂'
        return τ₂
  SFunSE ακs x τ e → do
    mapEnvL contextKindL (\ δ → assoc ακs ⩌ δ) $ do
      a ← checkType $ extract τ
      when (not a) $ throw (error "kinding error in sfun" ∷ TypeError)
      let τ' = map normalizeRExp $ extract τ
      σ :* τ'' ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ') ⩌ γ) $ inferSens e
      let (ς :* σ') = ifNone (zero :* σ) $ dview x σ
      let fvs = freeBvs τ''
      let isClosed = (fvs ∩ single𝑃 x) ≡ pø
      case isClosed of
        False → error $ "Lambda type/scoping error in return expression of type: " ⧺ (pprender τ'')
        True → do
          tell σ'
          return $ (ακs :* τ') :⊸: (ς :* τ'')
  -- AppPE e ηs as → do
  --   let η's = map normalizeRExp ηs
  --   τ ← pmFromSM $ inferSens e
  --   ηκs ← pmFromSM $ mapM (inferKind ∘ extract) ηs
  --   aστs ← pmFromSM $ mapM (hijack ∘ inferSens) as
  --   let aσs = map fst aστs
  --   let aτs = map snd aστs
  --   case τ of
  --     ((ακs :* PArgs (τps ∷ 𝐿 (_ ∧ Priv p' RNF))) :⊸⋆: τ₁)
  --       | (joins (values (joins aσs)) ⊑ ι 1)
  --       ⩓ (count ηs ≡ count ακs)
  --       ⩓ (count as ≡ count τps)
  --       → case eqPRIV (priv @ p) (priv @ p') of
  --           None → error "privacy variants dont match"
  --           Some Refl → do
  --             let fαs = map fst ακs
  --                 fκs = map snd ακs
  --                 αηs = zip fαs η's
  --                 subT ∷ Type RNF → Type RNF
  --                 subT τ' = fold τ' (\ (α :* η) τ'' → substType α η τ'') αηs
  --                 subP ∷ Priv p' RNF → Priv p' RNF
  --                 subP p = fold p (\ (α :* η) p' → map (substRNF α η) p') αηs
  --                 τps' = mapOn τps $ \ (τ' :* p) → (subT τ' :* subP p)
  --                 τs' = map fst τps'
  --                 ps' = map snd τps'
  --             case (ηκs ≡ fκs) ⩓ (aτs ≡ τs') of
  --               True → do
  --                 eachWith (zip aσs ps') $ \ (σ :* p) →
  --                   tell $ map (Priv ∘ truncate (unPriv p) ∘ unSens) σ
  --                 return τ₁
  --               False → error $ "type error in AppPE" ⧺ show𝕊 (ηκs,fκs,aτs,τs')
  --     _ → error $ "AppPE expected a function instead of" ⧺ pprender τ
  AppSE e₁ ηs e₂ → do
    let η's = map normalizeRExp ηs
    τ₁ ← inferSens e₁
    ηκs ← mapM (inferKind ∘ extract) ηs
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case τ₁ of
      (ακs :* τ₁₁) :⊸: (ς :* τ₁₂) → do
        let fαs = map fst ακs
            fκs = map snd ακs
            αηs = zip fαs η's
            subT ∷ Type RNF → Type RNF
            subT τ' = fold τ' (\ (α :* η) τ'' → substType α η τ'') αηs
            subS ∷ Sens RNF → Sens RNF
            subS p = fold p (\ (α :* η) p' → map (substRNF α η) p') αηs
            τ₁₁' = subT τ₁₁
            ς' = subS ς
        case (ηκs ≡ fκs) ⩓ (τ₂ ≡ τ₁₁') of
          True → do
            tell $ ς' ⨵ σ₂
            return $ subT τ₁₂
          False → error $ concat
            [ "AppSE error: "
            , pprender (τ₂ :* τ₁₁')
            , "\n"
            , pprender (ηκs :* fκs)
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
      _ → error $ "Application error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeSource Error
  PFunSE ακs xτs e → do
    let xτs' = map (mapSnd (map normalizeRExp ∘ extract)) xτs
        xs = map fst xτs
    mapEnvL contextKindL (\ δ → assoc ακs ⩌ δ) $ do
      σ :* τ ←
        smFromPM
        $ hijack
        $ mapEnvL contextTypeL (\ γ → assoc xτs' ⩌ γ)
        $ inferPriv e
      a ← map and $ mapM checkType $ map (extract ∘ snd) xτs
      when (not a) $ throw (error "kinding error in pfun" ∷ TypeError)
      let fvs = freeBvs τ
      let isClosed = (fvs ∩ pow xs) ≡ pø
      case isClosed of
        False → error $ "Lambda type/scoping error in return expression of type: " ⧺ (pprender τ)
        True → do
          tell $ map (Sens ∘ truncate Inf ∘ unPriv) $ without (pow xs) σ
          let τps = mapOn xτs' $ \ (x :* τ') → τ' :* ifNone null (σ ⋕? x)
          return $ (ακs :* PArgs τps) :⊸⋆: τ
  SetSE es → do
    -- homogeneity check
    l ← mapM (hijack ∘ inferSens) es
    let hm = 1 ≡ (count $ uniques $ map snd l)
    case hm of
      False → error "Set expression is not homogenous/unique"
      True → do
        case es of
          (x :& _xs) → do
            τ ← inferSens x
            return $ SetT τ
          _ → error $ "typing error in SetSE"
  UnionAllSE e → do
    τ ← inferSens e
    case τ of
      (SetT (SetT τ')) → return (SetT τ')
      _ → error $ "UnionAllSE expected a set of sets as its argument" ⧺ pprender τ
  MemberSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (τ₁', SetT τ₂') | τ₁' ≡ τ₂' → return 𝔹T
      _ → error $ "MemberSE error: " ⧺ (pprender (τ₁, τ₂))
  TupSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    return $ τ₁ :×: τ₂
  UntupSE x₁ x₂ e₁ e₂ → do
    σ₁ :* τₜ ← hijack $ inferSens e₁
    case τₜ of
      (τ₁ :×: τ₂) → do
        σ₂ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → (x₁ ↦ τ₁) ⩌ (x₂ ↦ τ₂) ⩌ γ) $ inferSens e₂
        let (ς₁ :* σ₂') = ifNone (zero :* σ₂) $ dview x₁ σ₂
            (ς₂ :* σ₂'') = ifNone (zero :* σ₂') $ dview x₂ σ₂'
        tell $ (ς₁ ⊔ ς₂) ⨵ σ₁
        tell σ₂''
        return τ₃
      _ → error $ "Untup error: " ⧺ (pprender $ τₜ)
  IdxSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℕˢT η → do tell σ ; return $ 𝕀T η
      _ → undefined -- TypeError
  RecordColSE a₁ e → do
    τ ← inferSens e
    case τ of
      RecordT as → do
        -- TODO: I (Joe) am not a wizard at this
        let f ∷ (𝕊 ∧ Type RNF) → 𝑂 (Type RNF) → 𝑂 (Type RNF) = \ p acc →
               case p of
                 (a₂ :* v) | a₁ ≡ a₂ → Some v
                 _ → acc
            τₐ ∷ 𝑂 (Type RNF) = fold None f as
        case τₐ of
          Some τ' → return τ'
          _ → error $ "RecordColSE attribute not found: " ⧺ (pprender (τ, τₐ))
      _ → error $ "RecordColSE error: " ⧺ (pprender τ)
  EqualsSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case τ₁ ≡ τ₂ of
      True → return 𝔹T
      _ → error $ "Equals error: " ⧺ (pprender (τ₁, τ₂))
  TrueSE → return 𝔹T
  FalseSE → return 𝔹T
  DFPartitionSE e₁ a e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    τ₂ ← inferSens e₂
    -- TODO: check that τ₁ and τ₂ overlap on some subset of their schemas
    case (τ₁, τ₂) of
      (BagT ℓ c (RecordT as), SetT τ₃) → do
        -- TODO: helper?
        let f ∷ (𝕊 ∧ Type RNF) → 𝑂 (Type RNF) → 𝑂 (Type RNF) = \ p acc →
               case p of
                 (a₂ :* v) | a ≡ a₂ → Some v
                 _ → acc
            τₐ ∷ 𝑂 (Type RNF) = fold None f as
        case τₐ of
          Some τ' → do
            case τ' ≡ τ₃ of
              False → error $ "Partition attribute type mismatch: " ⧺ (pprender (τ₁, τ₃))
              True → do
                tell σ₁
                -- TODO: make sure ℓ and c are right
                return $ BagT ℓ c τ₁
          _ → error $ "Partition attribute not found: " ⧺ (pprender (τ₁, τₐ))
      _ → error $ "Partition error: " ⧺ (pprender (τ₁, τ₂))
  BoxSE e → do
    σ :* τ ← hijack $ inferSens e
    return (BoxedT σ τ)
  UnboxSE e → do
    τ₁ ← inferSens e
    case τ₁ of
      BoxedT σ τ₂ → do
        tell σ
        return τ₂
      _ → error $ "Cannot unbox type: " ⧺ (pprender τ₁)
  ClipSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      𝔻T τ₁ → do
        tell σ
        return τ₁
      _ → error $ "Cannot clip type: " ⧺ (pprender τ)
  ConvSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      𝔻T τ₁ → do
        tell $ map (Sens ∘ truncate Inf ∘ unSens) σ
        return τ₁
      _ → error $ "Cannot conv type: " ⧺ (pprender τ)
  DiscSE e → do
    σ :* τ ← hijack $ inferSens e
    tell $ map (Sens ∘ truncate (Quantity (NatRNF 1)) ∘ unSens) σ
    return $ 𝔻T τ
  CountSE e → do
    τ ← inferSens e
    case τ of
      𝕄T ℓ c (RexpRT ηₘ) (RexpME r τ₁') → do
        return $ ℝT
  LoopSE e₂ e₃ x₁ x₂ e₄ → do
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    σ₄ :* τ₄ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) $ inferSens e₄
    let σ₄' = without (pow [x₁,x₂]) σ₄
    case τ₂ of
      ℕˢT ηₙ | τ₄ ≡ τ₃ → do
        -- tell $ map (Sens ∘ truncate Inf ∘ unSens) σ₄ -- wrong - want to multiply by ηₙ
        tell $ (Sens (Quantity ηₙ)) ⨵ σ₄'
        return τ₃
      _ → error $ concat
            [ "Loop error: "
            , (pprender $ (τ₂ :* τ₃ :* τ₄ :* σ₄))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MZipSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁, τ₂) of
      (𝕄T ℓ₁ c₁ r₁ s₁, 𝕄T ℓ₂ c₂ r₂ s₂) | r₁ ≡ r₂ → do
        let m₁ = 𝕄T ℓ₁ c₁ (RexpRT one) s₁
            m₂ = 𝕄T ℓ₂ c₂ (RexpRT one) s₂
        return $ 𝕄T LInf UClip r₁ $ ConsME (m₁ :×: m₂) EmptyME
      _ → error $ concat
            [ "Zip error: "
            , (pprender $ (τ₁ :* τ₂))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  ChunksSE e₁ e₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    case (τ₁, τ₂, τ₃) of
      (ℕˢT ηb, 𝕄T ℓ₁ c₁ r₁₁ s₁, 𝕄T ℓ₂ c₂ r₁₂ s₂) | r₁₁ ≡ r₁₂ → do
        let mt₁ = 𝕄T ℓ₁ c₁ (RexpRT ηb) s₁
            mt₂ = 𝕄T ℓ₂ c₂ (RexpRT ηb) s₂
            s   = ConsME (mt₁ :×: mt₂) EmptyME
        return $ 𝕄T LInf UClip (RexpRT ηb) s -- TODO: ηb is wrong here, but doesn't affect sens.
      _ → error $ concat
            [ "Chunks error: "
            , (pprender $ (τ₁ :* τ₂ :* τ₃))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MFilterSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ c r s → do
        let m = 𝕄T ℓ c (RexpRT one) s
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ m) ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ map (Sens ∘ truncate Inf ∘ unSens) σ₂'
        case τ₂ of
          𝔹T → return $ 𝕄T ℓ c StarRT s
          _  → error $ "MFilter error: " ⧺ (pprender (τ₁, τ₂))
      _ → error $ concat
            [ "MFilter error: "
            , (pprender $ (τ₁))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MMapColSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ c (RexpRT ηₘ) (RexpME r τ₁') → do
        let m = 𝕄T ℓ c (RexpRT ηₘ) (RexpME one τ₁')
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ m) ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ (ι r × ς) ⨵ σ₁
        tell $ ι (ηₘ × r) ⨵ σ₂'
        case τ₂ of
          𝕄T ℓ₂ c₂ (RexpRT ηₘ₂) (RexpME one τ₂') →
            return $ 𝕄T ℓ₂ c₂ (RexpRT ηₘ₂) (RexpME r τ₂')
          _ → return $ 𝕄T LInf UClip (RexpRT one) (RexpME r τ₂)
--          _ → error $ pprender τ₂
      _  → undefined -- TypeSource Error


  MFoldSE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case τ₂ of
      𝕄T ℓ c (RexpRT r₁) s → do
        let τᵢ = 𝕄T ℓ c (RexpRT one) s
        σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁,x₂ ↦ τᵢ] ⩌ γ) $
                     inferSens e₃
        let (_ :* σ₃')  = ifNone (zero :* σ₃)  $ dview x₁ σ₃
            (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
        tell $ map (Sens ∘ truncate Inf ∘ unSens) σ₁
        tell $ ς₂ ⨵ σ₂
        tell $ ι r₁ ⨵ σ₃''
        return τ₃
      _ → error $ concat
            [ "MFold error: "
            , (pprender $ (τ₁ :* τ₂))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  _ → error $ concat
        [ "inferSens unknown expression type: "
        , "\n"
        , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
        ]

isRealMExp ∷ MExp RNF → PM p 𝔹
isRealMExp me = case me of
  EmptyME → do
    return False
  VarME x → do
    ᴍ ← askL contextMExpL
    case ᴍ ⋕? x of
      None → error $ fromString (show x) -- TypeSource Error
      Some m → do
        isRealMExp $ m
  ConsME τ me₁ → do
    let b = isRealType τ
    a ← isRealMExp $ me₁
    return $ a ⩓ b
  AppendME me₁ me₂ → do
    a ← isRealMExp $ me₁
    b ← isRealMExp $ me₂
    return $ a ⩓ b
  RexpME _r τ → return $ isRealType τ

isRealType :: (Type r) → 𝔹
isRealType (ℝˢT _r) = True
isRealType (ℝT) = True
isRealType _ = False

matchArgPrivs ∷ 𝐿 (𝕏 ⇰ Sens RNF) → 𝐿 (Priv p RNF) → 𝐿 (𝕏 ⇰ Priv p RNF)
matchArgPrivs xss xps = list $ zipWith (↦) (fold Nil (⧺) (map (list ∘ uniques ∘ keys) xss)) xps

-- TODO: define and use these in place of truncate

truncateSS ∷ Sens r → Sens r → Sens r
truncateSS = undefined

truncatePP ∷ Priv p r → Priv p r → Priv p r
truncatePP = undefined

truncateSP ∷ Sens r → Priv p r → Priv p r
truncateSP = undefined

inferPriv ∷ ∀ p. (PRIV_C p) ⇒ PExpSource p → PM p (Type RNF)
inferPriv eA = case extract eA of
  ReturnPE e → pmFromSM $ inferSens e
  BindPE x e₁ e₂ → do
    τ₁ ← inferPriv e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferPriv e₂
    tell $ delete x σ₂
    return τ₂
  MMapPE e₁ x e₂ → do
    σ₁ :* τ₁ ← pmFromSM $ hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ _c (RexpRT ηₘ) (RexpME r τ₁') | (joins (values σ₁) ⊑ ι 1) → do
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferPriv e₂
        let (p :* σ₂') = ifNone (bot :* σ₂) $ dview x σ₂
        tell $ map Priv $ mapp (iteratePr (ηₘ × r)) $ (map unPriv σ₂)
        case (ιview @ (Pr p RNF) p) of
          (Some p') → do
            tell $ map (Priv ∘ truncate (Quantity (iteratePr (ηₘ × r) p')) ∘ unSens) σ₁
            return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME r τ₂)
          _ → do
            tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₁
            return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME r τ₂)
      _  → undefined -- TypeSource Error
  AppPE e ηs as → do
    let η's = map normalizeRExp ηs
    τ ← pmFromSM $ inferSens e
    ηκs ← pmFromSM $ mapM (inferKind ∘ extract) ηs
    aστs ← pmFromSM $ mapM (hijack ∘ inferSens) as
    let aσs = map fst aστs
    let aτs = map snd aστs
    case τ of
      ((ακs :* PArgs (τps ∷ 𝐿 (_ ∧ Priv p' RNF))) :⊸⋆: τ₁)
        | (joins (values (joins aσs)) ⊑ ι 1)
        ⩓ (count ηs ≡ count ακs)
        ⩓ (count as ≡ count τps)
        → case eqPRIV (priv @ p) (priv @ p') of
            None → error "privacy variants dont match"
            Some Refl → do
              let fαs = map fst ακs
                  fκs = map snd ακs
                  αηs = zip fαs η's
                  subT ∷ Type RNF → Type RNF
                  subT τ' = fold τ' (\ (α :* η) τ'' → substType α η τ'') αηs
                  subP ∷ Priv p' RNF → Priv p' RNF
                  subP p = fold p (\ (α :* η) p' → map (substRNF α η) p') αηs
                  τps' = mapOn τps $ \ (τ' :* p) → (subT τ' :* subP p)
                  τs' = map fst τps'
                  ps' = map snd τps'
              case (ηκs ≡ fκs) ⩓ (aτs ≡ τs') of
                True → do
                  eachWith (zip aσs ps') $ \ (σ :* p) →
                    tell $ map (Priv ∘ truncate (unPriv p) ∘ unSens) σ
                  return $ subT τ₁
                False → error $ concat
                  [ "type error in AppPE\n"
                  , concat $ inbetween "\n"
                      [ show𝕊 (ηκs ≡ fκs)
                      , show𝕊 (aτs ≡ τs')
                      , show𝕊 ηκs
                      , show𝕊 fκs
                      , show𝕊 aτs
                      , show𝕊 τs'
                      ]
                  ]
      _ → error $ "AppPE expected a function instead of" ⧺ pprender τ
  IfPE e₁ e₂ e₃ → do
    τ₁ ← pmFromSM $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferPriv e₂
    σ₃ :* τ₃ ← hijack $ inferPriv e₃
    case (τ₂ ≡ τ₃) of
      False → error $ "IfPE type mismatch" ⧺ (pprender (τ₂,τ₃))
      True → case τ₁ of
        𝔹T → do
          tell (σ₃ ⊔ σ₂)
          return τ₂
        _ → error $ "IfPE expected a boolean in the test position" ⧺ pprender τ₁
  EDLoopPE e₁ e₂ e₃ xs x₁ x₂ e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) $ inferPriv e₄
    let σ₄' = without (pow [x₁,x₂]) σ₄
    let σ₄Keep = restrict xs' σ₄'
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄'
    case (τ₁,τ₂,σ₄KeepMax) of
      (ℝˢT ηᵟ',ℕˢT ηₙ,Priv (Quantity (EDPriv ηᵋ ηᵟ))) | τ₄ ≡ τ₃ → do
        let ε = ι 2 × ηᵋ × root (ι 2 × ηₙ × log (ι 1 / ηᵟ'))
            δ = ηᵟ' + ηₙ × ηᵟ
        tell $ map (Priv ∘ truncate (Quantity $ EDPriv ε δ) ∘ unPriv) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unPriv) σ₄Toss
        return τ₃
      _ → error $ "EDloop error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* σ₄KeepMax :* σ₄Keep))
  -- TODO: push
  LoopPE e₂ e₃ xs x₁ x₂ e₄ → do
    let xs' = pow xs
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) $ inferPriv e₄
    let σ₄' = without (pow [x₁,x₂]) σ₄
    let σ₄Keep = restrict xs' σ₄'
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄'
    case (τ₂,ιview @ (Pr p RNF) σ₄KeepMax) of
      (ℕˢT ηₙ,Some p) | τ₄ ≡ τ₃ → do
        let p' = iteratePr ηₙ p
        tell $ map (Priv ∘ truncate (Quantity p') ∘ unPriv) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unPriv) σ₄Toss
        return τ₃
      _ → error $ "EDloop error: " ⧺ (pprender $ (τ₂ :* τ₃ :* τ₄ :* σ₄KeepMax :* σ₄Keep))
  GaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    -- TODO: fix this ιview thing as in MGauss
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return ℝT
      _ → error $ "Gauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  LaplacePE e₁ (EpsLaplaceParams e₂) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    -- TODO: fix this ιview thing as in MGauss
    case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ EpsPriv ηᵋ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return ℝT
      _ → error $ "Laplace error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  ParallelPE e₀ e₁ x₂ e₂ x₃ x₄ e₃ → do
    σ₀ :* τ₀ ← pmFromSM  $ hijack $ inferSens e₀
    σ₁ :* τ₁ ← pmFromSM $ hijack $ inferSens e₁
    case τ₀ of
      (𝕄T ℓ c StarRT me) | joins (values σ₀) ⊑ ι 1 →
        case τ₁ of
          (SetT τ₁') → do
            σ₂ :* τ₂ ← pmFromSM
              $ hijack
              $ mapEnvL contextTypeL (\ γ → (x₂ ↦ (𝕄T ℓ c (RexpRT (NatRNF 1)) me)) ⩌ γ)
              $ inferSens e₂
            let σₓ₂ = without (single𝑃 x₂) σ₂
            case (τ₁' ≡ τ₂) of
              False → error $ "ParallelPE partitioning type mismatch" ⧺ (pprender (τ₁',τ₂))
              True | and $ values (map (⊑ (Quantity (NatRNF 1))) (map unSens σₓ₂)) → do
                σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → (x₃ ↦ τ₁') ⩌ (x₄ ↦ (𝕄T ℓ c StarRT me)) ⩌ γ) $ inferPriv e₃
                let σₓ₃ = without (single𝑃 x₃) σ₃
                -- p is ⟨ε,δ⟩ in type rule
                let p':*σₓ₃₄ = ifNone (bot :* σₓ₃) $ dview x₄ σₓ₃
                tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₁
                tell $ map (Priv ∘ truncate Inf ∘ unSens) σₓ₂
                tell $ map (Priv ∘ truncate Inf ∘ unPriv) σₓ₃₄
                tell $ map (Priv ∘ truncate (unPriv p') ∘ unSens) σ₀
                return $ (SetT τ₃)
              _ → error $ "sensitivity error in ParallelPE"
          _ → error $ "℘ expected in second argument of ParallelPE" ⧺ (pprender τ₁)
      _ → error $ "𝕄T type expected in first argument of ParallelPE" ⧺ (pprender τ₀)
  SVTPE (EDSVTParams e₁) e₂ e₃ xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁, τ₂, τ₃, τ₄) of
      (ℝˢT ηᵋ, 𝕄T L1 UClip (RexpRT l) (RexpME r₂ ((αs :* τ₅) :⊸: (ηₛ :* ℝT))), ℝT, τ₅')
        | (τ₅ ≡ τ₅')
        ⩓ (l ≡ one)
--        ⩓ (ηₛ ≡ Sens (Quantity one)) -- TODO: why doesn't this one pass?
        → do
          tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ zero) ∘ unSens) σ₄Keep
          tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
          return $ 𝕀T r₂
      _ → error $ concat
            [ "Sparse Vector Technique error: "
            , "\n"
            , "τ₁: " ⧺ (pprender τ₁)
            , "\n"
            , "τ₂: " ⧺ (pprender τ₂)
            , "\n"
            , "τ₃: " ⧺ (pprender τ₃)
            , "\n"
            , "τ₄: " ⧺ (pprender τ₄)
            , "\n"
            , "Sensitivity bound: " ⧺ (pprender $ ιview @ RNF σ₄KeepMax)
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
  SVTPE (EPSSVTParams e₁) e₂ e₃ xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁, τ₂, τ₃, τ₄) of
      (ℝˢT ηᵋ, 𝕄T L1 UClip (RexpRT l) (RexpME r₂ ((αs :* τ₅) :⊸: (ηₛ :* ℝT))), ℝT, τ₅')
        | (τ₅ ≡ τ₅')
        ⩓ (l ≡ one)
--        ⩓ (ηₛ ≡ Sens (Quantity one)) -- TODO: why doesn't this one pass?
        → do
          tell $ map (Priv ∘ truncate (Quantity $ EpsPriv ηᵋ) ∘ unSens) σ₄Keep
          tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
          return $ 𝕀T r₂
      _ → error $ concat
            [ "Sparse Vector Technique error: "
            , "\n"
            , "τ₁: " ⧺ (pprender τ₁)
            , "\n"
            , "τ₂: " ⧺ (pprender τ₂)
            , "\n"
            , "τ₃: " ⧺ (pprender τ₃)
            , "\n"
            , "τ₄: " ⧺ (pprender τ₄)
            , "\n"
            , "Sensitivity bound: " ⧺ (pprender $ ιview @ RNF σ₄KeepMax)
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₃,τ₄) of
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,𝕄T ℓ _c ηₘ ηₙ)
        | (σ₄KeepMax ⊑ ι ηₛ)
        ⩓ (ℓ ≢ LInf)
        → do
          b ← isRealMExp ηₙ
          when (not b) $ throw (error "MGauss error isRealMExp check failed " ∷ TypeError)
          tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
          tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
          return $ 𝕄T LInf UClip ηₘ ηₙ
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,𝕄T ℓ _c ηₘ ηₙ) | (ℓ ≢ LInf) →
          error $ concat
            [ "MGauss error: "
            , "Claimed sensitivity bound (" ⧺ (pprender ηₛ) ⧺ ") is less than actual sensitivity bound (" ⧺ (pprender σ₄KeepMax) ⧺ ")\n"
            , "Debug info: "
            , pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax)
            , pprender σ₄
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
      _ → error $ concat
            [ "MGauss error: "
            , pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax)
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
  MGaussPE e₁ (ZCGaussParams e₂) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵨ,𝕄T L2 _c ηₘ ηₙ,Some ς) | ς ⊑ ηₛ → do
        b ← isRealMExp ηₙ
        when (not b) $ throw (error "MGauss error isRealMExp check failed" ∷ TypeError)
        tell $ map (Priv ∘ truncate (Quantity $ ZCPriv ηᵨ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ 𝕄T LInf UClip ηₘ ηₙ
      _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  MGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℕˢT ηᵅ,ℝˢT ηᵋ,𝕄T L2 _c ηₘ ηₙ,Some ς) | ς ⊑ ηₛ → do
        b ← isRealMExp ηₙ
        when (not b) $ throw (error "MGauss error isRealMExp check failed" ∷ TypeError)
        tell $ map (Priv ∘ truncate (Quantity $ RenyiPriv ηᵅ ηᵋ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ 𝕄T LInf UClip ηₘ ηₙ
      _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  MGaussPE e₁ (TCGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ρ,ℕˢT ω,𝕄T L2 _c ηₘ ηₙ,Some ς) | ς ⊑ ηₛ → do
        b ← isRealMExp ηₙ
        when (not b) $ throw (error "MGauss error isRealMExp check failed" ∷ TypeError)
        tell $ map (Priv ∘ truncate (Quantity $ TCPriv ρ ω) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ 𝕄T LInf UClip ηₘ ηₙ
      _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  BGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      -- TODO: do something with ℓ and c
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,BagT ℓ c ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        -- TODO: make sure ℓ and c are correct
        return $ BagT ℓ c ℝT
      _ → error $ "BGauss ED error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  BGaussPE e₁ (ZCGaussParams e₂) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
      -- TODO: do something with ℓ and c
      (ℝˢT ηₛ,ℝˢT ηᵨ,BagT ℓ c ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ ZCPriv ηᵨ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        -- TODO: make sure ℓ and c are correct
        return $ BagT ℓ c ℝT
      _ → error $ "BGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  BGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      -- TODO: do something with ℓ and c
      (ℝˢT ηₛ,ℝˢT ηᵅ,ℝˢT ηᵋ,BagT ℓ c ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ RenyiPriv ηᵅ ηᵋ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        -- TODO: make sure ℓ and c are correct
        return $ BagT ℓ c ℝT
      _ → error $ "BGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  GaussPE _e₁ (RenyiGaussParams _e₂ _e₃) _xs _e₄ → undefined
  GaussPE _e₁ (ZCGaussParams _e₂) _xs _e₃ → undefined
  ExponentialPE e₁ (EDExponentialParams e₂) e₃ xs x e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    mat ← pmFromSM $ inferSens e₃
    case mat of
      𝕄T _ℓ _c (RexpRT r₁) (RexpME r₂ τ₃) → do
        σ₄ :* τ₄ ← pmFromSM $ hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₃) ⩌ γ) $ inferSens e₄
        let σ₄' = delete x σ₄
            σ₄Keep = restrict xs' σ₄'
            σ₄KeepMax = joins $ values σ₄Keep
            σ₄Toss = without xs' σ₄'
        case (τ₁,τ₂,ιview @ RNF σ₄KeepMax) of
          (ℝˢT ηₛ,ℝˢT ηᵋ,Some ς) | (ς ⊑ ηₛ) ⩓ (τ₄ ≡ ℝT) ⩓ (r₁ ≡ one) → do
            tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ zero) ∘ unSens) σ₄Keep
            tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
            return $ 𝕀T r₂

          _ → error $ "Exponential error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
      _ → error "type error: ExponentialPE"
  ConvertZCEDPE e₁ e₂ → do
    τ₁ ← pmFromSM $ inferSens e₁
    case τ₁ of
      ℝˢT ηᵟ → do
        mapPPM (onPriv $ map $ convertZCEDPr ηᵟ) $ inferPriv e₂
      _ → error "type error: ConvertZCEDPE"
  ConvertRENYIEDPE e₁ e₂ → do
    τ₁ ← pmFromSM $ inferSens e₁
    case τ₁ of
      ℝˢT ηᵟ → do
        mapPPM (onPriv $ map $ convertRENYIEDPr ηᵟ) $ inferPriv e₂
      _ → error "type error: ConvertRENYIEDPE"
  ConvertEPSZCPE e₁ → do
    mapPPM (onPriv $ map $ convertEPSZCPr) $ inferPriv e₁
  EDSamplePE en exs eys xs' ys' e → do
    _ :* τn ← pmFromSM $ hijack $ inferSens en -- throw away the cost
    σ₁ :* τxs ← pmFromSM $ hijack $ inferSens exs
    σ₂ :* τys ← pmFromSM $ hijack $ inferSens eys
    -- check that upper bound on each of σ₁ and σ₂ is less than 1
    case (τn,τxs,τys) of
      (ℕˢT ηrows',𝕄T ℓ₁ c₁ (RexpRT ηrows₁) ς₁,𝕄T ℓ₂ c₂ (RexpRT ηrows₂) ς₂)
        | (ηrows₁ ≡ ηrows₂) ⩓ (joins (values σ₁) ⊑ ι 1) ⩓ (joins (values σ₂) ⊑ ι 1) {-⩓ (ηrows' ≤ ηrows₁)-} → do
            let τxs' = 𝕄T ℓ₁ c₁ (RexpRT ηrows') ς₁
                τys' = 𝕄T ℓ₂ c₂ (RexpRT ηrows') ς₂
                sε = ι 2 × ηrows' / ηrows₁
                sδ = ηrows' / ηrows₁
            σ :* τ ← hijack $ mapEnvL contextTypeL (\ γ → (xs' ↦ τxs') ⩌ (ys' ↦ τys') ⩌ γ) $ inferPriv e
            let σxs' = σ ⋕! xs'
                σys' = σ ⋕! ys'
                σ' = without (pow [xs',ys']) σ
            case (σxs',σys') of
              (Priv (Quantity (EDPriv ε₁ δ₁)), Priv (Quantity (EDPriv ε₂ δ₂))) → do
                tell $ map (Priv ∘ truncate (Quantity (EDPriv (ε₁×sε) (δ₁×sδ))) ∘ unSens) σ₁
                tell $ map (Priv ∘ truncate (Quantity (EDPriv (ε₂×sε) (δ₂×sδ))) ∘ unSens) σ₂
                tell σ'
                return τ
              _ → error $ "type error in EDSamplePE." ⧺ (pprender (σxs',σys'))
            -- pull out privacies p₁ for xs' p₂ and ys'
            -- truncate everything in σ₁ to be p₁ scaled by ⟨sε,sδ⟩
            -- truncate everything in σ₂ to be p₂ scaled by ⟨sε,sδ⟩
            -- output σ₁, σ₂, and leftovers from σ
      _ → error "type error in EDSamplePE"
  TCSamplePE en exs eys xs' ys' e → do
    _ :* τn ← pmFromSM $ hijack $ inferSens en
    σ₁ :* τxs ← pmFromSM $ hijack $ inferSens exs
    σ₂ :* τys ← pmFromSM $ hijack $ inferSens eys
    case (τn,τxs,τys) of
      (ℕˢT ηrows',𝕄T ℓ₁ c₁ (RexpRT ηrows₁) ς₁,𝕄T ℓ₂ c₂ (RexpRT ηrows₂) ς₂)
        | (ηrows₁ ≡ ηrows₂) ⩓ (joins (values σ₁) ⊑ ι 1) ⩓ (joins (values σ₂) ⊑ ι 1) → do
            let τxs' = 𝕄T ℓ₁ c₁ (RexpRT ηrows') ς₁
                τys' = 𝕄T ℓ₂ c₂ (RexpRT ηrows') ς₂
                s = ηrows' / ηrows₁
            σ :* τ ← hijack $ mapEnvL contextTypeL (\ γ → (xs' ↦ τxs') ⩌ (ys' ↦ τys') ⩌ γ) $ inferPriv e
            let σxs' = σ ⋕! xs'
                σys' = σ ⋕! ys'
                σ' = without (pow [xs',ys']) σ
            case (σxs',σys') of
              (Priv (Quantity (TCPriv ρ₁ _ω₁)), Priv (Quantity (TCPriv ρ₂ _ω₂))) → do
                tell $ map (Priv ∘ truncate (Quantity (TCPriv ((NNRealRNF 13.0) × s × s × ρ₁) ((log ((NNRealRNF 1.0)/s)) / ((NNRealRNF 4.0) × ρ₁)))) ∘ unSens) σ₁
                tell $ map (Priv ∘ truncate (Quantity (TCPriv ((NNRealRNF 13.0) × s × s × ρ₂) ((log ((NNRealRNF 1.0)/s)) / ((NNRealRNF 4.0) × ρ₂)))) ∘ unSens) σ₂
                tell σ'
                return τ
              _ → error $ "type error in TCSamplePE." ⧺ (pprender (σxs',σys'))
      _ → error "type error in TCSamplePE"
  RenyiSamplePE en exs eys xs' ys' e → do
    _ :* τn ← pmFromSM $ hijack $ inferSens en
    σ₁ :* τxs ← pmFromSM $ hijack $ inferSens exs
    σ₂ :* τys ← pmFromSM $ hijack $ inferSens eys
    case (τn,τxs,τys) of
      (ℕˢT ηrows',𝕄T ℓ₁ c₁ (RexpRT ηrows₁) ς₁,𝕄T ℓ₂ c₂ (RexpRT ηrows₂) ς₂)
        | (ηrows₁ ≡ ηrows₂) ⩓ (joins (values σ₁) ⊑ ι 1) ⩓ (joins (values σ₂) ⊑ ι 1) → do
            let τxs' = 𝕄T ℓ₁ c₁ (RexpRT ηrows') ς₁
                τys' = 𝕄T ℓ₂ c₂ (RexpRT ηrows') ς₂
                s = ηrows' / ηrows₁
            σ :* τ ← hijack $ mapEnvL contextTypeL (\ γ → (xs' ↦ τxs') ⩌ (ys' ↦ τys') ⩌ γ) $ inferPriv e
            let σxs' = σ ⋕! xs'
                σys' = σ ⋕! ys'
                σ' = without (pow [xs',ys']) σ
            case (σxs',σys') of
              (Priv (Quantity (RenyiPriv α₁ ϵ₁)), Priv (Quantity (RenyiPriv α₂ ϵ₂))) → do
                tell $ map (Priv ∘ truncate (Quantity (RenyiPriv α₁ (renyiϵ' (NatRNF 2) α₁ s ϵ₁))) ∘ unSens) σ₁
                tell $ map (Priv ∘ truncate (Quantity (RenyiPriv α₂ (renyiϵ' (NatRNF 2) α₂ s ϵ₂))) ∘ unSens) σ₂
                tell σ'
                return τ
              _ → error $ "type error in RenyiSamplePE." ⧺ (pprender (σxs',σys'))
      _ → error "type error in RenyiSamplePE"

  _ → error $ concat
        [ "inferPriv unknown expression type: "
        , "\n"
        , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
        ]

--  e → error $ fromString $ show e

renyiϵ' ∷ RNF → RNF → RNF → RNF → RNF
-- TODO
renyiϵ' j α s ϵ = (one / (α - one)) × log ((NNRealRNF 1.0) + (renyiϵ'Σpess j α s ϵ))

renyiϵ'Σpess ∷ RNF → RNF → RNF → RNF → RNF
renyiϵ'Σpess j α s ϵ = α × ((NNRealRNF 2.0) × (s^α)) × (α^α) × (exp ((α - one) × ϵ))

renyiϵ'Σ ∷ RNF → RNF → RNF → RNF → RNF
renyiϵ'Σ j α s ϵ = case α < j of
  True → (NNRealRNF 0.0)
  False → (((NNRealRNF 2.0) × (s^j)) × (choose α j) × (exp ((j - one) × ϵ))) + renyiϵ'Σ (j + (NatRNF 1)) α s ϵ

fac :: RNF → RNF
fac (NatRNF 0) = (NatRNF 1)
fac (NatRNF 1) = (NatRNF 1)
fac n = n × (fac (n - one))

choose :: RNF → RNF → RNF
choose n k = (fac n) / ((fac k) × (fac (n - k)))

substType ∷ 𝕏 → RNF → Type RNF → Type RNF
substType x r τ = substTypeR pø x r (fvRNF r) τ

substMExpR ∷ 𝑃 𝕏 → 𝕏 → RNF → 𝑃 𝕏 → MExp RNF → MExp RNF
substMExpR 𝓈 x r' fv = \case
  EmptyME → EmptyME
  VarME x' → VarME x'
  ConsME τ me → ConsME (substTypeR 𝓈 x r' fv τ) (substMExpR 𝓈 x r' fv me)
  AppendME me₁ me₂ → AppendME (substMExpR 𝓈 x r' fv me₁) (substMExpR 𝓈 x r' fv me₂)
  RexpME r τ → RexpME (substRNF x (renameRNF (renaming 𝓈 fv) r') r) (substTypeR 𝓈 x r' fv τ)

substTypeR ∷ 𝑃 𝕏 → 𝕏 → RNF → 𝑃 𝕏 → Type RNF → Type RNF
substTypeR 𝓈 x r' fv = \case
  ℕˢT r → ℕˢT $ substRNF x (renameRNF (renaming 𝓈 fv) r') r
  ℝˢT r → ℝˢT $ substRNF x (renameRNF (renaming 𝓈 fv) r') r
  ℕT → ℕT
  ℝT → ℝT
  𝕀T r → 𝕀T $ substRNF x (renameRNF (renaming 𝓈 fv) r') r
  𝔹T → 𝔹T
  𝕊T → 𝕊T
  SetT τ → SetT $ substTypeR 𝓈 x r' fv τ
  𝕄T ℓ c rs me →
    let rs' = case rs of
          RexpRT r → RexpRT $ substRNF x (renameRNF (renaming 𝓈 fv) r') r
          StarRT → StarRT
    in 𝕄T ℓ c rs' $ substMExpR 𝓈 x r' fv me
  𝔻T τ → 𝔻T $ substTypeR 𝓈 x r' fv τ
  τ₁ :+: τ₂ → substTypeR 𝓈 x r' fv τ₁ :+: substTypeR 𝓈 x r' fv τ₂
  τ₁ :×: τ₂ → substTypeR 𝓈 x r' fv τ₁ :×: substTypeR 𝓈 x r' fv τ₂
  τ₁ :&: τ₂ → substTypeR 𝓈 x r' fv τ₁ :&: substTypeR 𝓈 x r' fv τ₂
  (ακs :* τ₁) :⊸: (s :* τ₂) →
    let 𝓈' = joins [𝓈,pow $ map fst ακs]
    in (ακs :* substTypeR 𝓈' x r' fv τ₁) :⊸: (map (substRNF x (renameRNF (renaming 𝓈' fv) r')) s :* substTypeR 𝓈' x r' fv τ₂)
  (ακs :* PArgs args) :⊸⋆: τ →
    let 𝓈' = joins [𝓈,pow $ map fst ακs]
    in (ακs :* PArgs (mapOn args $ \ (τ' :* p) → substTypeR 𝓈' x r' fv τ' :* p)) :⊸⋆: substTypeR 𝓈' x r' fv τ
  BoxedT γ τ → BoxedT (mapp (substRNF x (renameRNF (renaming 𝓈 fv) r')) γ) (substTypeR 𝓈 x r' fv τ)

-- infraRed :: PExp -> KEnv → TEnv -> (TypeSource RNF, PEnv)
--
-- infraRed (PBindE x e₁ e₂) δ γ =
--     let (τ₁, pγ₁) = infraRed e₁ δ γ
--         (τ₂, pγ₂) = infraRed e₂ δ $ (x ↦ τ₁) ⩌ γ
--     in
--     (τ₂, pγ₁ `privAddEnv` pγ₂)
--
--
-- infraRed (PAppE αs e el) δ tenv =
--     let (t, senv) = infer e δ tenv
--     in
--        case t of
--             PFunT aks tps t' ->
--                 let ks  = map (kinferRNF δ) (map normalizeRExp αs)
--                 in
--                 case (elem Nothing ks, iterType el (map fst tps) tenv) of
--                      (False, True) -> (t', privAddEnv (Map.fromList (zip el (map snd tps))) (privMultEnv InfP (privSensCrossEnv senv)) )
--                      (_,_ ) -> error "type error"
--             _ -> error "type error"
-- -- case (e, t) of --      (SPFunE vtl e', PFunT tpl t') -> --        let tl = map fst tpl --            pl = map snd tpl --            vl = map fst vtl
--     --        in undefined
--     --       -- old stuff...
--     --            -- if (iterType el tl tenv)
--     --            --     then (t', (iterPrivU vl pl))
--     --            --     else error "type error"
--
-- -- TODO: actually typecheck that x₁ is a nat
-- infraRed (PLoopE x1 x2 x3 xs x₁ x₂ e) δ tenv =
--     let (t1, senv1) = infer x1 δ tenv
--         (t2, senv2) = infer x2 δ tenv
--         (t3, senv3) = infer x3 δ tenv
--         (t', penv) = infraRed e δ (Map.insert x₁ NatT (Map.insert x₂ t3 tenv))
--         in case (t1, t2, t3 == t', maxPriv (Map.restrictKeys penv (pow xs))) of
--                 (SingNNRealT d1, SingNatT n, True, EDPriv ep d) ->
--                     let ep' =
--                           NatRNF 2
--                           `timesRNF`
--                           ep
--                           `timesRNF`
--                           rootRNF (NatRNF 2
--                                    `timesRNF`
--                                    n
--                                    `timesRNF`
--                                    logRNF (invRNF d1))
--                         d' = (d1 `plusRNF` (n `timesRNF` d))
--                     in (t',(privAddEnv (privMultEnv InfP (privSensCrossEnv senv3))  (privMultEnv (EDPriv ep' d') (privCrossEnv penv))))
--                 (_,_,_,a) -> error $ "type error" ++ (show (t1, t2, t3 == t', (Map.restrictKeys penv (pow xs))))
--
-- infraRed (PSampleE se x1 x2 v1 v2 e) δ tenv =
--     let (t, senv) = infer se δ tenv
--         t1 = tenv Map.! x1
--         t2 = tenv Map.! x2
--         senv' = (privMultEnv InfP (privSensCrossEnv senv))
--     in case (t, t1, t2) of
--             (SingNatT n'', MatrixT l c m n t3, MatrixT l' c' m' n' t4) ->
--                 let (t5, penv) = infraRed e δ (Map.insert v1 (MatrixT l c n'' n t3) (Map.insert v2 (MatrixT l' c' n'' n' t4) tenv))
--                     p1 = penv Map.! v1
--                     p2 = penv Map.! v2
--                     ep = NatRNF 2 `timesRNF` n'' `timesRNF` invRNF m
--                     d =  n'' `timesRNF` invRNF m
--                     priv1 = privMult p1 (EDPriv ep d)
--                     priv2 = privMult p2 (EDPriv ep d)
--                     penv' = (privAddEnv (privMultEnv (EDPriv (NatRNF 0) (NatRNF 0)) (privSensCrossEnv senv)) (Map.insert x2 priv2 (Map.insert x1 priv1 penv)))
--                 in
--                   if NatRNF 0 ⊑ n''   && {-n ⊑ m  &&-}  m == m'
--                     then (t5, penv')
--                     else error $ "type error" ++ Prelude.unlines (map (\x -> (chars $ sho x) ++ "\n") (Map.toList penv'))
--             (_,_,_) -> error $ "type error" ++(show (t, t1, t2))
--
--
-- infraRed (PRandNatE e1 e2) δ tenv =
--     let (t1, senv1) = infer e1 δ tenv
--         (t2, senv2) = infer e2 δ tenv
--     in case (t1, t2) of
--             (NatT, NatT) -> (NatT, privMultEnv InfP (privSensCrossEnv senv1))
--             (_,_) -> error $ "type error" ++ (show (t1, t2))
--
-- infraRed (PGaussE e1 e2 e3 xs e4) δ tenv =
--     let (t1, senv1) = infer e1 δ tenv
--         (t2, senv2) = infer e2 δ tenv
--         (t3, senv3) = infer e3 δ tenv
--         (t4, senv4) = infer e4 δ tenv
--         r = maxSens (Map.restrictKeys senv4 (Set.fromList xs))
--     in
--     case (t1, t2, t3, t4, r) of
--          (SingNNRealT r1, SingNNRealT ep, SingNNRealT delt, RealT, RealSens r') ->
--             if r' ⊑ r1
--                 then (RealT, privAddEnv (privMultEnv InfP (privSensCrossEnv senv1)) (privMultEnv (EDPriv ep delt) (privSensCrossEnv senv4)))
--                 else error "type error"
--          (SingNNRealT r1, SingNNRealT ep, SingNNRealT delt, RealT, InfS) ->
--             (RealT, privAddEnv (privMultEnv InfP (privSensCrossEnv senv1)) (privMultEnv (EDPriv ep delt) (privSensCrossEnv senv4)))
--          (_,_,_,_,_) -> error $ "type error" ++ (show (t1, t2, t3, t4, r))
--
-- infraRed (PMGaussE e1 e2 e3 xs e4) δ tenv =
--     let (t1, senv1) = infer e1 δ tenv
--         (t2, senv2) = infer e2 δ tenv
--         (t3, senv3) = infer e3 δ tenv
--         (t4, senv4) = infer e4 δ tenv
--         r = maxSens (Map.restrictKeys senv4 (Set.fromList xs))
--     in
--     case (t4, t1, t2, t3, r) of
--          (MatrixT L2  c m n RealT, SingNNRealT r1, SingNNRealT e, SingNNRealT d, RealSens r') ->
--            if r' ⊑ r1
--              then (MatrixT L2 c m n RealT, privAddEnv (privMultEnv InfP (privSensCrossEnv senv1)) (privMultEnv (EDPriv e d) (privSensCrossEnv senv4)))
--              else error $ "type error" ++ show (prettyRNF r',prettyRNF r1)
--          (_,_,_,_,_) -> error $ "type error" ++ (show (t4, t1, t2, t3, r))
--
--
--
-- infraRed (PLaplaceE e1 e2 xs e3) δ tenv =
--     let (t1, senv1) = infer e1 δ tenv
--         (t2, senv2) = infer e2 δ tenv
--         (t3, senv3) = infer e3 δ tenv
--         r = maxSens (Map.restrictKeys senv3 (Set.fromList xs))
--     in
--     case (t1, t2, t3, r) of
--          (SingNNRealT r1, SingNNRealT ep, RealT, RealSens r') ->
--             if r1 > r'
--                 then (RealT, privAddEnv (privMultEnv (EDPriv ep (NatRNF 0)) (privSensCrossEnv senv3)) (privMultEnv InfP (privSensCrossEnv senv1)))
--                 else error "type error"
--          (SingNNRealT r1, SingNNRealT ep, RealT, InfS) ->
--             (RealT, privAddEnv (privMultEnv (EDPriv ep (NatRNF 0)) (privSensCrossEnv senv3)) (privMultEnv InfP (privSensCrossEnv senv1)))
--          (_,_,_,_) -> error "type error"
--
-- infraRed (PExpE e1 e2 e3 v4 e) δ tenv =
--     let (t1, senv1) = infer e1 δ tenv
--         (t2, senv2) = infer e2 δ tenv
--         (t3, senv3) = infer e3 δ tenv
--     in
--     case (t1, t2, t3) of
--          (SingNNRealT r1, SingNNRealT ep, MatrixT ℓ c r''' n' tm)
--            -- TODO: fix this check
--            | r''' == NatRNF 1 ->
--             let (t, senv) = infer e δ (Map.insert v4 tm tenv)
--                 s = maxSens senv
--             in  case s of
--                      RealSens r' ->
--                         if r1 > r'
--                             then (tm, privAddEnv (privMultEnv (EDPriv ep (NatRNF 0)) (privSensCrossEnv senv)) (privMultEnv InfP (privSensCrossEnv senv1 )))
--                             else error "type error"
--                      InfS -> (tm, privAddEnv (privMultEnv (EDPriv ep (NatRNF 0)) (privSensCrossEnv senv)) (privMultEnv InfP (privSensCrossEnv senv1 )))
--          (_,_,_) -> error "type error"
--
-- infraRed (PRRespE e1 e2 xs e3) δ tenv =
--     let (t1, senv1) = infer e1 δ tenv
--         (t2, senv2) = infer e2 δ tenv
--         (t3, senv3) = infer e3 δ tenv
--         r = maxSens (Map.restrictKeys senv3 (Set.fromList xs))
--     in
--     case (t1, t2, t3) of
--          (SingNatT n, SingNNRealT ep, NatT) ->
--                if r ⊑ (RealSens n)
--                 then (NatT, privAddEnv (privMultEnv (EDPriv ep (NatRNF 0)) (privSensCrossEnv senv3)) (privMultEnv InfP (privSensCrossEnv senv1)))
--                 else error "type error"
--          (_,_,_) -> error "type error"
--
-- infraRed (PReturnE e) δ γ =
--     let (t, sγ) = infer e δ γ in
--     (t, InfP `privMultEnv` privSensCrossEnv sγ)
--
--
-- iterType :: [Var] -> [TypeSource RNF] -> TEnv  -> Bool
-- iterType vl tl tenv = case (vl,tl) of
--      ([],[]) -> True
--      (v:vl',t:tl') ->  (tenv Map.! v  == t) && (iterType vl' tl' tenv)
--      (_,_) -> False
--
-- -- iterPrivU :: [Var] -> [Priv] -> PEnv
-- -- iterPrivU vl pl = case (vl,pl) of
-- --     ([],[]) -> Map.empty
-- --     (v:vl',p:pl') -> Map.insert v p (iterPrivU vl' pl')
-- --     (_,_) -> error "list error"
--
--
--
-- -- iterSens :: PEnv -> [Var] -> [Priv]
-- -- iterSens penv varl = case varl of
-- --     [] -> []
-- --     v:varl' -> (penv Map.! v):(iterSens penv varl')
--
-- -- iterU :: [Var] -> [TypeSource] -> TEnv
-- -- iterU varl typl = case (varl, typl) of
-- --     ([],[]) -> Map.empty
-- --     (v:varl', t:typl') -> Map.insert v t (iterU varl' typl')
-- --     (_,_) -> error "list error"
--
-- γø = Map.insert "sign" (SFunT NatT (RealSens $ RealRNF 1.0) NatT) dø
--
-- main :: IO ()
-- main = do
--   fns ← getArgs
--   each fns $ \ fn → do
--       e ←  read ^$ chars ^$ (CustomPrelude.readFile ("examples/" ⧺ fn ⧺ ".raw"))
--       shout e
--       let (PFunT αks τps τ,sγ) = infer e dø γø
--       shout τ
--       shout sγ
--       out "--------------------------------------------"
--       each (zip αks τps) $ \case
--         ((v,k),(τ,InfP)) → do
--           out $ "\n Var:  " ⧺ v
--           out $ "TypeSource: " ⧺ sho τ
--           out $ "(ε,δ) privacy bound: " ⧺ "∞"
--         ((v,k),(τ,EDPriv ε δ)) → do
--           out $ "\n Var:  " ⧺ v
--           out $ "TypeSource: " ⧺ sho τ
--           out $ "(ε,δ) privacy bound: " ⧺ prettyRNF ε ⧺ ", " ⧺ prettyRNF δ
--
--   -- undefined
--     -- putStrLn $ show (sgdTest "xs" "ys")
--     -- putStrLn $ show $ infraRed (sgdTest "xs" "ys") env
--   -- e = λ(x:nat).x
--   -- putStrLn $ show $ infer (FunE "x" NatT (VarE "x")) Map.empty
--   -- putStrLn $ show $ infer (FunE "x" NatT (VarE "y")) Map.empty
