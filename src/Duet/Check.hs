module Duet.Check where

import UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RExp
import Duet.Var
import Duet.Quantity

inferKind ∷ 𝕏 ⇰ Kind → RExpPre → 𝑂 Kind
inferKind δ = \case
  VarRE x → return $ δ ⋕! x
  NatRE _ → return $ ℕK
  NNRealRE _ → return $ ℝK
  MaxRE e₁ e₂ → do
    κ₁ ← inferKind δ $ extract e₁
    κ₂ ← inferKind δ $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → abort
  MinRE e₁ e₂ → do
    κ₁ ← inferKind δ $ extract e₁
    κ₂ ← inferKind δ $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → abort
  PlusRE e₁ e₂ → do
    κ₁ ← inferKind δ $ extract e₁
    κ₂ ← inferKind δ $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → abort
  TimesRE e₁ e₂ → do
    κ₁ ← inferKind δ $ extract e₁
    κ₂ ← inferKind δ $ extract e₂
    case (κ₁,κ₂) of
      (ℕK,ℕK) → return ℕK
      (ℝK,ℝK) → return ℝK
      _ → abort
  DivRE e₁ e₂ → do
    κ₁ ← inferKind δ $ extract e₁
    κ₂ ← inferKind δ $ extract e₂
    case (κ₁,κ₂) of
      (ℝK,ℝK) → return ℝK
      _ → abort
  RootRE e → do
    κ ← inferKind δ $ extract e
    case κ of
      ℝK → return ℝK
      _ → abort
  LogRE e → do
    κ ← inferKind δ $ extract e
    case κ of
      ℝK → return ℝK
      _ → abort

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
  }
makeLenses ''Context
makePrettyRecord ''Context

newtype SM p a = SM { unSM ∷ ReaderT Context (WriterT (𝕏 ⇰ Sens RNF) (ErrorT TypeError ID)) a }
  deriving 
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (𝕏 ⇰ Sens RNF))

mkSM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → TypeError ∨ ((𝕏 ⇰ Sens RNF) ∧ a)) → SM p a
mkSM f = SM $ ReaderT $ \ (Context δ γ) → WriterT $ ErrorT $ ID $ f δ γ

runSM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → SM p a → TypeError ∨ ((𝕏 ⇰ Sens RNF) ∧ a)
runSM δ γ = unID ∘ unErrorT ∘ unWriterT ∘ runReaderT (Context δ γ) ∘ unSM

newtype PM p a = PM { unPM ∷ ReaderT Context (WriterT (𝕏 ⇰ Priv p RNF) (ErrorT TypeError ID)) a }
  deriving 
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (𝕏 ⇰ Priv p RNF))

mkPM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → TypeError ∨ ((𝕏 ⇰ Priv p RNF) ∧ a)) → PM p a
mkPM f = PM $ ReaderT $ \ (Context δ γ) → WriterT $ ErrorT $ ID $ f δ γ

runPM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → PM p a → TypeError ∨ ((𝕏 ⇰ Priv p RNF) ∧ a)
runPM δ γ = unID ∘ unErrorT ∘ unWriterT ∘ runReaderT (Context δ γ) ∘ unPM

smFromPM ∷ PM p a → SM p a
smFromPM xM = mkSM $ \ δ γ → mapInr (mapFst $ map $ Sens ∘ truncate Inf ∘ unPriv) $ runPM δ γ xM

pmFromSM ∷ SM p a → PM p a
pmFromSM xM = mkPM $ \ δ γ → mapInr (mapFst $ map $ Priv ∘ truncate Inf ∘ unSens) $ runSM δ γ xM

mapPPM ∷ (Priv p₁ RNF → Priv p₂ RNF) → PM p₁ a → PM p₂ a 
mapPPM f xM = mkPM $ \ δ γ → mapInr (mapFst $ map f) $ runPM δ γ xM

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
      (𝔻T,𝔻T) → return 𝔻T
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
      (𝔻T,𝔻T) → return 𝔻T
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
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
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
      (𝔻T,𝔻T) → do tell $ σ₁ ⧺ σ₂ ; return 𝔻T
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
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
  RootSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ rootRNF η
      ℝT → do tell $ top ⨵ σ ; return ℝT
      𝔻T → return 𝔻T
      _ → undefined -- TypeError
  LogSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ rootRNF η
      ℝT → do tell $ top ⨵ σ ; return ℝT
      𝔻T → return 𝔻T
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
      (𝔻T,𝔻T) → return 𝔻T
      _ → error $ "Minus error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeError
  MCreateSE ℓ e₁ e₂ x₁ x₂ e₃ → do
    τ₁ ← inferSens e₁ 
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT ηₘ,ℕˢT ηₙ) → do
        σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ 𝕀T ηₘ,x₂ ↦ 𝕀T ηₙ] ⩌ γ) $ inferSens e₃
        let σ₃' = without (pow [x₁,x₂]) σ₃
        tell $ ι (ηₘ × ηₙ) ⨵ σ₃'
        return $ 𝕄T ℓ UClip ηₘ ηₙ τ₃
      _ → undefined -- TypeError
  MIndexSE e₁ e₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    case (τ₁,τ₂,τ₃) of
      (𝕄T _ℓ _c ηₘ ηₙ τ,𝕀T ηₘ',𝕀T ηₙ') → return τ -- -- | (ηₘ' ≤ ηₘ) ⩓ (ηₙ' ≤ ηₙ) → return τ
      -- had error: duet: ⟨⟨𝕄 [L∞ U|1,n] ℝ,ℕ⟩,ℕ⟩
      _ → error $ "Index error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃)) -- TypeError
  MUpdateSE e₁ e₂ e₃ e₄ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    τ₄ ← inferSens e₄
    case (τ₁,τ₂,τ₃,τ₄) of
      -- TODO: why does this check fail for FW?
      (𝕄T ℓ c ηₘ ηₙ τ,𝕀T ηₘ',𝕀T ηₙ',τ') | {-(ηₘ' ≤ ηₘ) ⩓ -}(ηₙ' ≤ ηₙ) ⩓ (τ ≡ τ') →
                                          return $ 𝕄T ℓ c ηₘ ηₙ τ
      _ → error $ "Update error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄)) -- TypeError
  MRowsSE e → do
    _ :* τ ← hijack $ inferSens e
    case τ of
      𝕄T _ℓ _c ηₘ _ηₙ _τ' → return $ ℕˢT ηₘ
      _ → undefined -- TypeSource Error
  MColsSE e → do
    _ :* τ ← hijack $ inferSens e
    case τ of
      𝕄T _ℓ _c _ηₘ ηₙ _τ' → return $ ℕˢT ηₙ
      _ → undefined -- TypeSource Error
  MClipSE ℓ e → do
    τ ← inferSens e
    case τ of
      𝕄T ℓ' _c ηₘ ηₙ τ' | τ' ≡ 𝔻T → return $ 𝕄T ℓ' (NormClip ℓ) ηₘ ηₙ τ'
      _ → undefined -- TypeSource Error
  MConvertSE e → do
    τ ← inferSens e
    case τ of
      𝕄T _ℓ (NormClip ℓ) ηₘ ηₙ τ' | τ' ≡ 𝔻T → return $ 𝕄T ℓ UClip ηₘ ηₙ ℝT
      _ → undefined -- TypeSource Error
  MLipGradSE _g e₁ e₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    tell $ top ⨵ σ₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    σ₃ :* τ₃ ← hijack $ inferSens e₃
    case (τ₁,τ₂,τ₃) of
      (𝕄T _ℓ₁ _c₁ ηₘ₁ ηₙ₁ τ₁',𝕄T _ℓ₂ (NormClip ℓ) ηₘ₂ ηₙ₂ τ₂',𝕄T _ℓ₃ _c₃ ηₘ₃ ηₙ₃ τ₃') 
        | meets
          [ τ₁' ≡ ℝT
          , τ₂' ≡ 𝔻T
          , τ₃' ≡ 𝔻T
          , ηₘ₁ ≡ one
          , ηₙ₃ ≡ one
          , ηₙ₁ ≡ ηₙ₂
          , ηₘ₂ ≡ ηₘ₃
          ]
        → do tell $ ι (ι 1 / ηₘ₂) ⨵ (σ₂ ⧺ σ₃)
             return $ 𝕄T ℓ UClip one ηₙ₁ ℝT
      _ → undefined -- TypeSource Error
  MMapSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ _c ηₘ ηₙ τ₁' → do
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ ι (ηₘ × ηₙ) ⨵ σ₂'
        return $ 𝕄T ℓ UClip ηₘ ηₙ τ₂ 
      _  → undefined -- TypeSource Error
  MMap2SE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (𝕄T ℓ₁ _c₁ ηₘ₁ ηₙ₁ τ₁',𝕄T ℓ₂ _c₂ ηₘ₂ ηₙ₂ τ₂')
        | meets
          [ ℓ₁ ≡ ℓ₂
          , ηₘ₁ ≡ ηₘ₂
          , ηₙ₁ ≡ ηₙ₂
          ]
        → do σ₃ :* τ₃ ← 
               hijack $ 
               mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁',x₂ ↦ τ₂'] ⩌ γ) $ 
               inferSens e₃
             let (ς₁ :* σ₃') = ifNone (zero :* σ₃) $ dview x₁ σ₃
                 (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
             tell $ ς₁ ⨵ σ₁
             tell $ ς₂ ⨵ σ₂
             tell $ ι (ηₘ₁ × ηₙ₁) ⨵ σ₃''
             return $ 𝕄T ℓ₁ UClip ηₘ₁ ηₙ₁ τ₃
      _ → error $ "Map2 error: " ⧺ (pprender $ (τ₁ :* τ₂))
  VarSE x → do
    γ ← askL contextTypeL
    case γ ⋕? x of
      None → error $ fromString (show x) -- TypeSource Error
      Some τ → do
        tell $ x ↦ ι 1
        return τ
  LetSE x e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferSens e₂
    let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
    tell $ ς ⨵ σ₁
    tell σ₂'
    return τ₂
  SFunSE x τ e → do
    let τ' = map normalizeRExp $ extract τ
    σ :* τ'' ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ') ⩌ γ) $ inferSens e
    let (ς :* σ') = ifNone (zero :* σ) $ dview x σ
    tell σ'
    return $ τ' :⊸: (ς :* τ'')
  AppSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case τ₁ of
      τ₁' :⊸: (ς :* τ₂') | τ₁' ≡ τ₂ → do
        tell $ ς ⨵ σ₂
        return τ₂'
      _ → error $ "Application error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeSource Error
  PFunSE ακs xτs e → do
    let xτs' = map (mapSnd (map normalizeRExp ∘ extract)) xτs
        xs = map fst xτs
    σ :* τ ← 
      smFromPM 
      $ hijack 
      $ mapEnvL contextKindL (\ δ → assoc ακs ⩌ δ)
      $ mapEnvL contextTypeL (\ γ → assoc xτs' ⩌ γ)
      $ inferPriv e
    tell $ map (Sens ∘ truncate Inf ∘ unPriv) $ without (pow xs) σ
    let τps = mapOn xτs' $ \ (x :* τ') → τ' :* ifNone null (σ ⋕? x)
    return $ (ακs :* PArgs τps) :⊸⋆: τ
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
      ℕˢT η → do tell σ ; return $ 𝕀T $ rootRNF η
      _ → undefined -- TypeError

  e → error $ fromString $ show e

inferPriv ∷ ∀ p. (PRIV_C p) ⇒ PExpSource p → PM p (Type RNF)
inferPriv eA = case extract eA of
  ReturnPE e → pmFromSM $ inferSens e
  BindPE x e₁ e₂ → do
    τ₁ ← inferPriv e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferPriv e₂
    tell $ delete x σ₂
    return τ₂
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
    case (τ₁,τ₂,ιview @ (Pr 'ED RNF) σ₄KeepMax) of
      (ℝˢT ηᵟ',ℕˢT ηₙ,Some (EDPriv ηᵋ ηᵟ)) | τ₄ ≡ τ₃ → do 
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
        let p' = scalePr ηₙ p
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
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return ℝT
      _ → undefined -- TypeError
  MGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,𝕄T L2 _c ηₘ ηₙ ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ 𝕄T LInf UClip ηₘ ηₙ ℝT
      _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  MGaussPE e₁ (ZCGaussParams e₂) xs e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵨ,𝕄T L2 _c ηₘ ηₙ ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ ZCPriv ηᵨ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ 𝕄T LInf UClip ηₘ ηₙ ℝT
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
      (ℝˢT ηₛ,ℝˢT ηᵅ,ℝˢT ηᵋ,𝕄T L2 _c ηₘ ηₙ ℝT,Some ς) | ς ⊑ ηₛ → do
        tell $ map (Priv ∘ truncate (Quantity $ RenyiPriv ηᵅ ηᵋ) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ 𝕄T LInf UClip ηₘ ηₙ ℝT
      _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  GaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄ → undefined
  GaussPE e₁ (ZCGaussParams e₂) xs e₃ → undefined
  ExponentialPE e₁ (EDExponentialParams e₂) e₃ xs x e₄ → do
    let xs' = pow xs
    τ₁ ← pmFromSM $ inferSens e₁
    τ₂ ← pmFromSM $ inferSens e₂
    𝕄T _ℓ _c ηₘ _ηₙ τ₃ ← pmFromSM $ inferSens e₃
    σ₄ :* τ₄ ← pmFromSM $ hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₃) ⩌ γ) $ inferSens e₄
    let σ₄' = delete x σ₄
    let σ₄Keep = restrict xs' σ₄'
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄'
    case (τ₁,τ₂,ιview @ RNF σ₄KeepMax) of
      (ℝˢT ηₛ,ℝˢT ηᵋ,Some ς) | (ς ⊑ ηₛ) ⩓ (τ₄ ≡ ℝT) ⩓ (ηₘ ≡ one) → do
        tell $ map (Priv ∘ truncate (Quantity $ EDPriv ηᵋ zero) ∘ unSens) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
        return $ τ₃
      _ → error $ "Exponential error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
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
  e → error $ fromString $ show e
   
    
    
    
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
