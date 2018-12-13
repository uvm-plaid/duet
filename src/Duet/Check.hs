module Duet.Check where

import UVMHS

import Duet.Syntax
import Duet.RExp
import Duet.Var
import Duet.Quantity
import Duet.AddToUVMHS

inferKind ∷ 𝕏 ⇰ KindPre → RExpPre → 𝑂 KindPre
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

data TypeError p = TypeError
  { typeErrorTerm ∷ Doc
  , typeErrorContext ∷ (𝕏 ⇰ TypePre p RNF)
  , typeErrorType ∷ TypePre p RNF
  , typeErrorExpected ∷ 𝐿 𝕊
  }
makePrettyRecord ''TypeError

anno ∷ a → Annotated FullContext a
anno = Annotated $ FullContext null null null

inferSens ∷ (Privacy p) 
          ⇒ (𝕏 ⇰ Kind) 
          → (𝕏 ⇰ TypePre p RNF) 
          → SExp p 
          → ErrorT (TypeError p) (WriterT (𝕏 ⇰ Sens RNF) ID) (TypePre p RNF)
inferSens δ γ eA = case extract eA of
  ℕˢSE n → return $ ℕˢT $ NatRNF n
  ℝˢSE d → return $ ℝˢT $ NNRealRNF d
  DynSE e → do
    τ ← inferSens δ γ e
    case τ of
      ℕˢT _η → return ℕT
      ℝˢT _η → return ℝT
      𝕀T _η → return ℕT
      _ → throw $ TypeError (pretty $ annotatedTag eA) γ τ (list ["singleton nat","singleton real"])
  ℕSE _n → return $ ℕT
  ℝSE _d → return $ ℝT
  RealSE e → do
    τ ← inferSens δ γ e
    case τ of
      ℕT → return ℝT
      ℕˢT η → return $ ℝˢT η
      _ → undefined -- TypeError
  MaxSE e₁ e₂ → do
    τ₁ ← inferSens δ γ e₁
    τ₂ ← inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ ⊔ η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ ⊔ η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ ⊔ η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
  MinSE e₁ e₂ → do
    τ₁ ← inferSens δ γ e₁
    τ₂ ← inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ ⊓ η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ ⊓ η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ ⊓ η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
  PlusSE e₁ e₂ → do
    τ₁ ← inferSens δ γ e₁
    τ₂ ← inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ + η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ + η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ + η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
  TimesSE e₁ e₂ → do
    σ₁ :* τ₁ ← listen $ inferSens δ γ e₁
    σ₂ :* τ₂ ← listen $ inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℕˢT $ η₁ × η₂
      (ℝˢT η₁,ℝˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℝˢT $ η₁ × η₂
      (𝕀T η₁,𝕀T η₂) →   do tell $ σ₁ ⧺ σ₂ ; return $ 𝕀T $ η₁ × η₂
      (ℕˢT η₁,ℕT) → do
        tell $ σ₁ ⧺ map ((×) $ Sens $ Quantity η₁) σ₂
        return ℕT
      (ℕT,ℕˢT η₂) → do
        tell $ map ((×) $ Sens $ Quantity η₂) σ₁ ⧺ σ₂
        return ℕT
      (ℝˢT η₁,ℝT) → do
        tell $ σ₁ ⧺ map ((×) $ Sens $ Quantity η₁) σ₂
        return ℝT
      (ℝT,ℝˢT η₂) → do
        tell $ map ((×) $ Sens $ Quantity η₂) σ₁ ⧺ σ₂
        return ℝT
      (𝕀T η₁,ℕT) → do
        tell $ σ₁ ⧺ map ((×) $ Sens $ Quantity η₁) σ₂
        return ℕT
      (ℕT,𝕀T η₂) → do
        tell $ map ((×) $ Sens $ Quantity η₂) σ₁ ⧺ σ₂
        return ℕT
      (ℕT,ℕT) → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (ℝT,ℝT) → do tell $ σ₁ ⧺ σ₂ ; return ℝT
      (𝔻T,𝔻T) → do tell $ σ₁ ⧺ σ₂ ; return 𝔻T
      _ → undefined -- TypeError
  DivSE e₁ e₂ → do
    σ₁ :* τ₁ ← listen $ inferSens δ γ e₁
    σ₂ :* τ₂ ← listen $ inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℝˢT η₁,ℝˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℝˢT $ η₁ / η₂
      (ℝˢT _η₁,ℝT) → do 
        tell $ σ₁ ⧺ map ((×) $ Sens Inf) σ₂
        return $ ℝT
      (ℝT,ℝˢT η₂) → do 
        tell $ map ((×) $ Sens $ Quantity $ one / η₂) σ₁ ⧺ σ₂ 
        return $ ℝT
      (ℝT,ℝT) → return ℝT
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
  RootSE e → do
    σ :* τ ← listen $ inferSens δ γ e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ rootRNF η
      ℝT → do tell $ map ((×) $ Sens Inf) σ ; return ℝT
      𝔻T → return 𝔻T
      _ → undefined -- TypeError
  LogSE e → do
    σ :* τ ← listen $ inferSens δ γ e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ rootRNF η
      ℝT → do tell $ map ((×) $ Sens Inf) σ ; return ℝT
      𝔻T → return 𝔻T
      _ → undefined -- TypeError
  ModSE e₁ e₂ → do
    σ₁ :* τ₁ ← listen $ inferSens δ γ e₁
    σ₂ :* τ₂ ← listen $ inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℕˢT _η₁,ℕˢT _η₂) → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (𝕀T _η₁,𝕀T _η₂)   → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (ℕˢT η₁,ℕT) → do
        tell $ σ₁ ⧺ map ((×) $ Sens $ Quantity η₁) σ₂
        return ℕT
      (ℕT,ℕˢT η₂) → do 
        tell $ map ((×) $ Sens $ Quantity η₂) σ₁ ⧺ σ₂
        return ℕT
      (𝕀T η₁,ℕT) → do
        tell $ σ₁ ⧺ map ((×) $ Sens $ Quantity η₁) σ₂
        return ℕT
      (ℕT,𝕀T η₂) → do
        tell $ map ((×) $ Sens $ Quantity η₂) σ₁ ⧺ σ₂
        return ℕT
      (ℕT,ℕT) → do tell $ map ((×) $ Sens Inf) $ σ₁ ⧺ σ₂ ; return ℕT
      _ → undefined -- TypeError
  MinusSE e₁ e₂ → do
    τ₁ ← inferSens δ γ e₁
    τ₂ ← inferSens δ γ e₂
    case (τ₁,τ₂) of
      (ℝˢT _η₁,ℝˢT _η₂) → return ℝT
      (ℝT,ℝT) → return ℝT
      (𝔻T,𝔻T) → return 𝔻T
      _ → undefined -- TypeError
  MCreateSE ℓ e₁ e₂ x₁ x₂ e₃ → do
    τ₁ ← inferSens δ γ e₁ 
    τ₂ ← inferSens δ γ e₂
    case (τ₁,τ₂) of
      (𝕀T ηₘ,𝕀T ηₙ) → do
        σ₃ :* τ₃ ← listen $ inferSens δ (dict [x₁ ↦ 𝕀T ηₘ,x₂ ↦ 𝕀T ηₙ] ⩌ γ) e₃
        let σ₃' = without (pow [x₁,x₂]) σ₃
        tell $ map ((×) $ Sens $ Quantity $ ηₘ × ηₙ) σ₃'
        return $ 𝕄T ℓ UClip ηₘ ηₙ $ anno τ₃
      _ → undefined -- TypeError
  MIndexSE e₁ e₂ e₃ → do
    τ₁ ← inferSens δ γ e₁
    τ₂ ← inferSens δ γ e₂
    τ₃ ← inferSens δ γ e₃
    case (τ₁,τ₂,τ₃) of
      (𝕄T _ℓ _c ηₘ ηₙ τ,𝕀T ηₘ',𝕀T ηₙ') | (ηₘ ≡ ηₘ') ⩓ (ηₙ ≡ ηₙ') → return $ extract τ
      _ → undefined -- TypeError
  MUpdateSE e₁ e₂ e₃ e₄ → do
    τ₁ ← inferSens δ γ e₁
    τ₂ ← inferSens δ γ e₂
    τ₃ ← inferSens δ γ e₃
    τ₄ ← inferSens δ γ e₄
    case (τ₁,τ₂,τ₃,τ₄) of
      (𝕄T ℓ c ηₘ ηₙ τ,𝕀T ηₘ',𝕀T ηₙ',τ') | (ηₘ ≡ ηₘ') ⩓ (ηₙ ≡ ηₙ') ⩓ (extract τ ≡ τ') → return $ 𝕄T ℓ c ηₘ ηₙ τ
      _ → undefined -- TypeError
  MRowsSE e → do
    τ ← inferSens δ γ e
    case τ of
      𝕄T _ℓ _c ηₘ _ηₙ _τ' → return $ ℕˢT ηₘ
      _ → undefined -- Type Error
  MColsSE e → do
    τ ← inferSens δ γ e
    case τ of
      𝕄T _ℓ _c _ηₘ ηₙ _τ' → return $ ℕˢT ηₙ
      _ → undefined -- Type Error
  MClipSE ℓ e → do
    τ ← inferSens δ γ e
    case τ of
      𝕄T ℓ' _c ηₘ ηₙ τ' | extract τ' ≡ 𝔻T → return $ 𝕄T ℓ' (NormClip ℓ) ηₘ ηₙ τ'
      _ → undefined -- Type Error
  MConvertSE e → do
    τ ← inferSens δ γ e
    case τ of
      𝕄T _ℓ (NormClip ℓ) ηₘ ηₙ τ' | extract τ' ≡ 𝔻T → return $ 𝕄T ℓ UClip ηₘ ηₙ $ anno ℝT
      _ → undefined -- Type Error
  MLipGradSE _g e₁ e₂ e₃ → do
    σ₁ :* τ₁ ← listen $ inferSens δ γ e₁
    tell $ map ((×) $ Sens Inf) σ₁
    τ₂ ← inferSens δ γ e₂
    τ₃ ← inferSens δ γ e₃
    case (τ₁,τ₂,τ₃) of
      (𝕄T _ℓ₁ _c₁ ηₘ₁ ηₙ₁ τ₁',𝕄T _ℓ₂ (NormClip ℓ) ηₘ₂ ηₙ₂ τ₂',𝕄T _ℓ₃ _c₃ ηₘ₃ ηₙ₃ τ₃') 
        | meets
          [ extract τ₁' ≡ ℝT
          , extract τ₂' ≡ 𝔻T
          , extract τ₃' ≡ 𝔻T
          , ηₘ₁ ≡ one
          , ηₙ₃ ≡ one
          , ηₙ₁ ≡ ηₙ₂
          , ηₘ₂ ≡ ηₘ₃
          ]
        → return $ 𝕄T ℓ UClip one ηₙ₁ $ anno ℝT
      _ → undefined -- Type Error
  MMapSE e₁ x e₂ → do
    σ₁ :* τ₁ ← listen $ inferSens δ γ e₁
    case τ₁ of
      𝕄T ℓ _c ηₘ ηₙ τ₁' → do
        σ₂ :* τ₂ ← listen $ inferSens δ ((x ↦ extract τ₁') ⩌ γ) e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ deleteView x σ₂
        tell $ map ((×) ς) σ₁
        tell $ map ((×) $ Sens $ Quantity $ ηₘ × ηₙ) σ₂'
        return $ 𝕄T ℓ UClip ηₘ ηₙ $ anno τ₂ 
      _  → undefined -- Type Error
  VarSE x → case γ ⋕? x of
    None → undefined -- Type Error
    Some τ → do
      tell $ x ↦ (Sens $ Quantity one)
      return τ
  LetSE x e₁ e₂ → do
    σ₁ :* τ₁ ← listen $ inferSens δ γ e₁
    σ₂ :* τ₂ ← listen $ inferSens δ ((x ↦ τ₁) ⩌ γ) e₂
    let (ς :* σ₂') = ifNone (zero :* σ₂) $ deleteView x σ₂
    tell $ map ((×) ς) σ₁
    tell σ₂'
    return τ₂
  SFunSE x τ e → do
    let τ' = map normalizeRExp $ extract τ
    σ :* τ'' ← listen $ inferSens δ ((x ↦ τ') ⩌ γ) e
    let (ς :* σ') = ifNone (zero :* σ) $ deleteView x σ
    tell σ'
    return $ anno τ' :⊸: (ς :* anno τ'')
  AppSE e₁ e₂ → do
    τ₁ ← inferSens δ γ e₁
    σ₂ :* τ₂ ← listen $ inferSens δ γ e₂
    case τ₁ of
      τ₁' :⊸: (ς :* τ₂') | extract τ₁' ≡ τ₂ → do
        tell $ map ((×) ς) σ₂
        return $ extract τ₂'
      _ → undefined -- Type Error
  PFunSE ακs xτs e → do
    let xτs' = map (mapSnd (map normalizeRExp ∘ extract)) xτs
        xs = map fst xτs
    σ :* τ ← privToSens $ listen $ inferPriv (dict (map single ακs) ⩌ δ) (dict (map single xτs') ⩌ γ) e
    tell $ map (Sens ∘ truncate Inf ∘ unPriv) $ without (pow xs) σ
    let τps = mapOn xτs' $ \ (x :* τ') → anno τ' :* ifNone zero (σ ⋕? x)
    return $ (ακs :* τps) :⊸⋆: anno τ

privToSens ∷ (Privacy p)
           ⇒ ErrorT (TypeError p) (WriterT (𝕏 ⇰ Priv p RNF) ID) a
           → ErrorT (TypeError p) (WriterT (𝕏 ⇰ Sens RNF) ID) a
privToSens = undefined

sensToPriv ∷ (Privacy p)
           ⇒ ErrorT (TypeError p) (WriterT (𝕏 ⇰ Sens RNF) ID) a
           → ErrorT (TypeError p) (WriterT (𝕏 ⇰ Priv p RNF) ID) a
sensToPriv = undefined

inferPriv ∷ (Privacy p) 
          ⇒ (𝕏 ⇰ Kind) 
          → (𝕏 ⇰ TypePre p RNF) 
          → PExp p 
          → ErrorT (TypeError p) (WriterT (𝕏 ⇰ Priv p RNF) ID) (TypePre p RNF)
inferPriv δ γ eA = case extract eA of
  ReturnPE e → sensToPriv $ inferSens δ γ e
  BindPE x e₁ e₂ → do
    τ₁ ← inferPriv δ γ e₁
    σ₂ :* τ₂ ← listen $ inferPriv δ ((x ↦ τ₁) ⩌ γ) e₂
    let σ₂' = delete x σ₂
    tell σ₂
    return τ₂
  EDLoopPE e₁ e₂ e₃ xs x₁ x₂ e₄ → do
    let xs' = pow xs
    τ₁ ← sensToPriv $ inferSens δ γ e₁
    τ₂ ← sensToPriv $ inferSens δ γ e₂
    τ₃ ← sensToPriv $ inferSens δ γ e₃
    σ₄ :* τ₄ ← listen $ inferPriv δ (dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) e₄
    let σ₄Keep = restrict xs' σ₄
        σ₄KeepMax = joins $ values σ₄Keep
        σ₄Toss = without xs' σ₄
    case (τ₁,τ₂,σ₄KeepMax) of
      (ℝˢT ηᵟ,ℝˢT ηₙ,Priv (Quantity p)) | τ₄ ≡ τ₃ → do 
        tell $ map (Priv ∘ truncate (Quantity $ edLoopBounds ηᵟ ηₙ p)∘ unPriv) σ₄Keep
        tell $ map (Priv ∘ truncate Inf ∘ unPriv) σ₄Toss
        return τ₃
      _ → undefined -- TypeError
  -- GaussPE e₁ e₂ e₃ xs e₄ → do
  --   τ₁ ← sensToPriv $ inferSens δ γ e₁
  --   τ₂ ← sensToPriv $ inferSens δ γ e₂
  --   τ₃ ← sensToPriv $ inferSens δ γ e₃
  --   σ₄ :* τ₄ ← sensToPriv $ listen $ inferSens δ γ e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₃,τ₄,σ₄KeepMax) of
  --     (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,Sens (Quantity ς)) → do
  --       tell $ map (Priv ∘ trruncate (Quantity $ 
  _ → undefined
   
    
    
    
-- infraRed :: PExp -> KEnv → TEnv -> (Type RNF, PEnv)
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
-- iterType :: [Var] -> [Type RNF] -> TEnv  -> Bool
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
-- -- iterU :: [Var] -> [Type] -> TEnv 
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
--           out $ "Type: " ⧺ sho τ
--           out $ "(ε,δ) privacy bound: " ⧺ "∞"
--         ((v,k),(τ,EDPriv ε δ)) → do
--           out $ "\n Var:  " ⧺ v
--           out $ "Type: " ⧺ sho τ
--           out $ "(ε,δ) privacy bound: " ⧺ prettyRNF ε ⧺ ", " ⧺ prettyRNF δ
-- 
--   -- undefined
--     -- putStrLn $ show (sgdTest "xs" "ys")
--     -- putStrLn $ show $ infraRed (sgdTest "xs" "ys") env
--   -- e = λ(x:nat).x
--   -- putStrLn $ show $ infer (FunE "x" NatT (VarE "x")) Map.empty
--   -- putStrLn $ show $ infer (FunE "x" NatT (VarE "y")) Map.empty
