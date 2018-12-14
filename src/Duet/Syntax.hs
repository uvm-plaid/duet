module Duet.Syntax where

import UVMHS

import Duet.Quantity
import Duet.Var
import Duet.RExp
import Duet.AddToUVMHS

type Kind = Annotated FullContext KindPre
data KindPre =
    ℕK
  | ℝK
  deriving (Eq,Ord,Show)
makePrettySum ''KindPre

data Norm = L1 | L2 | LInf
  deriving (Eq,Ord,Show)
makePrettySum ''Norm

data Clip = NormClip Norm | UClip
  deriving (Eq,Ord,Show)
makePrettySum ''Clip

newtype Sens r = Sens { unSens ∷ Quantity r }
  deriving 
  (Eq,Ord,Show,Functor
  ,Additive,Multiplicative
  ,Null,Append,Monoid
  ,Bot,Join,JoinLattice
  ,Top,Meet,MeetLattice)
makePrettyUnion ''Sens

instance (HasPrism (Quantity r) s) ⇒ HasPrism (Sens r) s where
  hasPrism = Prism
    { construct = Sens ∘ construct hasPrism
    , view = view hasPrism ∘ unSens
    }

data PRIV = EPS | ED | RENYI | ZC | TC
data PRIV_W (p ∷ PRIV) where
  EPS_W ∷ PRIV_W 'EPS
  ED_W ∷ PRIV_W 'ED
  RENYI_W ∷ PRIV_W 'RENYI
  ZC_W ∷ PRIV_W 'ZC
  TC_W ∷ PRIV_W 'TC
class PRIV_C (p ∷ PRIV) where priv ∷ PRIV_W p

data Pr (p ∷ PRIV) r where
  EpsPriv ∷ r → Pr 'EPS r
  EDPriv ∷ r → r → Pr 'ED r
  RenyiPriv ∷ r → r → Pr 'RENYI r
  ZCPriv ∷ r → Pr 'ZC r
  TCPriv ∷ r → r → Pr 'TC r
deriving instance (Eq r) ⇒ Eq (Pr p r)
deriving instance (Ord r) ⇒ Ord (Pr p r)
deriving instance (Show r) ⇒ Show (Pr p r)

instance (Pretty r) ⇒ Pretty (Pr p r) where
  pretty = \case
    EpsPriv r → pretty r
    EDPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂
    RenyiPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂
    ZCPriv r  → pretty r
    TCPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂

-- instance (Additive r,PRIV_C p) ⇒ Additive (Pr p r) where
--   zero = case priv @ p of
--     EPS_W → EpsPriv zero
--     ED_W → EDPriv zero zero
--     RENYI_W → RenyiPriv zero zero
--     ZC_W → ZCPriv zero
--     TC_W → TCPriv zero
--   EpsPriv ε₁ + EpsPriv ε₂ = EpsPriv $ ε₁ + ε₂
--   EDPriv ε₁ δ₁ + EDPriv ε₂ δ₂ = EDPriv (ε₁ + ε₂) (δ₁ + δ₂)
--   RenyiPriv α₁ ε₁ + RenyiPriv _α₂ ε₂ = RenyiPriv α₁ (ε₁ + ε₂)
--   ZCPriv ρ₁ + ZCPriv ρ₂ = ZCPriv $ ρ₁ + ρ₂
--   TCPriv ψ₁ + TCPriv ψ₂ = TCPriv $ ψ₁ + ψ₂
-- instance (Null r,PRIV_C p) ⇒ Null (Pr p r) where
--   null = case priv @ p of
--     EPS_W → EpsPriv null
--     ED_W → EDPriv null null
--     RENYI_W → RenyiPriv null null
--     ZC_W → ZCPriv null
--     TC_W → TCPriv null
instance (Append r,Meet r) ⇒ Append (Pr p r) where
  EpsPriv ε₁ ⧺ EpsPriv ε₂ = EpsPriv $ ε₁ ⧺ ε₂
  EDPriv ε₁ δ₁ ⧺ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⧺ ε₂) (δ₁ ⧺ δ₂)
  RenyiPriv α₁ ε₁ ⧺ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊓ α₂) (ε₁ ⧺ ε₂)
  ZCPriv ρ₁ ⧺ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⧺ ρ₂
  TCPriv ρ₁ ω₁ ⧺ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⧺ ρ₂) (ω₁ ⊓ ω₂)
-- instance (Monoid r,PRIV_C p) ⇒ Monoid (Pr p r)
-- instance (Bot r,PRIV_C p) ⇒ Bot (Pr p r) where
--   bot = case priv @ p of
--     EPS_W → EpsPriv bot
--     ED_W → EDPriv bot bot
--     RENYI_W → RenyiPriv bot bot
--     ZC_W → ZCPriv bot
--     TC_W → TCPriv bot
instance (Join r,Meet r) ⇒ Join (Pr p r) where
  EpsPriv ε₁ ⊔ EpsPriv ε₂ = EpsPriv $ ε₁ ⊔ ε₂
  EDPriv ε₁ δ₁ ⊔ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⊔ ε₂) (δ₁ ⊔ δ₂)
  RenyiPriv α₁ ε₁ ⊔ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊓ α₂) (ε₁ ⊔ ε₂)
  ZCPriv ρ₁ ⊔ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⊔ ρ₂
  TCPriv ρ₁ ω₁ ⊔ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⊔ ρ₂) (ω₁ ⊓ ω₂)
-- instance (JoinLattice r,PRIV_C p) ⇒ JoinLattice (Pr p r)

instance Functor (Pr p) where
  map f (EpsPriv ε) = EpsPriv $ f ε
  map f (EDPriv ε δ) = EDPriv (f ε) (f δ)
  map f (RenyiPriv α ε) = RenyiPriv (f α) (f ε)
  map f (ZCPriv ρ) = ZCPriv $ f ρ
  map f (TCPriv ρ ω) = TCPriv (f ρ) (f ω)

newtype Priv p r = Priv { unPriv ∷ Quantity (Pr p r) }
  deriving (Eq,Ord,Show,{-Additive,-}Null,Append,Monoid,Bot,Join,JoinLattice)
instance Functor (Priv p) where map f = Priv ∘ mapp f ∘ unPriv
makePrettyUnion ''Priv

instance (HasPrism (Quantity (Pr p r)) s) ⇒ HasPrism (Priv p r) s where
  hasPrism = Prism
    { construct = Priv ∘ construct hasPrism
    , view = view hasPrism ∘ unPriv
    }

type TypeSource (p ∷ PRIV) r = Annotated FullContext (Type p r)
data Type (p ∷ PRIV) r =
    ℕˢT r
  | ℝˢT r
  | ℕT
  | ℝT
  | 𝔻T
  | 𝕀T r
  | 𝕄T Norm Clip r r (Type p r)
  | Type p r :+: Type p r
  | Type p r :×: Type p r
  | Type p r :&: Type p r
  | Type p r :⊸: (Sens r ∧ Type p r)
  | (𝐿 (𝕏 ∧ Kind) ∧ 𝐿 (Type p r ∧ Priv p r)) :⊸⋆: Type p r
  deriving (Eq,Ord)
makePrettySum ''Type

instance Functor (Type p) where
  map f = \case
    ℕˢT r → ℕˢT $ f r
    ℝˢT r → ℝˢT $ f r
    ℕT → ℕT
    ℝT → ℝT
    𝔻T → 𝔻T
    𝕀T r → 𝕀T (f r)
    𝕄T ℓ c r₁ r₂ τ → 𝕄T ℓ c (f r₁) (f r₂) $ map f τ
    τ₁ :+: τ₂ → map f τ₁ :+: map f τ₂
    τ₁ :×: τ₂ → map f τ₁ :×: map f τ₂
    τ₁ :&: τ₂ → map f τ₁ :&: map f τ₂
    τ₁ :⊸: (s :* τ₂) → map f τ₁ :⊸: (map f s :*  map f τ₂)
    (αks :* xτs) :⊸⋆: τ → (αks :* map (mapPair (map f) (map f)) xτs) :⊸⋆: map f τ

-----------------
-- Expressions --
-----------------

data Grad = LR
  deriving (Eq,Ord,Show)
makePrettySum ''Grad

type SExpSource (p ∷ PRIV) = Annotated FullContext (SExp p)
data SExp (p ∷ PRIV) where
  -- numeric operations
  ℕˢSE ∷ ℕ → SExp p
  ℝˢSE ∷ 𝔻 → SExp p
  DynSE ∷ SExpSource p → SExp p
  ℕSE ∷ ℕ → SExp p
  ℝSE ∷ 𝔻 → SExp p
  RealSE ∷ SExpSource p → SExp p
  MaxSE ∷ SExpSource p → SExpSource p → SExp p
  MinSE ∷ SExpSource p → SExpSource p → SExp p
  PlusSE ∷ SExpSource p → SExpSource p → SExp p
  TimesSE ∷ SExpSource p → SExpSource p → SExp p
  DivSE ∷ SExpSource p → SExpSource p → SExp p
  RootSE ∷ SExpSource p → SExp p
  LogSE ∷ SExpSource p → SExp p
  ModSE ∷ SExpSource p → SExpSource p → SExp p
  MinusSE ∷ SExpSource p → SExpSource p → SExp p
  -- matrix operations
  MCreateSE ∷ Norm  → SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  MIndexSE ∷ SExpSource p → SExpSource p → SExpSource p → SExp p
  MUpdateSE ∷ SExpSource p → SExpSource p → SExpSource p → SExpSource p → SExp p
  MRowsSE ∷ SExpSource p → SExp p
  MColsSE ∷ SExpSource p → SExp p
  MClipSE ∷ Norm → SExpSource p → SExp p
  MConvertSE ∷ SExpSource p → SExp p
  MLipGradSE ∷ Grad → SExpSource p → SExpSource p → SExpSource p → SExp p
  -- | MUnbGradSE (SExpSource p) (SExpSource p) (SExpSource p)
  MMapSE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  MMap2SE ∷ SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  -- | MMapRowSE (SExpSource p) 𝕏 (SExpSource p)
  -- | MMapRow2SE (SExpSource p) 𝕏 (SExpSource p)
  -- | MFoldRowSE (SExpSource p) (SExpSource p) 𝕏 𝕏 (SExpSource p)
  -- connectives
  -- | IfSE (SExpSource p) (SExpSource p) (SExpSource p)
  -- | SLoopSE (SExpSource p) (SExpSource p) 𝕏 (SExpSource p)
  -- | LoopSE (SExpSource p) (SExpSource p) 𝕏 (SExpSource p)
  VarSE ∷ 𝕏 → SExp p
  LetSE ∷ 𝕏  → SExpSource p → SExpSource p → SExp p
  SFunSE ∷ 𝕏  → TypeSource p RExp → SExpSource p → SExp p
  AppSE ∷ SExpSource p → SExpSource p → SExp p
  PFunSE ∷ 𝐿 (𝕏 ∧ Kind) → 𝐿 (𝕏 ∧ TypeSource p RExp) → PExpSource p → SExp p
  InlSE ∷ TypeSource p RExp → SExpSource p → SExp p
  InrSE ∷ TypeSource p RExp → SExpSource p → SExp p
  CaseSE ∷ SExpSource p → 𝕏 → SExpSource p → 𝕏 → SExpSource p → SExp p
  TupSE ∷ SExpSource p → SExpSource p → SExp p
  UntupSE ∷ 𝕏 → 𝕏 → SExpSource p → SExpSource p → SExp p
  PairSE ∷ SExpSource p → SExpSource p → SExp p
  FstSE ∷ SExpSource p → SExp p
  SndSE ∷ SExpSource p → SExp p
  deriving (Eq,Ord)

data GaussParams (p ∷ PRIV) where
  EDGaussParams ∷ SExpSource 'ED → SExpSource 'ED → GaussParams 'ED
  RenyiGaussParams ∷ SExpSource 'RENYI → SExpSource 'RENYI → GaussParams 'RENYI
  ZCGaussParams ∷ SExpSource 'ZC → SExpSource 'ZC → GaussParams 'ZC
deriving instance Eq (GaussParams p)
deriving instance Ord (GaussParams p)

data LaplaceParams (p ∷ PRIV) where
  EpsLaplaceParams ∷ SExpSource 'EPS → LaplaceParams 'EPS
  EDLaplaceParams ∷ SExpSource 'ED → SExpSource 'ED → LaplaceParams 'ED
  RenyiLaplaceParams ∷ SExpSource 'RENYI → SExpSource 'RENYI → LaplaceParams 'RENYI
deriving instance Eq (LaplaceParams p)
deriving instance Ord (LaplaceParams p)

type PExpSource (p ∷ PRIV) = Annotated FullContext (PExp p)
data PExp (p ∷ PRIV) where
  ReturnPE ∷ SExpSource p → PExp p
  BindPE ∷ 𝕏 → PExpSource p → PExpSource p → PExp p
  AppPE ∷ 𝐿 RExp → SExpSource p → 𝐿 𝕏 → PExp p
  EDLoopPE ∷ SExpSource 'ED → SExpSource 'ED → SExpSource 'ED → 𝐿 𝕏 → 𝕏 → 𝕏 → PExpSource 'ED → PExp 'ED
  LoopPE ∷ SExpSource p → SExpSource p → 𝐿 𝕏 → 𝕏 → 𝕏 → PExpSource p → PExp p
  GaussPE ∷ SExpSource p → GaussParams p → 𝐿 𝕏 → SExpSource p → PExp p
  MGaussPE ∷ SExpSource p → GaussParams p → 𝐿 𝕏 → SExpSource p → PExp p
  PLaplaceE ∷ SExpSource p → LaplaceParams p → 𝐿 𝕏 → SExpSource p → PExp p
  -- PExponentialE ∷ SExpSource p → SExpSource p → SExpSource p → 𝕏  → SExpSource p → PExp p
  -- PRRespE ∷ SExpSource p → SExpSource p → 𝐿 𝕏 → SExpSource p → PExp p
  PSampleE ∷ SExpSource p → 𝕏 → 𝕏 → 𝕏 → 𝕏 → PExpSource p → PExp p
  PRandNatE ∷ SExpSource p → SExpSource p → PExp p
deriving instance Eq (PExp p)
deriving instance Ord (PExp p)

instance Pretty (SExp p) where pretty _ = ppLit "SEXP"
instance Pretty (PExp p) where pretty _ = ppLit "PEXP"
