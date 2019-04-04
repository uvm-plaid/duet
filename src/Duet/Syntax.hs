{-# LANGUAGE PartialTypeSignatures #-}
module Duet.Syntax where

import Duet.UVMHS

import Duet.Quantity
import Duet.RNF

data Kind =
    ℕK
  | ℝK
  deriving (Eq,Ord,Show)

instance POrd Kind where
  ℕK ⊑ ℕK = True
  ℕK ⊑ ℝK = True
  ℝK ⊑ ℝK = True
  _ ⊑ _ = False

data Norm = L1 | L2 | LInf
  deriving (Eq,Ord,Show)

data Clip = NormClip Norm | UClip
  deriving (Eq,Ord,Show)

newtype Sens r = Sens { unSens ∷ Quantity r }
  deriving
  (Eq,Ord,Show,Functor
  ,Zero,Plus,Additive
  ,One,Times,Multiplicative
  ,Null,Append,Monoid
  ,Unit,Cross,Prodoid
  ,POrd
  ,Bot,Join,JoinLattice
  ,Top,Meet,MeetLattice
  ,Lattice)

instance (HasPrism (Quantity r) s) ⇒ HasPrism (Sens r) s where
  hasPrism = Prism
    { construct = Sens ∘ construct hasPrism
    , view = view hasPrism ∘ unSens
    }

data PRIV = EPS | ED | RENYI | ZC | TC
  deriving (Eq,Ord,Show)

data PRIV_W (p ∷ PRIV) where
  EPS_W ∷ PRIV_W 'EPS
  ED_W ∷ PRIV_W 'ED
  RENYI_W ∷ PRIV_W 'RENYI
  ZC_W ∷ PRIV_W 'ZC
  TC_W ∷ PRIV_W 'TC

eqPRIV ∷ PRIV_W p₁ → PRIV_W p₂ → 𝑂 (p₁ ≟ p₂)
eqPRIV p₁ p₂ = case (p₁,p₂) of
  (EPS_W,EPS_W) → Some Refl
  (ED_W,ED_W) → Some Refl
  (RENYI_W,RENYI_W) → Some Refl
  (ZC_W,ZC_W) → Some Refl
  (TC_W,TC_W) → Some Refl
  (_,_) → None

stripPRIV ∷ PRIV_W p → PRIV
stripPRIV = \case
  EPS_W → EPS
  ED_W → ED
  RENYI_W → RENYI
  ZC_W → ZC
  TC_W → TC

class PRIV_C (p ∷ PRIV) where
  priv ∷ PRIV_W p

instance PRIV_C 'EPS where priv = EPS_W
instance PRIV_C 'ED where priv = ED_W
instance PRIV_C 'RENYI where priv = RENYI_W
instance PRIV_C 'ZC where priv = ZC_W
instance PRIV_C 'TC where priv = TC_W

data Pr (p ∷ PRIV) r where
  EpsPriv ∷ r → Pr 'EPS r
  EDPriv ∷ r → r → Pr 'ED r
  RenyiPriv ∷ r → r → Pr 'RENYI r
  ZCPriv ∷ r → Pr 'ZC r
  TCPriv ∷ r → r → Pr 'TC r
deriving instance (Eq r) ⇒ Eq (Pr p r)
deriving instance (Ord r) ⇒ Ord (Pr p r)
deriving instance (Show r) ⇒ Show (Pr p r)

instance (Append r,Meet r) ⇒ Append (Pr p r) where
  EpsPriv ε₁ ⧺ EpsPriv ε₂ = EpsPriv $ ε₁ ⧺ ε₂
  EDPriv ε₁ δ₁ ⧺ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⧺ ε₂) (δ₁ ⧺ δ₂)
  RenyiPriv α₁ ε₁ ⧺ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊓ α₂) (ε₁ ⧺ ε₂)
  ZCPriv ρ₁ ⧺ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⧺ ρ₂
  TCPriv ρ₁ ω₁ ⧺ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⧺ ρ₂) (ω₁ ⊓ ω₂)
instance (Join r,Meet r) ⇒ Join (Pr p r) where
  EpsPriv ε₁ ⊔ EpsPriv ε₂ = EpsPriv $ ε₁ ⊔ ε₂
  EDPriv ε₁ δ₁ ⊔ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⊔ ε₂) (δ₁ ⊔ δ₂)
  RenyiPriv α₁ ε₁ ⊔ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊓ α₂) (ε₁ ⊔ ε₂)
  ZCPriv ρ₁ ⊔ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⊔ ρ₂
  TCPriv ρ₁ ω₁ ⊔ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⊔ ρ₂) (ω₁ ⊓ ω₂)

iteratePr ∷ (Times r) ⇒ r → Pr p r → Pr p r
iteratePr x = \case
  EpsPriv ε → EpsPriv $ x × ε
  EDPriv ε δ → EDPriv (x × ε) (x × δ)
  RenyiPriv α ε → RenyiPriv α $ x × ε
  ZCPriv ρ → ZCPriv $ x × ρ
  TCPriv ρ ω → TCPriv (x × ρ) ω

-- JOE TODO: put a link here to the paper
convertRENYIEDPr ∷ (One r,Plus r,Minus r,Divide r,Log r) ⇒ r → Pr 'RENYI r → Pr 'ED r
convertRENYIEDPr δ (RenyiPriv α ε) = EDPriv (ε + log (one / δ) / (α - one)) δ

-- JOE TODO: put a link here to the paper
convertZCEDPr ∷ (One r,Plus r,Minus r,Times r,Divide r,Root r,Log r) ⇒ r → Pr 'ZC r → Pr 'ED r
convertZCEDPr δ (ZCPriv ρ) = EDPriv (ρ + (one + one) × root (ρ × log (one / δ))) δ

-- JOE TODO: put a link here to the paper
convertEPSZCPr ∷ (One r,Plus r,Minus r,Times r,Divide r,Root r,Log r) ⇒ Pr 'EPS r → Pr 'ZC r
convertEPSZCPr (EpsPriv ε) = ZCPriv ((one / (one + one)) × ε × ε)

-- JOE TODO: put a link here to the paper
-- we would like to have a constraint solver for this, because the conversion
-- only makes sense when ⟨δ,ρ,ω⟩ are in a particular relationship
-- convertTCEDPr ∷ (One r,Plus r,Minus r,Divide r,Log r) ⇒ r → Pr 'TC r → Pr 'ED r
-- convertTCEDPr δ (TCPriv ρ ω) = EDPRIV _ _

instance Functor (Pr p) where
  map f (EpsPriv ε) = EpsPriv $ f ε
  map f (EDPriv ε δ) = EDPriv (f ε) (f δ)
  map f (RenyiPriv α ε) = RenyiPriv (f α) (f ε)
  map f (ZCPriv ρ) = ZCPriv $ f ρ
  map f (TCPriv ρ ω) = TCPriv (f ρ) (f ω)

newtype Priv p r = Priv { unPriv ∷ Quantity (Pr p r) }
  deriving
  (Eq,Ord,Show
  ,Null,Append,Monoid
  ,Bot,Join,JoinLattice)
instance Functor (Priv p) where map f = Priv ∘ mapp f ∘ unPriv

onPriv ∷ (Quantity (Pr p₁ r₁) → Quantity (Pr p₂ r₂)) → Priv p₁ r₁ → Priv p₂ r₂
onPriv f = Priv ∘ f ∘ unPriv

instance (HasPrism (Quantity (Pr p r)) s) ⇒ HasPrism (Priv p r) s where
  hasPrism = Prism
    { construct = Priv ∘ construct hasPrism
    , view = view hasPrism ∘ unPriv
    }

data PArgs r where
  PArgs ∷ ∀ (p ∷ PRIV) r. (PRIV_C p) ⇒ 𝐿 (Type r ∧ Priv p r) → PArgs r

instance (Eq r) ⇒ Eq (PArgs r) where
  (==) ∷ PArgs r → PArgs r → 𝔹
  PArgs (xps₁ ∷ 𝐿 (_ ∧ Priv p₁ _)) == PArgs (xps₂ ∷ 𝐿 (_ ∧ Priv p₂ _)) = case eqPRIV (priv @ p₁) (priv @ p₂) of
    Some Refl → xps₁ ≡ xps₂
    None → False
instance (Ord r) ⇒ Ord (PArgs r) where
  compare ∷ PArgs r → PArgs r → Ordering
  compare (PArgs (xps₁ ∷ 𝐿 (_ ∧ Priv p₁ _))) (PArgs (xps₂ ∷ 𝐿 (_ ∧ Priv p₂ _))) = case eqPRIV (priv @ p₁) (priv @ p₂) of
    Some Refl → compare xps₁ xps₂
    None → compare (stripPRIV (priv @ p₁)) (stripPRIV (priv @ p₂))
deriving instance (Show r) ⇒ Show (PArgs r)


data RowsT r = RexpRT r | StarRT deriving (Eq,Ord,Show)

instance Functor RowsT where
  map ∷ (a → b) → RowsT a → RowsT b
  map f = \case
    RexpRT r → RexpRT $ f r
    StarRT → StarRT

data MExp r =
    EmptyME
  | VarME 𝕏
  | ConsME (Type r) (MExp r)
  | AppendME (MExp r) (MExp r)
  | RexpME r (Type r)
  deriving (Eq,Ord,Show)

instance Functor MExp where
  map ∷ (a → b) → MExp a → MExp b
  map f = \case
    EmptyME → EmptyME
    VarME x → VarME x
    ConsME τ m → ConsME (map f τ) (map f m)
    AppendME n m → AppendME (map f n) (map f m)
    RexpME r τ → RexpME (f r) (map f τ)

type TypeSource r = Annotated FullContext (Type r)
data Type r =
    ℕˢT r
  | ℝˢT r
  | ℕT
  | ℝT
  | 𝕀T r
  | 𝔹T
  | 𝕊T
  | 𝔻𝔽T (𝐿 (𝕊 ∧ Type r)) -- TODO: remove
  | BagT Norm Clip (Type r)
  | SetT (Type r)
  | RecordT (𝐿 (𝕊 ∧ Type r))
  | 𝕄T Norm Clip (RowsT r) (MExp r)
  | 𝔻T (Type r)
  | Type r :+: Type r
  | Type r :×: Type r
  | Type r :&: Type r
  | (𝐿 (𝕏 ∧ Kind) ∧ Type r) :⊸: (Sens r ∧ Type r)
  | (𝐿 (𝕏 ∧ Kind) ∧ PArgs r) :⊸⋆: Type r
  | BoxedT (𝕏 ⇰ Sens r) (Type r)
  deriving (Eq,Ord,Show)

instance Functor Type where
  map ∷ (a → b) → Type a → Type b
  map f = \case
    ℕˢT r → ℕˢT $ f r
    ℝˢT r → ℝˢT $ f r
    ℕT → ℕT
    ℝT → ℝT
    𝕀T r → 𝕀T $ f r
    𝔹T → 𝔹T
    𝕊T → 𝕊T
    𝔻𝔽T as → 𝔻𝔽T $ map (mapPair id $ map f) as -- TODO: remove
    BagT ℓ c τ → BagT ℓ c (map f τ)
    SetT τ → SetT (map f τ)
    RecordT as → RecordT $ map (mapPair id $ map f) as
    𝕄T ℓ c r₁ r₂ → 𝕄T ℓ c (map f r₁) (map f r₂)
    𝔻T τ → 𝔻T $ map f τ
    τ₁ :+: τ₂ → map f τ₁ :+: map f τ₂
    τ₁ :×: τ₂ → map f τ₁ :×: map f τ₂
    τ₁ :&: τ₂ → map f τ₁ :&: map f τ₂
    (αks :* τ₁) :⊸: (s :* τ₂) → (αks :* map f τ₁) :⊸: (map f s :*  map f τ₂)
    (αks :* PArgs xτs) :⊸⋆: τ → (αks :* PArgs (map (mapPair (map f) (map f)) xτs)) :⊸⋆: map f τ
    BoxedT σ τ → BoxedT (map (map f) σ) (map f τ)

-----------------
-- Expressions --
-----------------

data Grad = LR
  deriving (Eq,Ord,Show)
makePrettySum ''Grad


type SExpSource (p ∷ PRIV) = Annotated FullContext (SExp p)
-- this is using GADT syntax and extension
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
  MTimesSE ∷ SExpSource p → SExpSource p → SExp p
  DivSE ∷ SExpSource p → SExpSource p → SExp p
  RootSE ∷ SExpSource p → SExp p
  LogSE ∷ SExpSource p → SExp p
  ModSE ∷ SExpSource p → SExpSource p → SExp p
  MinusSE ∷ SExpSource p → SExpSource p → SExp p
  EqualsSE ∷ SExpSource p → SExpSource p → SExp p
  TrueSE ∷ SExp p
  FalseSE ∷ SExp p
  AndSE ∷ SExpSource p → SExpSource p → SExp p
  OrSE ∷ SExpSource p → SExpSource p → SExp p
  -- dataframe operations
  RecordColSE ∷ 𝕊 → SExpSource p → SExp p
  DFPartitionSE ∷ SExpSource p → 𝕊 → SExpSource p → SExp p
  DFMapSE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  DFAddColSE ∷ 𝕊 → SExpSource p → SExp p
  DFJoin1SE ∷ 𝕊 → SExpSource p → SExpSource p → SExp p
  -- matrix operations
  MCreateSE ∷ Norm  → SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  MIndexSE ∷ SExpSource p → SExpSource p → SExpSource p → SExp p
  MUpdateSE ∷ SExpSource p → SExpSource p → SExpSource p → SExpSource p → SExp p
  MFilterSE ∷ SExpSource p → 𝕏 → SExpSource p → SExp p
  MZipSE ∷ SExpSource p → SExpSource p → SExp p
  MRowsSE ∷ SExpSource p → SExp p
  MColsSE ∷ SExpSource p → SExp p
  MTransposeSE ∷ SExpSource p → SExp p
  IdxSE ∷ SExpSource p → SExp p
  MClipSE ∷ Norm → SExpSource p → SExp p
  MConvertSE ∷ SExpSource p → SExp p
  MLipGradSE ∷ Grad → SExpSource p → SExpSource p → SExpSource p → SExp p
  MUnbGradSE ∷ Grad → SExpSource p → SExpSource p → SExpSource p → SExp p
  -- | MUnbGradSE (SExpSource p) (SExpSource p) (SExpSource p)
  MMapSE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  MMapColSE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  MMapCol2SE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  MMapRowSE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  MMap2SE ∷ SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  MFoldSE ∷ SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  JoinSE ∷ SExpSource p → SExpSource p → SExpSource p → SExpSource p → SExp p
  -- CSVtoMatrixSE :: 𝐿 (𝐿 𝕊) → TypeSource RExp → SExp p
  BMapSE ∷ SExpSource p → 𝕏  → SExpSource p → SExp p
  BMap2SE ∷ SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  -- | MMapRowSE (SExpSource p) 𝕏 (SExpSource p)
  -- | MMapRow2SE (SExpSource p) 𝕏 (SExpSource p)
  -- | MFoldRowSE (SExpSource p) (SExpSource p) 𝕏 𝕏 (SExpSource p)
  -- connectives
  -- | SLoopSE (SExpSource p) (SExpSource p) 𝕏 (SExpSource p)
  LoopSE ∷ SExpSource p → SExpSource p → 𝕏 → 𝕏 → SExpSource p → SExp p
  VarSE ∷ 𝕏 → SExp p
  LetSE ∷ 𝕏  → SExpSource p → SExpSource p → SExp p
  SFunSE ∷ 𝐿 (𝕏 ∧ Kind) → 𝕏  → TypeSource RExp → SExpSource p → SExp p
  AppSE ∷ SExpSource p → 𝐿 RExp → SExpSource p → SExp p
  PFunSE ∷ 𝐿 (𝕏 ∧ Kind) → 𝐿 (𝕏 ∧ TypeSource RExp) → PExpSource p → SExp p
  InlSE ∷ TypeSource RExp → SExpSource p → SExp p
  InrSE ∷ TypeSource RExp → SExpSource p → SExp p
  CaseSE ∷ SExpSource p → 𝕏 → SExpSource p → 𝕏 → SExpSource p → SExp p
  TupSE ∷ SExpSource p → SExpSource p → SExp p
  UntupSE ∷ 𝕏 → 𝕏 → SExpSource p → SExpSource p → SExp p
  SetSE ∷ 𝐿 (SExpSource p) → SExp p
  UnionAllSE ∷ SExpSource p → SExp p
  MemberSE ∷ SExpSource p → SExpSource p → SExp p
  PairSE ∷ SExpSource p → SExpSource p → SExp p
  FstSE ∷ SExpSource p → SExp p
  SndSE ∷ SExpSource p → SExp p
  BoxSE ∷ SExpSource p → SExp p
  UnboxSE ∷ SExpSource p → SExp p
  ClipSE ∷ SExpSource p → SExp p
  ConvSE ∷ SExpSource p → SExp p
  DiscFSE ∷ SExpSource p → SExp p
  DiscSE ∷ SExpSource p → SExp p
  CountSE ∷ SExpSource p → SExp p
  ChunksSE ∷ SExpSource p → SExpSource p → SExp p
  Chunks2SE ∷ SExpSource p → SExpSource p → SExpSource p → SExp p
  deriving (Eq,Ord,Show)

data GaussParams (p ∷ PRIV) where
  EDGaussParams ∷ SExpSource 'ED → SExpSource 'ED → GaussParams 'ED
  RenyiGaussParams ∷ SExpSource 'RENYI → SExpSource 'RENYI → GaussParams 'RENYI
  TCGaussParams ∷ SExpSource 'TC → SExpSource 'TC → GaussParams 'TC
  ZCGaussParams ∷ SExpSource 'ZC → GaussParams 'ZC
deriving instance Eq (GaussParams p)
deriving instance Ord (GaussParams p)
deriving instance Show (GaussParams p)

data LaplaceParams (p ∷ PRIV) where
  EpsLaplaceParams ∷ SExpSource 'EPS → LaplaceParams 'EPS
deriving instance Eq (LaplaceParams p)
deriving instance Ord (LaplaceParams p)
deriving instance Show (LaplaceParams p)

data ExponentialParams (p ∷ PRIV) where
  EDExponentialParams ∷ SExpSource 'ED → ExponentialParams 'ED
deriving instance Eq (ExponentialParams p)
deriving instance Ord (ExponentialParams p)
deriving instance Show (ExponentialParams p)

data SVTParams (p ∷ PRIV) where
  EPSSVTParams ∷ SExpSource 'EPS → SVTParams 'EPS
  EDSVTParams ∷ SExpSource 'ED → SVTParams 'ED
deriving instance Eq (SVTParams p)
deriving instance Ord (SVTParams p)
deriving instance Show (SVTParams p)

type PExpSource (p ∷ PRIV) = Annotated FullContext (PExp p)
data PExp (p ∷ PRIV) where
  ReturnPE ∷ SExpSource p → PExp p
  BindPE ∷ 𝕏 → PExpSource p → PExpSource p → PExp p
  AppPE ∷ SExpSource p → 𝐿 RExp → 𝐿 (SExpSource p) → PExp p
  EDLoopPE ∷ SExpSource 'ED → SExpSource 'ED → SExpSource 'ED → 𝐿 𝕏 → 𝕏 → 𝕏 → PExpSource 'ED → PExp 'ED
  LoopPE ∷ SExpSource p → SExpSource p → 𝐿 𝕏 → 𝕏 → 𝕏 → PExpSource p → PExp p
  GaussPE ∷ SExpSource p → GaussParams p → 𝐿 𝕏 → SExpSource p → PExp p
  IfPE ∷ (SExpSource p) → (PExpSource p) → (PExpSource p) → PExp p
  ParallelPE ∷ SExpSource p → SExpSource p → 𝕏 → SExpSource p → 𝕏 → 𝕏 → PExpSource p → PExp p
  MMapPE ∷ SExpSource p → 𝕏 → PExpSource p → PExp p
  PMapColPE ∷ SExpSource p → 𝕏 → PExpSource p → PExp p
  PFldRowsPE ∷ SExpSource p → SExpSource p → SExpSource p → PExp p
  PFldRows2PE ∷ SExpSource p → SExpSource p → SExpSource p → SExpSource p → SExpSource p → PExp p
  MGaussPE ∷ SExpSource p → GaussParams p → 𝐿 𝕏 → SExpSource p → PExp p
  BGaussPE ∷ SExpSource p → GaussParams p → 𝐿 𝕏 → SExpSource p → PExp p
  LaplacePE ∷ SExpSource p → LaplaceParams p → 𝐿 𝕏 → SExpSource p → PExp p
  MLaplacePE ∷ SExpSource p → LaplaceParams p → 𝐿 𝕏 → SExpSource p → PExp p
  ExponentialPE ∷ SExpSource p → ExponentialParams p → SExpSource p → 𝐿 𝕏 → 𝕏  → SExpSource p → PExp p
  SVTPE ∷ SVTParams p → SExpSource p → SExpSource p → 𝐿 𝕏 → SExpSource p → PExp p
  RRespPE ∷ SExpSource p → SExpSource p → 𝐿 𝕏 → SExpSource p → PExp p
  EDSamplePE ∷ SExpSource 'ED → SExpSource 'ED → SExpSource 'ED → 𝕏 → 𝕏 → PExpSource 'ED → PExp 'ED
  RenyiSamplePE ∷ SExpSource 'RENYI → SExpSource 'RENYI → SExpSource 'RENYI → 𝕏 → 𝕏 → PExpSource 'RENYI → PExp 'RENYI
  TCSamplePE ∷ SExpSource 'TC → SExpSource 'TC → SExpSource 'TC → 𝕏 → 𝕏 → PExpSource 'TC → PExp 'TC
  RandNatPE ∷ SExpSource p → SExpSource p → PExp p
  ConvertZCEDPE ∷ SExpSource 'ED → PExpSource 'ZC → PExp 'ED
  ConvertEPSZCPE ∷ PExpSource 'EPS → PExp 'ZC
  ConvertRENYIEDPE ∷ SExpSource 'ED → PExpSource 'RENYI → PExp 'ED

deriving instance Eq (PExp p)
deriving instance Ord (PExp p)
deriving instance Show (PExp p)

instance Pretty (SExp p) where pretty _ = ppLit "SEXP"
instance Pretty (PExp p) where pretty _ = ppLit "PEXP"
