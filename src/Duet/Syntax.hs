module Duet.Syntax where

import UVMHS

import Duet.Quantity
import Duet.Var
import Duet.RExp

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

newtype Sens e = Sens { unSens ∷ Quantity e }
  deriving (Eq,Ord,Show,Functor,Null,Append,Monoid)
makePrettyUnion ''Sens

newtype Priv p e = Priv { unPriv ∷ Quantity (p e) }
  deriving (Eq,Ord,Show,Null,Append,Monoid)
makePrettyUnion ''Priv
instance (Functor p) ⇒ Functor (Priv p) where
  map f (Priv q) = Priv $ mapp f q

type Type p e = Annotated FullContext (TypePre p e)
data TypePre p e =
    ℕˢT e
  | ℝˢT e
  | ℕT
  | ℝT
  | 𝔻T
  | 𝕀T e
  | 𝕄T Norm Clip e e (Type p e)
  | Type p e :+: Type p e
  | Type p e :×: Type p e
  | Type p e :&: Type p e
  | Type p e :⊸: (Sens e ∧ Type p e)
  | (𝐿 (𝕏 ∧ Kind) ∧ 𝐿 (Type p e ∧ Priv p e)) :⊸⋆: Type p e
  deriving (Eq,Ord)
makePrettySum ''TypePre

instance (Functor p) ⇒ Functor (TypePre p) where
  map f = \case
    ℕˢT e → ℕˢT $ f e
    ℝˢT e → ℝˢT $ f e
    ℕT → ℕT
    ℝT → ℝT
    𝔻T → 𝔻T
    𝕀T e → 𝕀T (f e)
    𝕄T ℓ c e₁ e₂ τ → 𝕄T ℓ c (f e₁) (f e₂) $ mapp f τ
    τ₁ :+: τ₂ → mapp f τ₁ :+: mapp f τ₂
    τ₁ :×: τ₂ → mapp f τ₁ :×: mapp f τ₂
    τ₁ :&: τ₂ → mapp f τ₁ :&: mapp f τ₂
    τ₁ :⊸: (s :* τ₂) → mapp f τ₁ :⊸: (map f s :*  mapp f τ₂)
    (αks :* xτs) :⊸⋆: τ → (αks :* map (mapPair (mapp f) (map f)) xτs) :⊸⋆: mapp f τ

-----------------
-- Expressions --
-----------------

data Grad = LR
  deriving (Eq,Ord,Show)
makePrettySum ''Grad

type SExp p = Annotated FullContext (SExpPre p)
data SExpPre p = 
  -- numeric operations
    ℕˢSE ℕ
  | ℝˢSE 𝔻
  | DynSE (SExp p)
  | ℕSE ℕ
  | ℝSE 𝔻
  | RealSE (SExp p)
  | MaxSE (SExp p) (SExp p)
  | MinSE (SExp p) (SExp p)
  | PlusSE (SExp p) (SExp p)
  | TimesSE (SExp p) (SExp p)
  | DivSE (SExp p) (SExp p)
  | RootSE (SExp p)
  | LogSE (SExp p)
  | ModSE (SExp p) (SExp p)
  | MinusSE (SExp p) (SExp p)
  -- matrix operations
  | MCreateSE Norm (SExp p) (SExp p) 𝕏 𝕏 (SExp p)
  | MIndexSE (SExp p) (SExp p) (SExp p)
  | MUpdateSE (SExp p) (SExp p) (SExp p) (SExp p)
  | MRowsSE (SExp p)
  | MColsSE (SExp p)
  | MClipSE Norm (SExp p)
  | MConvertSE (SExp p)
  | MLipGradSE Grad Norm (SExp p) (SExp p) (SExp p)
  | MUnbGradSE Grad (SExp p) (SExp p) (SExp p)
  | MMapSE (SExp p) 𝕏 (SExp p)
  | MMap2SE (SExp p) (SExp p) 𝕏 𝕏 (SExp p)
  | MMapRowSE (SExp p) 𝕏 (SExp p)
  | MMapRow2SE (SExp p) 𝕏 (SExp p)
  | MFoldRowSE (SExp p) (SExp p) 𝕏 𝕏 (SExp p)
  -- connectives
  | IfSE (SExp p) (SExp p) (SExp p)
  | SLoopSE (SExp p) (SExp p) 𝕏 (SExp p)
  | LoopSE (SExp p) (SExp p) 𝕏 (SExp p)
  | VarSE 𝕏
  | LetSE 𝕏 (SExp p) (SExp p)
  | SFunSE 𝕏 (Type p RExp) (SExp p)
  | AppSE (SExp p) (SExp p)
  | PFunSE (𝐿 (𝕏 ∧ Kind)) (𝐿 (𝕏 ∧ Type p RExp)) (PExp p)
  | InlSE (Type p RExp) (SExp p)
  | InrSE (Type p RExp) (SExp p)
  | CaseSE (SExp p) 𝕏 (SExp p) 𝕏 (SExp p)
  | TupSE (SExp p) (SExp p)
  | UntupSE 𝕏 𝕏 (SExp p) (SExp p)
  | PairSE (SExp p) (SExp p)
  | FstSE (SExp p)
  | SndSE (SExp p)
deriving instance (∀ a. Eq a ⇒ Eq (p a)) ⇒ Eq (SExpPre p)
deriving instance (∀ a. Eq a ⇒ Eq (p a),∀ a. Ord a ⇒ Ord (p a)) ⇒ Ord (SExpPre p)

type PExp p = Annotated FullContext (PExpPre p)
data PExpPre p =
    ReturnPE (SExp p)
  | BindPE 𝕏 (PExp p) (PExp p)
  | AppPE (𝐿 RExp) (SExp p) (𝐿 𝕏)
  | LoopPE (SExp p) (SExp p) (SExp p) (𝐿 𝕏) 𝕏 𝕏 (PExp p)
  | GaussPE (SExp p) (SExp p) (SExp p) (𝐿 𝕏) (SExp p)
  | MGaussPE (SExp p) (SExp p) (SExp p) (𝐿 𝕏) (SExp p)
  | PLaplaceE (SExp p) (SExp p) (𝐿 𝕏) (SExp p)
  | PExponentialE (SExp p) (SExp p) (SExp p) 𝕏 (SExp p)
  | PRRespE (SExp p) (SExp p) (𝐿 𝕏) (SExp p)
  | PSampleE (SExp p) 𝕏 𝕏 𝕏 𝕏 (PExp p)
  | PRandNatE (SExp p) (SExp p)
deriving instance (∀ a. Eq a ⇒ Eq (p a)) ⇒ Eq (PExpPre p)
deriving instance (∀ a. Eq a ⇒ Eq (p a),∀ a. Ord a ⇒ Ord (p a)) ⇒ Ord (PExpPre p)

makePrettySum ''SExpPre
makePrettySum ''PExpPre
