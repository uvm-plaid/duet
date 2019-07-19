module Duet.Interpreter where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax

-- external libraries
import System.Random.MWC
import Data.Random.Normal

type Env = 𝕏 ⇰ Val
type DuetVector a = 𝐿 a
type Model = DuetVector 𝔻


-- | Defining Val algebraic data type
data Val =
  NatV ℕ
  | RealV 𝔻
  | PairV (Val ∧ Val)
  | StrV 𝕊
  | BoolV 𝔹
  | ListV (𝐿 Val)
  | SetV (𝑃 Val)
  | SFunV 𝕏 (ExPriv SExp) Env  -- See UVMHS.Core.Init for definition of Ex
  | PFunV (𝐿 𝕏) (ExPriv PExp) Env
  | MatrixV (ExMatrix Val)
  deriving (Eq,Ord,Show)

instance Eq (Sℕ32 n) where
  TRUSTME_Sℕ32 n₁ == TRUSTME_Sℕ32 n₂ = n₁ ≡ n₂
instance (Eq a) ⇒ Eq (Vᴍ m n a) where
  Vᴍ m₁ n₁ a₁ == Vᴍ m₂ n₂ a₂ = (m₁ == m₂) ⩓ (n₁ == n₂) ⩓ (a₁ == a₂)
data ExMatrix a where
  ExMatrix ∷ (Rℕ m,Rℕ n) ⇒ Vᴍ m n a -> ExMatrix a
instance Functor ExMatrix where
  map f (ExMatrix m) = ExMatrix $ map f m
instance (Eq a) ⇒ Eq (ExMatrix a) where
  ExMatrix (Vᴍ _ _ a₁) == ExMatrix (Vᴍ _ _ a₂) = a₁ ≡ a₂
instance (Ord a) ⇒ Ord (ExMatrix a) where
  compare (ExMatrix xs₁) (ExMatrix xs₂) = compare (xlist2 xs₁) (xlist2 xs₂)
instance (Show a) ⇒ Show (ExMatrix a) where
  show (ExMatrix xs) = show $ xlist2 xs

instance Pretty Val where
  pretty = \case
    NatV n → pretty n
    RealV d → pretty d
    StrV s → pretty s
    BoolV b → pretty b
    ListV l → pretty l
    SetV s → pretty s
    PairV a → pretty a
    SFunV _x _se _e → ppKeyPun "<sλ value>"
    PFunV _xs _pe _e → ppKeyPun "<pλ value>"
    MatrixV m → ppVertical $ list [ppText "MATRIX VALUE:",pretty m]

instance (Pretty a) ⇒ Pretty (ExMatrix a) where
  pretty (ExMatrix a) = pretty a

instance (Pretty a) ⇒ Pretty (Vᴍ m n a) where
  pretty m = pretty $ xlist2 m

-- this could be moved to Syntax.hs, and PArgs r (and its Eq and Ord instances)
-- could be derived using this type
newtype ExPriv (e ∷ PRIV → ★) = ExPriv { unExPriv ∷ Ex_C PRIV_C e }

deriving instance (∀ p. Show (e p)) ⇒ Show (ExPriv e)

instance (∀ p. Eq (e p)) ⇒ Eq (ExPriv e) where
  ExPriv (Ex_C (e₁ ∷ e p₁)) ==  ExPriv (Ex_C (e₂ ∷ e p₂)) = case eqPRIV (priv @ p₁) (priv @ p₂) of
    Some (Refl ∷ p₁ ≟ p₂) → (e₁ ∷ e p₁) ≡ (e₂ ∷ e p₁)
    None → False

instance (∀ p. Eq (e p),∀ p. Ord (e p)) ⇒ Ord (ExPriv e) where
  ExPriv (Ex_C (e₁ ∷ e p₁)) `compare`  ExPriv (Ex_C (e₂ ∷ e p₂)) = case eqPRIV (priv @ p₁) (priv @ p₂) of
    Some (Refl ∷ p₁ ≟ p₂) → (e₁ ∷ e p₁) ⋚ (e₂ ∷ e p₁)
    None → stripPRIV (priv @ p₁) ⋚ stripPRIV (priv @ p₂)

ex2m :: ExMatrix a → (∀ m n. Vᴍ m n a → b) → b
ex2m (ExMatrix xs) f = f xs

n2i :: ∀ n. Rℕ n ⇒ Sℕ32 n → ℕ → 𝕀32 n
n2i s n = case (d𝕚 s (𝕟32 n)) of
  Some x → x
  None → error "index out of bounds"

-- TODO: eventually add this to UVMHS
minElem ::  Ord b => (a → b) → 𝐿 a → a
minElem f Nil = error "minElem on empty list"
minElem f (x:&xs) = fold x (\ x₁ x₂ → case f x₁ < f x₂ of { True → x₁ ; False → x₂ }) xs

minElemPairs :: Ord b => 𝐿 (a ∧ b) → a ∧ b
minElemPairs = minElem snd

norm_2 :: Vᴍ 1 m 𝔻 → 𝔻
norm_2 = root ∘ sum ∘ xmap (\x → x×x)

cols :: ExMatrix a → ℕ
cols (ExMatrix xs) = nat $ unSℕ32 $ xcols xs

rows :: ExMatrix a → ℕ
rows (ExMatrix xs) = nat $ unSℕ32 $ xrows xs

scols :: ∀ n a. Rℕ n ⇒ ExMatrix a → Sℕ32 n
scols (ExMatrix (xs ∷ Vᴍ m' n' a)) = case compareTℕ @ n @ n' of
  Some Refl → xcols xs

srows :: ∀ n a. Rℕ n ⇒ ExMatrix a → Sℕ32 n
srows (ExMatrix (xs ∷ Vᴍ m' n' a)) = case compareTℕ @ n @ m' of
  Some Refl → xrows xs

tr :: ExMatrix 𝔻 → ExMatrix 𝔻
tr (ExMatrix xs) = ExMatrix $ xtranspose xs

mindex :: ∀ m n a. (Rℕ m,Rℕ n) ⇒ ExMatrix a → 𝕀32 m → 𝕀32 n → a
mindex (ExMatrix (xs ∷ Vᴍ m' n' a)) i j = case (compareTℕ @ n @ n',compareTℕ @ m @ m') of
  (Some Refl, Some Refl) → xs 𝄪 (i,j)

boolCheck :: 𝔹 → 𝔻
boolCheck True = 1.0
boolCheck False = 0.0

flatten :: ExMatrix a → DuetVector a
flatten m = fold Nil (⧺) (toRows m)

(<>) :: ExMatrix 𝔻 → ExMatrix 𝔻 → ExMatrix 𝔻
(<>) (ExMatrix a) (ExMatrix b) =
  let b' = (xbp b) in
  let b'' = matrix (xcols a) (xcols b) $ \ i j → b' 𝄪 ((n2i (xrows b) (nat (un𝕀32 i))),j) in
    ExMatrix $ xproduct (xvirt (xbp a)) b''

xgradient ∷ ∀ m n. Vᴍ 1 n 𝔻 → Vᴍ m n 𝔻 → Vᴍ m 1 𝔻 → Vᴍ 1 n 𝔻
xgradient θ xs ys = unID $ do
  let θ' ∷ Vᴍ 1 n 𝔻
      θ' = {- xvirt $ xup -} θ
  let exponent ∷ Vᴍ m 1 𝔻
      exponent = xvirt $ xup $ xtranspose (θ' ✖ xtranspose xs) × ys
  let scaled ∷ Vᴍ m 1 𝔻
      scaled = ys × xmap (\ x → 1.0 / (exp x + 1.0)) exponent
  let gradSum ∷ Vᴍ 1 n 𝔻
      gradSum = xtranspose scaled ✖ xs
  let r = neg $ dbl $ unSℕ32 $ xrows xs
  let avgGrad ∷ Vᴍ 1 n 𝔻
      avgGrad = xvirt $ xup $ xmap (\ x → x / r) gradSum
  return avgGrad

scale :: 𝔻 → DuetVector 𝔻 → Model
scale r v = map (× r) v

mscale :: 𝔻 → ExMatrix 𝔻 → ExMatrix 𝔻
mscale r (ExMatrix m) = ExMatrix $ xmap (× r) m

-- build the rows of a matrix
fromRows :: 𝐿 (𝐿 a) → ExMatrix a
fromRows Nil = ExMatrix $ matrix (s𝕟32 @ 0) (s𝕟32 @ 0) (\i j -> undefined)
fromRows ls = xb ls $ \ xs → ExMatrix (xvirt xs)

-- extracts the rows of a matrix as a list of vectors
toRows :: ExMatrix a → 𝐿 (𝐿 a)
toRows (ExMatrix m) = xlist2 m

(+++) :: (Plus a) => ExMatrix a → ExMatrix a → ExMatrix a
(+++) (ExMatrix a) (ExMatrix b) =
  let b' = matrix (xrows a) (xcols a) $ \ i j → b 𝄪 ((n2i (xrows b) (nat (un𝕀32 i))),(n2i (xcols b) (nat (un𝕀32 j)))) in
  ExMatrix $ xmap2 (+) a b'

(-/) :: (Minus a) => ExMatrix a → ExMatrix a → ExMatrix a
(-/) (ExMatrix a) (ExMatrix b) =
  let b' = matrix (xrows a) (xcols a) $ \ i j → b 𝄪 ((n2i (xrows b) (nat (un𝕀32 i))),(n2i (xcols b) (nat (un𝕀32 j)))) in
  ExMatrix $ xmap2 (-) a b'

urv :: Val → 𝔻
urv x = case x of
  RealV d → d
  _ → error $ "unpack real val failed" ⧺ pprender x

arsinh ∷ 𝔻 → 𝔻
arsinh x = log $ x + (root $ (x × x) + 1.0)

-- Nat, 1-row matrix (really a row), list of one row matrices, and so on
-- mostly because matrices are the only thing we can index
joinMatch₁ ∷ ℕ → ExMatrix Val → 𝐿 (ExMatrix Val) → ℕ → 𝐿 Val
joinMatch₁ n₁ row₁ Nil n₂ = Nil
joinMatch₁ n₁ (ExMatrix row₁) ((ExMatrix row₂):&rows₂) n₂ =
  case ((indexVᴍ (n2i (xrows row₁) 0) (n2i (xcols row₁) n₁) row₁) ≡ (indexVᴍ (n2i (xrows row₂) 0) (n2i (xcols row₂) n₂) row₂)) of
    True →  (flatten (ExMatrix row₁)) ⧺ (flatten (ExMatrix row₂))
    False → joinMatch₁ n₁ (ExMatrix row₁) rows₂ n₂

schemaToTypes :: MExp r → 𝐿 (Type r)
schemaToTypes me = case me of
  (ConsME τ me') → schemaToTypes₁ me
  _ → error "schemaToTypes expects a ConsME"

schemaToTypes₁ :: MExp r → 𝐿 (Type r)
schemaToTypes₁ me = case me of
  (ConsME τ me') → τ :& schemaToTypes₁ me'
  EmptyME → Nil
  _ → error "schemaToTypes: unexpected MExp within ConsME"

rowToDFRow :: (Pretty r) ⇒ 𝐿 (Type r) → 𝐿 𝕊 → 𝐿 Val
rowToDFRow Nil Nil = Nil
rowToDFRow (τ:&τs) (s:&ss) = case τ of
  ℕT → NatV (read𝕊 s) :& rowToDFRow τs ss
  ℕˢT _ → NatV (read𝕊 s) :& rowToDFRow τs ss
  ℝT → RealV (read𝕊 s) :& rowToDFRow τs ss
  ℝˢT _ → RealV (read𝕊 s) :& rowToDFRow τs ss
  𝕊T → StrV (read𝕊 s) :& rowToDFRow τs ss
  𝔻T τ' → rowToDFRow (τ':&τs) (s:&ss)
  _ → error $ "rowToDFRow: type is currently not supported" ⧺ pprender τ
rowToDFRow y z = error $ "rowToDFRow: arguments length mismatch" ⧺ (pprender (y :* z))

pairList ∷ 𝐿 Val → Val
pairList (v₁ :& v₂ :& Nil) = PairV (v₁ :* v₂)
pairList _ = error "pairList: tried to build pair out of list with incorrect structure"

csvToPairSet ∷ (Pretty r) ⇒ 𝐿 (𝐿 𝕊) → 𝐿 (Type r) → Val
csvToPairSet sss τs =
  let csvList ∷ 𝐿 (𝐿 Val) = map (rowToDFRow τs) sss
  in SetV $ pow $ map pairList csvList

csvToDF ∷ (Pretty r) ⇒ 𝐿 (𝐿 𝕊) → 𝐿 (Type r) → Val
csvToDF sss τs =
  let csvList ∷ 𝐿 (𝐿 Val) = map (rowToDFRow τs) sss
  in MatrixV $ fromRows csvList

partition ∷ 𝐿 Val → 𝐿 (Val ∧ 𝐿 (𝐿 Val)) → 𝐿 (Val ∧ 𝐿 (𝐿 Val))
partition _ Nil = Nil
partition Nil _ = Nil
partition (k:&ks) (v:&vs) = (k :* partition₁ k (v:&vs)) :& partition ks (v:&vs)

partition₁ ∷ Val → 𝐿 (Val ∧ 𝐿 (𝐿 Val)) → 𝐿 (𝐿 Val)
partition₁ k Nil = Nil
partition₁ k ((val:*llvals):&vs) = case k ≡ val of
  True → llvals ⧺ partition₁ k vs
  False → partition₁ k vs

shapedExMatrix ∷ ∀ m n a. (Rℕ m,Rℕ n) ⇒ Sℕ32 m → Sℕ32 n → ExMatrix a → 𝑂 (Vᴍ m n a)
shapedExMatrix m n (ExMatrix (xs ∷ Vᴍ m' n' a)) = do
  Refl ← compareTℕ @ m @ m'
  Refl ← compareTℕ @ n @ n'
  return xs

-- | Evaluates an expression from the sensitivity language
seval ∷ (PRIV_C p) ⇒ (Env) → (SExp p) → (Val)

-- literals
seval _ (ℕSE n)        = NatV n
seval _ (ℝSE n)        = RealV n
seval _ (ℝˢSE n)       = RealV n
seval _ (ℕˢSE n)       = NatV n
seval env (RealSE e) =
  case (seval env $ extract e) of
    (NatV n) → RealV $ dbl n
    (RealV n) → RealV n
    a → error $ "realSE: unknown type " ⧺ (pprender a) ⧺ " in " ⧺ (pprender e)

-- variables
seval env (VarSE x) = env ⋕! x

seval env (LetSE x e₁ e₂) = do
  let v₁ = seval env (extract e₁) in
    seval ((x ↦ v₁) ⩌ env) (extract e₂)

-- arithmetic
seval env (PlusSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → MatrixV $ map RealV ( (map urv v₁) +++ (map urv v₂) )
    (RealV v₁, RealV v₂) → RealV (v₁ + v₂)
    (NatV v₁, NatV v₂) → NatV (v₁ + v₂)
    (a, b) → error $ "No pattern in + for " ⧺ (show𝕊 (a, b))

seval env (MinusSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → MatrixV $ map RealV ( (map urv v₁) -/ (map urv v₂) )
    (RealV v₁, RealV v₂) → RealV (v₁ - v₂)
    (NatV v₁, NatV v₂) → NatV (v₁ - v₂)
    (a, b) → error $ "No pattern for " ⧺ (show𝕊 (a, b))

seval env (TimesSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → MatrixV $ map RealV ((map urv v₁) <> (map urv v₂))
    (RealV v₁, MatrixV v₂) → MatrixV $ map RealV (mscale v₁ (map urv v₂))
    (RealV v₁, RealV v₂) → RealV (v₁ × v₂)
    (NatV v₁, NatV v₂) → NatV (v₁ × v₂)
    (a, b) → error $ "No pattern for " ⧺ (show𝕊 (a, b))

seval env (DivSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (RealV v₁, RealV v₂) → RealV (v₁ / v₂)
    (a, b) → error $ "No pattern for " ⧺ (show𝕊 (a, b))

-- matrix operations
seval env (MRowsSE e) =
  case (seval env (extract e)) of
    (MatrixV v) →
      NatV $ nat $ rows v

seval env (MColsSE e) =
  case (seval env (extract e)) of
    (MatrixV v) →
      NatV $ nat $ cols v

seval env (MIndexSE e₁ e₂ e₃) =
  case (seval env (extract e₁),seval env (extract e₂),seval env (extract e₃)) of
    (MatrixV (ExMatrix v), NatV n₁, NatV n₂) →
      case (d𝕚 (xrows v) (natΩ32 n₁),d𝕚 (xcols v) (natΩ32 n₂)) of
        (Some (n₁' ∷ 𝕀32 m),Some (n₂' ∷ 𝕀32 n))  → v 𝄪 (n₁',n₂')
        _ → error "matrix index out of bounds"
    (a, b, c) → error $ "Mindex fail: " ⧺ (pprender (e₁ :* a :* b :* c))

-- clip operation for only L2 norm
seval env (MClipSE norm e) =
  case seval env $ extract e of
    MatrixV (ExMatrix m) →
      MatrixV
      $ ExMatrix
      $ xmap RealV
      $ xmeld (xcols m)
      $ xmap normalize
      $ xsplit
      $ xmap urv m
    _ → error $ "cannot mclip a not matrix"

-- gradient
seval env (MLipGradSE LR e₁ e₂ e₃) =
  case (seval env (extract e₁), seval env (extract e₂), seval env (extract e₃)) of
    (MatrixV (ExMatrix (θ ∷ Vᴍ m₁ n₁ Val)), MatrixV (ExMatrix (xs ∷ Vᴍ m₂ n₂ Val)), MatrixV (ExMatrix (ys ∷ Vᴍ m₃ n₃ Val))) →
      case (compareTℕ @ m₁ @ 1,compareTℕ @ n₃ @ 1,compareTℕ @ n₁ @ n₂,compareTℕ @ m₂ @ m₃) of
        (Some Refl,Some Refl,Some Refl,Some Refl) →
          let θ' = map urv θ
              xs' = map urv xs
              ys' = map urv ys
          in MatrixV $ ExMatrix $ map RealV $ xgradient θ' xs' ys'
        _ → error "seval MLipGradSE : bad stuff happened"

-- create matrix
seval env (MCreateSE l e₁ e₂ ix jx e₃) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (NatV v₁, NatV v₂) →
      d𝕟32 (natΩ32 v₁) $ \ (m ∷ Sℕ32 m) →
      d𝕟32 (natΩ32 v₂) $ \ (n ∷ Sℕ32 n)  →
      MatrixV $ ExMatrix $ matrix m n $ \ i j →
        seval ((ix ↦ NatV (nat $ un𝕀32 i)) ⩌ (jx ↦ NatV (nat $ un𝕀32 j)) ⩌ env) $ extract e₃

seval env (MFoldSE e₁ e₂ x₁ x₂ e₃) =
  case (seval env (extract e₁),seval env (extract e₂)) of
    (v₁, MatrixV (ExMatrix v₂)) →
      fold v₁ (\b a → (seval ((x₁ ↦ a) ⩌ (x₂ ↦ b) ⩌ env) (extract e₃))) $ iter $ map (MatrixV ∘ ExMatrix) $ xsplit v₂

-- matrix maps
seval env (MMapSE e₁ x e₂) =
  case (seval env (extract e₁)) of
    (MatrixV v₁) →
      MatrixV $ map (\a → (seval ((x ↦ a) ⩌ env) (extract e₂))) v₁

seval env (MMap2SE e₁ e₂ x₁ x₂ e₃) =
  case (seval env (extract e₁),seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → case v₁ of
      ExMatrix (xs ∷ Vᴍ m n Val) → case shapedExMatrix (xrows xs) (xcols xs) v₂ of
        None → error "bad dimensions"
        Some (ys ∷ Vᴍ m n Val) →
          let fn = (\a b → (seval ((x₂ ↦ b) ⩌ ((x₁ ↦ a) ⩌ env)) (extract e₃)))
              c = xmap2 fn xs ys
          in MatrixV $ ExMatrix c

seval env (MMapColSE e₁ x e₂) =
  case (seval env (extract e₁)) of
    (MatrixV (ExMatrix v₁)) →
      MatrixV $ ExMatrix $ map (\a → (seval ((x ↦ (MatrixV (ExMatrix a))) ⩌ env) (extract e₂))) (xcolsplit v₁)

-- functions and application
seval env (PFunSE _ args body) =
  PFunV (map fst args) (ExPriv (Ex_C (extract body))) env

seval env (SFunSE _ x _ body) =
  SFunV x (ExPriv (Ex_C (extract body))) env

seval env (BoxSE e) = seval env (extract e)

seval env (UnboxSE e) = seval env (extract e)

seval env TrueSE = BoolV True

seval env FalseSE = BoolV False

seval env (AppSE e₁ _ e₂) =
  case seval env (extract e₁) of
    (SFunV x (ExPriv (Ex_C body)) env') →
      let env'' = (x ↦ (seval env (extract e₂))) ⩌ env'
      in seval env'' body

seval env (SetSE es) = SetV $ pow $ map ((seval env) ∘ extract) es

seval env (TupSE e₁ e₂) = PairV $ seval env (extract e₁) :* seval env (extract e₂)

seval env (MemberSE e₁ e₂) = case (seval env (extract e₁), seval env (extract e₂)) of
  (v, SetV p) → BoolV $ v ∈ p

seval env (UnionAllSE e) = case (seval env (extract e)) of
  (SetV ss) → SetV $ fold pø (∪) $ pmap (\(SetV p) → p) ss

seval env (JoinSE e₁ e₂ e₃ e₄) =
  case (seval env (extract e₁),seval env (extract e₂),seval env (extract e₃),seval env (extract e₄)) of
    (MatrixV m₁, NatV n₁, MatrixV m₂, NatV n₂) →
      let colmaps = map (\row₁ → joinMatch₁ n₁ (fromRows (list [row₁])) (map (\l → (fromRows (list [l]))) (toRows m₂)) n₂) (toRows m₁)
          colmaps₁ = filter (\colmap → not (colmap ≡ Nil)) $ colmaps
      in MatrixV $ fromRows $ list colmaps₁

seval env (EqualsSE e₁ e₂) =
  let v₁ = seval env $ extract e₁
      v₂ = seval env $ extract e₂
  in BoolV $ v₁ ≡ v₂

seval env (IdxSE e) = seval env $ extract e

seval env (DiscSE e) = seval env $ extract e

seval env (ConvSE e) = seval env $ extract e

seval env (MFilterSE e₁ x e₂) =
  case (seval env (extract e₁)) of
    MatrixV m → do
      let boolVals ∷ 𝐿 (Val ∧ (𝐿 Val)) = map (\row → (seval ((x ↦ MatrixV (fromRows (list [row]))) ⩌ env) (extract e₂)) :* row) (toRows m)
      let filtered = filter (\val → case val of
                                (BoolV v :* result) → v)
                     boolVals
      let final = map snd filtered
      let finalM = MatrixV $ fromRows $ list final
      finalM
    _ → error $ "Error in mfilterSE"


seval env e = error $ "Unknown expression: " ⧺ (show𝕊 e)

-- | Evaluates an expression from the privacy language
peval ∷ (PRIV_C p) ⇒ Env → PExp p → IO (Val)

-- bind and application
peval env (BindPE x e₁ e₂) = do
  v₁ ← peval env (extract e₁)
  v₂ ← peval ((x ↦ v₁) ⩌ env) (extract e₂)
  return v₂

peval env (IfPE e₁ e₂ e₃) = case seval env (extract e₁) of
  BoolV True → peval env (extract e₂)
  BoolV False → peval env (extract e₃)

peval env (AppPE e₁ _ e₂s) =
  let f = seval env (extract e₁) in
  case f of
    (PFunV xs (ExPriv (Ex_C body)) env') →
      let args = map (seval env ∘ extract) e₂s in
      let env'' = (assoc $ zip xs args) ⩌ env' in
      peval env'' body
    _ → error $ "AppPE: invalid function: " ⧺ (pprender f)
      -- let env'' = (x ↦ (seval env (extract e₂))) ⩌ env'
      -- in seval env'' body

-- sample on two matrices and compute on sample
peval env (EDSamplePE size xs ys x y e) =
  case (seval env (extract size), seval env (extract xs), seval env (extract ys)) of
    (NatV n, MatrixV v1, MatrixV v2) → case v1 of
      ExMatrix (xs ∷ Vᴍ m n Val) → case shapedExMatrix (xrows xs) (s𝕟32 @ 1) v2 of
        None → error "bad dimensions"
        Some (ys ∷ Vᴍ m 1 Val) →
          (d𝕟32 (natΩ32 n) (\n₁ → sampleHelper n₁ (map urv xs) (map urv ys) x y (extract e) env))

peval env (TCSamplePE size xs ys x y e) =
  case (seval env (extract size), seval env (extract xs), seval env (extract ys)) of
    (NatV n, MatrixV v1, MatrixV v2) → case v1 of
      ExMatrix (xs ∷ Vᴍ m n Val) → case shapedExMatrix (xrows xs) (s𝕟32 @ 1) v2 of
        None → error "bad dimensions"
        Some (ys ∷ Vᴍ m 1 Val) →
          (d𝕟32 (natΩ32 n) (\n₁ → sampleHelper n₁ (map urv xs) (map urv ys) x y (extract e) env))

peval env (RenyiSamplePE size xs ys x y e) =
  case (seval env (extract size), seval env (extract xs), seval env (extract ys)) of
    (NatV n, MatrixV v1, MatrixV v2) → case v1 of
      ExMatrix (xs ∷ Vᴍ m n Val) → case shapedExMatrix (xrows xs) (s𝕟32 @ 1) v2 of
        None → error "bad dimensions"
        Some (ys ∷ Vᴍ m 1 Val) →
          (d𝕟32 (natΩ32 n) (\n₁ → sampleHelper n₁ (map urv xs) (map urv ys) x y (extract e) env))

-- gaussian mechanism for real numbers
peval env (GaussPE r (EDGaussParams ε δ) vs e) =
  case (seval env (extract r), seval env (extract ε), seval env (extract δ), seval env (extract e)) of
    (RealV r', RealV ε', RealV δ', RealV v) → do
      r ← gaussianNoise zero (r' × (root $ 2.0 × (log $ 1.25/δ')) / ε')
      return $ RealV $ v + r
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

-- laplace mechanism for real numbers
peval env (LaplacePE r (EpsLaplaceParams ε) vs e) =
  case (seval env (extract r), seval env (extract ε), seval env (extract e)) of
    (RealV r', RealV ε', RealV v) → do
      r ← laplaceNoise (r' / ε')
      return $ RealV $ v + r
    (a, b, c) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c))

-- gaussian mechanism for matrices
peval env (MGaussPE r (EDGaussParams ε δ) vs e) =
  case (seval env (extract r), seval env (extract ε), seval env (extract δ), seval env (extract e)) of
    (RealV r', RealV ε', RealV δ', MatrixV (ExMatrix mat)) → do
      let σ = (r' × (root $ 2.0 × (log $ 1.25/δ')) / ε')
      let mat' = map urv mat
      mat'' ← xumapM (\val → gaussianNoise val σ) mat'
      let r = MatrixV $ ExMatrix $ (map RealV $ xvirt mat'')
      return r
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

peval env (MGaussPE r (RenyiGaussParams α ϵ) vs e) =
  case (seval env (extract r), seval env (extract α), seval env (extract ϵ), seval env (extract e)) of
    (RealV r', NatV α', RealV ϵ', MatrixV mat) → do
      let σ = (r' × (root (dbl α'))) / (root (2.0 × ϵ'))
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toRows (map urv mat)
      return $ MatrixV $ (map RealV (fromRows mat'))
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

peval env (MGaussPE r (TCGaussParams ρ ω) vs e) =
  case (seval env (extract r), seval env (extract ρ), seval env (extract ω), seval env (extract e)) of
    (RealV r', RealV ρ', NatV ω', MatrixV mat) → do
      gn ← gaussianNoise 0.0 ((8.0 × r' × r') / ρ')
      let a = 8.0 × r' × (dbl ω')
      let σ =  a × (arsinh $ (1.0 / a) × gn)
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toRows (map urv mat)
      return $ MatrixV $ (map RealV (fromRows mat'))
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

-- evaluate finite iteration
peval env (LoopPE k init xs x₁ x₂ e) =
  case (seval env (extract k), seval env (extract init)) of
    (NatV k', initV) →
      iter₁ k' initV x₁ x₂ 0 (extract e) env

peval env (EDLoopPE _ k init xs x₁ x₂ e) =
  case (seval env (extract k), seval env (extract init)) of
    (NatV k', initV) →
      iter₁ k' initV x₁ x₂ 0 (extract e) env

peval env (ParallelPE e₀ e₁ x₂ e₂ x₃ x₄ e₃) =
  case (seval env (extract e₀), seval env (extract e₁)) of
    (MatrixV m, SetV p) → do
      let candidates ∷ 𝐿 (Val ∧ 𝐿 (𝐿 Val)) = map (\row → (seval ((x₂ ↦ MatrixV (fromRows (list [row]))) ⩌ env) (extract e₂)) :* (list [row])) (toRows m)
      let partitions = map (\x → x :* (concat $ map snd $ filter (\y → (fst y) ≡ x) candidates))
                       (uniques p)
      let evalPart (name :* llvals) = evalOnePart name $ MatrixV (fromRows llvals)
          evalOnePart v m = (peval ((x₃ ↦ v) ⩌ (x₄ ↦ m) ⩌ env) (extract e₃))
      r ← pow ^$ mapM evalPart partitions
      return $ SetV $ r

-- evaluate sensitivity expression and return in the context of the privacy language
peval env (ReturnPE e) =
  return $ seval env (extract e)

peval env (ExponentialPE se (EDExponentialParams εe) xse _ x body) =
  case (seval env (extract se), seval env (extract εe), seval env (extract xse)) of
    (RealV s, RealV ε, MatrixV (ExMatrix (xs ∷ Vᴍ m n Val))) → case compareTℕ @ m @ 1 of
      None → error "bad matrix shape not 1 in exponential"
      Some Refl → do
        i ← exponentialHelper env s ε xs x $ extract body
        return $ NatV i

-- error
peval env e = error $ "Unknown expression: " ⧺ (show𝕊 e)

exponentialHelper ∷ ∀ p m n. (PRIV_C p,Rℕ n) ⇒ (𝕏 ⇰ Val) → 𝔻 → 𝔻 → Vᴍ 1 n Val → 𝕏 → SExp p → IO ℕ
exponentialHelper env s ε xs x body = do
  let scores = map (\ x' →  urv $ seval ((x ↦ x') ⩌ env) body) xs
      δ     = 1e-5
      σ      = (s × (root $ 2.0 × (log $ 1.25/δ)) / ε)
  scores' ← xumapM (\score → gaussianNoise score σ) scores
  let rM = firstMaxByLT ((<) `on` snd) $ withIndex scores'
  return $ case rM of
    None → error "exponential on empty thing"
    Some r → fst r

-- | Helper function for loop expressions
iter₁ ∷ (PRIV_C p) ⇒ ℕ → Val → 𝕏 → 𝕏 → ℕ → PExp p → Env → IO (Val)
iter₁ 0 v _ _ _ _ _ = return v
iter₁ k v t x kp body env = do
  newVal ← peval ((x ↦ v) ⩌ ((t ↦ (NatV $ nat kp)) ⩌ env)) body
  iter₁ (k - 1) newVal t x (kp+1) body env

-- | Samples a normal distribution and returns a single value
gaussianNoise ∷ 𝔻 → 𝔻 → IO 𝔻
gaussianNoise c v = normalIO'(c, v)

laplaceNoise ∷ 𝔻 → IO 𝔻
laplaceNoise scale = do
  gen ← createSystemRandom
  u ← uniformR (neg 0.5, 0.5) gen
  return $ neg $ scale × (signum u) × log(1.0 - 2.0 × (abs u))

-- -- | Helper function for PSampleE
sampleHelper :: (PRIV_C p, Rℕ o) ⇒ Sℕ32 o → Vᴍ m n 𝔻 → Vᴍ m 1 𝔻 → 𝕏 → 𝕏 → PExp p → Env → IO Val
sampleHelper n xs ys x y e env = do
  batch <- minibatch n xs ys
  peval (insertDataSet env (x :* y) ((fst batch) :* (snd batch))) e

randIndex ∷ GenIO → Sℕ32 m → IO (𝕀32 m)
randIndex gen n = do
  x ← uniformR (zero, unSℕ32 n - 𝕟32 1) gen
  return $ d𝕟32 x $ \ x' → 𝕀32 x' TRUSTME_LT

-- -- | Generates random indicies for sampling
randIndices ∷ (Rℕ m) ⇒ GenIO → Sℕ32 m → Sℕ32 n → IO (Vᴍ 1 m (𝕀32 n))
randIndices gen m n = map xvirt $ xbmapM (\ () → randIndex gen n) $ xconst (s𝕟32 @ 1) m ()

-- | Outputs a single minibatch of data
minibatch :: (Rℕ o) ⇒ Sℕ32 o → Vᴍ m n 𝔻 → Vᴍ m 1 𝔻 → IO (Vᴍ o n 𝔻 ∧ Vᴍ o 1 𝔻)
minibatch batchSize xs@(Vᴍ _ _ _) ys@(Vᴍ _ _ _) = do
  gen <- createSystemRandom
  idxs <- randIndices gen batchSize (xrows xs)
  return (xindirect xs idxs :* xindirect ys idxs)

insertDataSet ∷ Env → (𝕏 ∧ 𝕏) → (Vᴍ o n 𝔻 ∧ Vᴍ o 1 𝔻) → Env
insertDataSet env (x :* y) (xs@(Vᴍ _ _ _) :* ys@(Vᴍ _ _ _)) =
  (x ↦ (MatrixV $ ExMatrix $ map RealV xs)) ⩌ (y ↦ (MatrixV $ ExMatrix $ map RealV ys)) ⩌ env

-- | Obtains a vector in the same direction with L2-norm=1
normalize ::Vᴍ 1 m 𝔻 → Vᴍ 1 m 𝔻
normalize v
  | r > 1.0     =  xmap (\ x → x / r) v
  | otherwise   =  v
  where
    r = norm_2 v

-- | Makes a single prediction
predict ∷ Model → (DuetVector 𝔻 ∧ 𝔻) → 𝔻
predict θ (x :* _y) = signum $ x <.> θ

-- dot product
(<.>) :: DuetVector 𝔻 → DuetVector 𝔻 → 𝔻
(<.>) a b = sum $ zipWith (×) a b

signum ∷ (Ord a, Zero a, Zero p, Minus p, One p) ⇒ a → p
signum x = case compare x zero of
  LT → neg one
  EQ → zero
  GT → one

abs ∷ (Ord p, Zero p, Minus p) ⇒ p → p
abs x = case compare x zero of
  LT → neg x
  EQ → zero
  GT → x

isCorrect ∷ (𝔻 ∧ 𝔻) → (ℕ ∧ ℕ)
isCorrect (prediction :* actual) = unID $ do
  return $ case prediction ≡ actual of
    True → (1 :* 0)
    False → (0 :* 1)

-- | Calculates the accuracy of a model
accuracy ∷ ExMatrix 𝔻 → DuetVector 𝔻 → Model → (ℕ ∧ ℕ)
accuracy (ExMatrix x) y θ =
  let x' = xlist2 $ xmeld (xcols x) $ xmap normalize $ xsplit x
      pairs ∷ 𝐿 (DuetVector 𝔻 ∧ 𝔻) = list $ zip x' y
      labels ∷ 𝐿 𝔻 = map (predict θ) pairs
      correct ∷ 𝐿 (ℕ ∧ ℕ) = map isCorrect $ list $ zip labels y
  in fold (0 :* 0) (\a b → ((fst a + fst b) :* (snd a + snd b))) correct
