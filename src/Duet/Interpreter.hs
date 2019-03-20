module Duet.Interpreter where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF
import Duet.Quantity

-- libraries
import System.Random
import System.Random.MWC
import Data.Random.Normal

-- import qualified GHC.TypeLits as HS
-- import qualified Prelude as HS
-- import qualified Data.Type.Equality as HS
-- import qualified Data.Proxy as HS

type Env = 𝕏 ⇰ Val
type DuetVector a = 𝐿 a

-- helpers

-- TODO: eventually add this to UVMHS
minElem ::  Ord b => (a → b) → 𝐿 a → a
minElem f Nil = error "minElem on empty list"
minElem f (x:&xs) = fold x (\ x₁ x₂ → case f x₁ < f x₂ of { True → x₁ ; False → x₂ }) xs

minElemPairs :: Ord b => 𝐿 (a ∧ b) → a ∧ b
minElemPairs = minElem snd

replicate :: ℕ → a → 𝐿 a
replicate len v = list $ build len v (\ x → x)

zipWith :: (a → b → c) → 𝐿 a → 𝐿 b → 𝐿 c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil
zipWith f (x:&xs) (y:&ys) = f x y :& zipWith f xs ys

-- vector/matrix ops

norm_2 :: DuetVector 𝔻 → 𝔻
norm_2 = root ∘ sum ∘ map (\x → x×x)

cols :: ExMatrix a → ℕ
cols (ExMatrix xs) = nat $ unSℕ32 $ xcols xs

rows :: ExMatrix a → ℕ
rows (ExMatrix xs) = nat $ unSℕ32 $ xrows xs

tr :: ExMatrix 𝔻 → ExMatrix 𝔻
tr (ExMatrix xs) = ExMatrix $ xtranspose xs

(===) :: ExMatrix a → ExMatrix a → ExMatrix a
(===) a b =
  let a₁ = toRows a
      b₁ = toRows b
      c = a₁ ⧺ b₁
  in fromRows c

ident :: ℕ → ExMatrix 𝔻
ident n = let m = [ [boolCheck $ i ≡ j | i <- list $ upTo n] | j <- list $ upTo n] in
  fromRows m

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

scale :: 𝔻 → DuetVector 𝔻 → Model
scale r v = map (× r) v

mscale :: 𝔻 → ExMatrix 𝔻 → ExMatrix 𝔻
mscale r (ExMatrix m) = ExMatrix $ xmap (× r) m

vector :: 𝐿 𝔻 → DuetVector 𝔻
vector x = x

fromList :: 𝐿 𝔻 → DuetVector 𝔻
fromList x = x

fromLists :: 𝐿 (𝐿 a) → ExMatrix a
fromLists = buildRows

fromRows = fromLists

-- creates a 1-column matrix from a vector
asColumn :: DuetVector a → ExMatrix a
asColumn vec = buildRows (map single𝐿 vec)

-- really build a matrix
buildRows :: 𝐿 (𝐿 a) → ExMatrix a
buildRows ls = xb𝐿 ls $ \ xs → ExMatrix (xvirt xs)

-- extract rows in N
(?) :: ExMatrix 𝔻 → 𝐿 ℤ → ExMatrix 𝔻
(?) m ns = buildRows (m ?? ns)

(??) :: ExMatrix 𝔻 → 𝐿 ℤ → 𝐿 (𝐿 𝔻)
(??) (ExMatrix m) (n:&ns) = (xlist2 (xrow (n2i (xrows m) (natΩ n)) m)) ⧺ ((ExMatrix m) ?? ns)
(??) m Nil = Nil

toList :: DuetVector 𝔻 → 𝐿 𝔻
toList x = x

-- extracts the rows of a matrix as a list of vectors
toRows :: ExMatrix a → 𝐿 (𝐿 a)
toRows (ExMatrix m) = xlist2 m

toLists = toRows

-- size :: ExMatrix Val → (ℕ, ℕ)
-- size m = (xrows m, xcols m)

-- creates a 1-row matrix from a vector
asRow :: DuetVector a → ExMatrix a
asRow vec = fromLists $ list [vec]

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

csvToMatrix ∷ 𝐿 (𝐿 𝕊) → Val
csvToMatrix sss =
  let csvList ∷ 𝐿 (𝐿 𝔻) = mapp read𝕊 sss
      m ∷ ExMatrix 𝔻 = fromLists csvList
  in MatrixV $ map RealV m

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

csvToDF ∷ (Pretty r) ⇒ 𝐿 (𝐿 𝕊) → 𝐿 (Type r) → Val
csvToDF sss τs =
  let csvList ∷ 𝐿 (𝐿 Val) = map (rowToDFRow τs) sss
  in MatrixV $ fromLists csvList

csvToMatrix𝔻 ∷ 𝐿 (𝐿 𝕊) → ExMatrix 𝔻
csvToMatrix𝔻 sss =
  let csvList ∷ 𝐿 (𝐿 𝔻) = mapp read𝕊 sss
  in fromLists csvList

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

ex2m :: ExMatrix a → (∀ m n. Vᴍ m n a → b) → b
ex2m (ExMatrix xs) f = f xs

n2i :: Sℕ32 n → ℕ → 𝕀32 n
n2i s n = case (d𝕚 s (𝕟32 n)) of
  Some x → x
  None → error "index out of bounds"

instance Pretty Val where
  pretty = \case
    NatV n → pretty n
    RealV d → pretty d
    StrV s → pretty s
    BoolV b → pretty b
    ListV l → pretty l
    SetV s → pretty s
    PairV a → pretty a
    SFunV x se e → ppKeyPun "<sλ value>"
    PFunV xs pe e → ppKeyPun "<pλ value>"
    MatrixV m → ppVertical $ list [ppText "MATRIX VALUE:",pretty m]

instance (Pretty a) ⇒ Pretty (ExMatrix a) where
  pretty (ExMatrix a) = pretty a

instance (Pretty a) ⇒ Pretty (Vᴍ m n a) where
  pretty m = pretty $ xlist2 m

-- | Converts and integer to a 𝔻
intDouble ∷ ℕ → 𝔻
intDouble = dbl

-- | Converts a natural number to a double
mkDouble ∷ ℕ → 𝔻
mkDouble = dbl

-- | Evaluates an expression from the sensitivity language
seval ∷ (PRIV_C p) ⇒ (Env) → (SExp p) → (Val)

-- literals
seval _ (ℕSE n)        = NatV n
seval _ (ℝSE n)        = RealV n
seval _ (ℝˢSE n)       = RealV n
seval _ (ℕˢSE n)       = NatV n
seval env (RealSE e) =
  case (seval env $ extract e) of
    (NatV n) → RealV $ mkDouble n

-- variables
seval env (VarSE x) = env ⋕! x
-- | x ∈ env
-- | otherwise = error $ "Unknown variable: " ⧺ (show𝕊 x) ⧺ " in environment with bound vars " ⧺ (show𝕊 $ keys env)

seval env (LetSE x e₁ e₂) = do
  let v₁ = seval env (extract e₁) in
    seval ((x ↦ v₁) ⩌ env) (extract e₂)

-- arithmetic
seval env (PlusSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → MatrixV $ map RealV ( (map urv v₁) +++ (map urv v₂) )
    (RealV v₁, RealV v₂) → RealV (v₁ + v₂)
    (NatV v₁, NatV v₂) → NatV (v₁ + v₂)
    (a, b) → error $ "No pattern for " ⧺ (show𝕊 (a, b))

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
        _ → error "index out of bounds"

--


seval env (IdxSE e) =
  case (seval env (extract e)) of
    (NatV d) →
      let posMat ∷ ExMatrix 𝔻 = ident d
          negMat ∷ ExMatrix 𝔻 = mscale (neg one) posMat
      in MatrixV (map RealV (posMat === negMat))

-- seval env (SMTrE e) =
--   case seval env e of (MatrixV m) → MatrixV $ tr m

-- clip operation for only L2 norm
seval env (MClipSE norm e) =
  case (norm, seval env (extract e)) of
    (L2,   MatrixV v) →  MatrixV $ map RealV $ fromRows (map normalize $ toRows $ map urv v)
    (LInf, MatrixV v) →  MatrixV $ map RealV $ fromRows (map normalize $ toRows $ map urv v)
    (l, _) → error $ "Invalid norm for clip: " ⧺ (show𝕊 l)

-- gradient
seval env (MLipGradSE LR e₁ e₂ e₃) =
  case (seval env (extract e₁), seval env (extract e₂), seval env (extract e₃)) of
    (MatrixV θ, MatrixV xs, MatrixV ys) →
      case ((rows θ ≡ 1) ⩓ (cols ys ≡ 1)) of
        True →
          let θ'  ∷ DuetVector 𝔻 = flatten (map urv θ)
              ys' ∷ DuetVector 𝔻 = flatten (map urv ys)
          in MatrixV $ map RealV $ asRow $ ngrad θ' (map urv xs) ys'
        False →
          error $ "Incorrect matrix dimensions for gradient: " ⧺ (show𝕊 (rows θ, cols ys))
    (a, b, c) → error $ "No pattern for " ⧺ (show𝕊 (a, b, c))

-- create matrix
seval env (MCreateSE l e₁ e₂ i j e₃) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (NatV v₁, NatV v₂) →
      let row = replicate v₂ 0.0
          m = replicate v₁ row
          m₁ = fromRows m
      in MatrixV (map RealV m₁)

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

-- functions and application
seval env (PFunSE _ args body) =
  PFunV (map fst args) (ExPriv (Ex_C (extract body))) env

seval env (SFunSE x _ body) =
  SFunV x (ExPriv (Ex_C (extract body))) env

seval env (BoxSE e) = seval env (extract e)

seval env (UnboxSE e) = seval env (extract e)

seval env TrueSE = BoolV True

seval env FalseSE = BoolV False

-- TODO: this is supposed to clip the vector that e evaluates to such that the norm
-- of the ouptut vector is 1. (only do this if the norm is > 1)
seval env (ClipSE e) = seval env (extract e)

seval env (ConvSE e) = seval env (extract e)

seval env (DiscSE e) = seval env (extract e)

seval env (AppSE e₁ e₂) =
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
      let colmaps = map (\row₁ → joinMatch₁ n₁ (buildRows (list [row₁])) (map (\l → (buildRows (list [l]))) (toLists m₂)) n₂) (toLists m₁)
          colmaps₁ = filter (\colmap → not (colmap ≡ Nil)) $ colmaps
      in MatrixV $ buildRows $ list colmaps₁

-- seval env (CSVtoMatrixSE s _) =
--   let csvList ∷ 𝐿 (𝐿 𝔻) = mapp read𝕊 s
--       m ∷ ExMatrix 𝔻 = fromLists csvList
--   in MatrixV $ mapp RealV m

seval env (EqualsSE e₁ e₂) =
  let v₁ = seval env $ extract e₁
      v₂ = seval env $ extract e₂
  in BoolV $ v₁ ≡ v₂

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

-- peval env (AppPE f _ as) =
--   case seval env (extract f) of
--     (PFunV args body env') →
--       let vs    ∷ 𝐿 Val = map ((seval env) ∘ extract) as
--           env'' ∷ Env = fold env' (\(var :* val) → (⩌ (var ↦ val))) (zip args vs)
--       in peval env'' body

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
    (NatV n, MatrixV v1, MatrixV v2) → error "TODO"
      -- sampleHelper n (map urv v1) (map urv v2) x y (extract e) env

peval env (RenyiSamplePE size xs ys x y e) =
  case (seval env (extract size), seval env (extract xs), seval env (extract ys)) of
    (NatV n, MatrixV v1, MatrixV v2) → error "TODO"
      -- sampleHelper n (map urv v1) (map urv v2) x y (extract e) env

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
    (RealV r', RealV ε', RealV δ', MatrixV mat) → do
      let σ = (r' × (root $ 2.0 × (log $ 1.25/δ')) / ε')
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists (map urv mat)
      return $ MatrixV $ (map RealV (fromLists mat'))
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

peval env (MGaussPE r (RenyiGaussParams α ϵ) vs e) =
  case (seval env (extract r), seval env (extract α), seval env (extract ϵ), seval env (extract e)) of
    (RealV r', NatV α', RealV ϵ', MatrixV mat) → do
      let σ = (r' × (root (dbl α'))) / (root (2.0 × ϵ'))
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists (map urv mat)
      return $ MatrixV $ (map RealV (fromLists mat'))
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

peval env (MGaussPE r (TCGaussParams ρ ω) vs e) =
  case (seval env (extract r), seval env (extract ρ), seval env (extract ω), seval env (extract e)) of
    (RealV r', RealV ρ', NatV ω', MatrixV mat) → do
      gn ← gaussianNoise 0.0 ((8.0 × r' × r') / ρ')
      let a = 8.0 × r' × (dbl ω')
      let σ =  a × (arsinh $ (1.0 / a) × gn)
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists (map urv mat)
      return $ MatrixV $ (map RealV (fromLists mat'))
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
      let candidates ∷ 𝐿 (Val ∧ 𝐿 (𝐿 Val)) = map (\row → (seval ((x₂ ↦ MatrixV (fromRows (list [row]))) ⩌ env) (extract e₂)) :* (list [row])) (toLists m)
      let parts ∷ 𝐿 (Val ∧ 𝐿 (𝐿 Val)) = partition (list (uniques p)) $ list $ filter (\x → (fst x) ∈ p) candidates
      let parts₁ = filter (\(v:*llvs) → not (llvs ≡ Nil)) parts
      r ← pow ^$ mapM (\(v :* llvals) → (peval ((x₃ ↦ v) ⩌ (x₄ ↦ MatrixV (fromRows llvals)) ⩌ env) (extract e₃))) parts₁
      return $ SetV $ r

-- evaluate sensitivity expression and return in the context of the privacy language
peval env (ReturnPE e) =
  return $ seval env (extract e)

-- exponential mechanism
-- peval env (ExponentialPE s ε xs _ x body) =
--   case (seval env s, seval env ε, seval env xs) of
--     (RealV s', RealV ε', MatrixV xs') →
--       let xs''     = map (\row' → fromLists [row']) $ toLists xs'
--           envs     = map (\m → (x ↦ (MatrixV m)) ⩌ env) xs''
--           getScore = \env1 → case seval env1 (extract body) of
--             (RealV   r) → r
--             (MatrixV m) | size m == (1, 1) → head $ head $ toLists m
--             a → error $ "Invalid score: " ⧺ (chars $ show𝕊 a)
--           scores   = map getScore envs
--           δ'       = 1e-5
--           σ        = (s' × (root $ 2.0 × (log $ 1.25/δ')) / ε')
--       in do
--         scores' ← mapM (\score → gaussianNoise score σ) scores
--         return $ MatrixV $ minElem (zip xs'' scores')

-- error
peval env e = error $ "Unknown expression: " ⧺ (show𝕊 e)


-- | Helper function for loop expressions
iter₁ ∷ (PRIV_C p) ⇒ ℕ → Val → 𝕏 → 𝕏 → ℕ → PExp p → Env → IO (Val)
iter₁ 0 v _ _ _ _ _ = return v
iter₁ k v t x kp body env = do
  newVal ← peval ((x ↦ v) ⩌ ((t ↦ (NatV $ nat kp)) ⩌ env)) body
  iter₁ (k - 1) newVal t x (kp+1) body env

-- | Empty environment
emptyEnv ∷ Env
emptyEnv = dø

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
  x ← uniformR (zero, unSℕ32 n) gen
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

type Model = DuetVector 𝔻

-- | Averages LR gradient over the whole matrix of examples
ngrad ∷ Model → ExMatrix 𝔻 → DuetVector 𝔻 → DuetVector 𝔻
ngrad θ x y =
  let θ'       = asColumn θ
      y'       = asColumn y
      exponent = (x <> θ') <> y'
      scaled   = y' <> (map (\x → 1.0/(exp(x)+1.0) ) exponent)
      gradSum  = (tr x) <> scaled
      avgGrad  ∷ DuetVector 𝔻 = flatten $ mscale (1.0/(dbl $ rows x)) gradSum
  in (scale (neg one) avgGrad)

-- | Obtains a vector in the same direction with L2-norm=1
normalize :: DuetVector 𝔻 → DuetVector 𝔻
normalize v
  | r > 1.0     =  scale (1.0/r) v
  | otherwise =  v
  where
    r = norm_2 v

-- | Makes a single prediction
predict ∷ Model → (DuetVector 𝔻 ∧ 𝔻) → 𝔻
predict θ (x :* y) = signum $ x <.> θ

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
isCorrect (prediction :* actual) | prediction ≡ actual = (1 :* 0)
                                 | otherwise = (0 :* 1)

-- | Calculates the accuracy of a model
accuracy ∷ ExMatrix 𝔻 → DuetVector 𝔻 → Model → (ℕ ∧ ℕ)
accuracy x y θ = let pairs ∷ 𝐿 (DuetVector 𝔻 ∧ 𝔻) = list $ zip (map normalize $ toRows x) (toList y)
                     labels ∷ 𝐿 𝔻 = map (predict θ) pairs
                     correct ∷ 𝐿 (ℕ ∧ ℕ) = map isCorrect $ list $ zip labels (toList y)
                 in fold (0 :* 0) (\a b → ((fst a + fst b) :* (snd a + snd b))) correct
