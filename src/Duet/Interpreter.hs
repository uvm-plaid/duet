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

type Env = 𝕏 ⇰ Val
type Vector v = 𝐿 v
type Matrix v = (ℕ ⇰ (ℕ ⇰ v))

-- TODO: eventually add this to UVMHS
minElem ::  Ord b => (a → b) → 𝐿 a → a
minElem f Nil = error "minElem on empty list"
minElem f (x:&xs) = fold x (\ x₁ x₂ → case f x₁ < f x₂ of { True → x₁ ; False → x₂ }) xs

minElemPairs :: Ord b => 𝐿 (a ∧ b) → a ∧ b
minElemPairs = minElem snd

-- helpers

iota :: ℕ → 𝐿 ℕ
iota n = (single𝐿 0) ⧺ list (upTo (n-1))

replicate :: ℕ → a → 𝐿 a
replicate len v = list $ build len v (\ x → x)

zipWith :: (a → b → c) → 𝐿 a → 𝐿 b → 𝐿 c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil
zipWith f (x:&xs) (y:&ys) = f x y :& zipWith f xs ys

take :: ℕ → 𝐿 𝔻 → 𝐿 𝔻
take 0 _ = Nil
take _ Nil= Nil
take n (x:&xs) = x :& take (n-1) xs

iterate :: (a → a) → a → [a]
iterate f a = a : iterate f (f a)

norm_2 :: Vector 𝔻 → 𝔻
norm_2 = root ∘ sum ∘ map (\x → x×x)

fst1 :: (a,b) → a
fst1 (x,_) = x

snd1 :: (a,b) → b
snd1 (_,x) = x

-- matrix ops

cols :: Matrix v → ℕ
cols a =
  let rws = list𝐼 (uniques (keys a)) in
    case rws of
      (x:&xs) → (dsize (a ⋕! x))
      _ → error "cols: empty matrix"

rows :: Matrix v → ℕ
rows = dsize

tr :: Matrix 𝔻 → Matrix 𝔻
tr m = fromLists $ transpose $ toRows m

transpose:: 𝐿 (𝐿 a) → 𝐿 (𝐿 a)
transpose (Nil:&_) = Nil
transpose m = (map head m) :& transpose (map tail m)

(===) :: Matrix a → Matrix a → Matrix a
(===) a b =
  let a₁ = toRows a
      b₁ = toRows b
      c = a₁ ⧺ b₁
  in fromRows c

normalize :: Vector 𝔻 → 𝐿 𝔻
normalize vec = map (/ (root $ sum (map (^2.0) vec))) vec

ident :: ℕ → Matrix 𝔻
ident n = let m = [ [boolCheck $ i ≡ j | i <- list $ upTo n] | j <- list $ upTo n] in
  fromRows m

boolCheck :: 𝔹 → 𝔻
boolCheck True = 1.0
boolCheck False = 0.0

flatten :: Matrix 𝔻 → Vector 𝔻
flatten m = fold Nil (⧺) (list (values (map (list ∘ values) m)))

(<>) :: Matrix 𝔻 → Matrix 𝔻 → Matrix 𝔻
(<>) a b =
  let a₁ = toRows a
      b₁ = toRows (tr b)
      c = [ [ sum $ zipWith (×) ar bc | bc <- b₁ ] | ar <- a₁ ]
  in fromRows c

scale :: 𝔻 → Vector 𝔻 → Model
scale r v = map (× r) v

mscale :: 𝔻 → Matrix 𝔻 → Matrix 𝔻
mscale r v = mapp (× r) v

vector :: 𝐿 𝔻 → Vector 𝔻
vector x = x

head :: 𝐿 a → a
head (x:&xs) = x
head _ = error "head failed"

tail :: 𝐿 a → 𝐿 a
tail (x:&xs) = xs
tail _ = error "tail failed"

fromList :: 𝐿 𝔻 → Vector 𝔻
fromList x = x

-- Creates a matrix from a list of vectors, as columns
fromColumns :: 𝐿 (Vector t) → Matrix t
fromColumns vecs =
  let rows = buildCols vecs in
    buildRows (iota (count rows)) rows

-- given list of vecs build list of colmaps, so really building rows
buildCols :: 𝐿 (Vector t) → 𝐿 (ℕ ⇰ t)
buildCols vecs = case (fold Nil (⧺) vecs) of
  (x:&xs) → let row = (map head vecs) in
    (buildCol (iota (count row)) row) ⧺ buildCols (map tail vecs)
  Nil → empty𝐿

fromLists :: 𝐿 (𝐿 a) → Matrix a
fromLists ls =
  let cols = fromLists1 ls in buildRows (iota (count cols)) cols

fromLists1 :: 𝐿 (𝐿 a) → 𝐿 (ℕ ⇰ a)
fromLists1 (x:&xs) = (buildCol (iota (count x)) x) ⧺ fromLists1 xs
fromLists1 Nil = Nil

fromRows = fromLists

-- build col map (really a row)
buildCol :: 𝐿 ℕ → 𝐿 a → 𝐿 (ℕ ⇰ a)
buildCol idxs vals = single𝐿 $ fold dø (⩌) (zipWith (↦) idxs vals)

-- creates a 1-column matrix from a vector
asColumn :: Vector a → Matrix a
asColumn vec = buildRows (iota (count vec)) (map ((↦) 0) vec)

-- given a list of column dicts and its iota, really a matrix
buildRows :: 𝐿 ℕ → 𝐿 (ℕ ⇰ a) → Matrix a
buildRows rows cols = fold dø (⩌) (zipWith (↦) rows cols)

-- Creates a list of vectors from the columns of a matrix
toColumns :: Matrix t → 𝐿 (Vector t)
toColumns m = let colLists = (values m) in
  (mapLookup (iota (count colLists)) (list colLists))

mapLookup :: 𝐿 ℕ →  𝐿 (ℕ ⇰ a) → 𝐿 (𝐿 a)
mapLookup (i:&idxs) cols = single𝐿 (map (\x → x ⋕! i) cols) ⧺ mapLookup idxs cols
mapLookup Nil cols = Nil

-- extract rows in N
(?) :: Matrix 𝔻 → 𝐿 ℕ → Matrix 𝔻
(?) m (n:&ns) = (n ↦ (m ⋕! n)) ⩌ (m ? ns)
(?) m Nil = dø

toList :: Vector 𝔻 → 𝐿 𝔻
toList x = x

-- extracts the rows of a matrix as a list of vectors
toRows :: Matrix a → 𝐿 (Vector a)
toRows m =  list $ values $ map (list ∘ values) m

toLists = toRows

size :: Matrix Val → (ℕ, ℕ)
size m = (dsize m, (dsize (head (list (values m)))))

-- creates a 1-row matrix from a vector
asRow :: Vector a → Matrix a
asRow vec = 0 ↦ (fold dø (⩌) (buildCol (iota (count vec)) vec))

(+++) :: (Plus a) => Matrix a → Matrix a → Matrix a
(+++) a b =
  let a₁ = toRows a
      b₁ = toRows b
      add = zipWith (zipWith (+))
      c = add a₁ b₁
  in fromRows c

(-/) :: (Minus a) => Matrix a → Matrix a → Matrix a
(-/) a b =
  let a₁ = toRows a
      b₁ = toRows b
      sub = zipWith (zipWith (-))
      c = sub a₁ b₁
  in fromRows c

urv :: Val → 𝔻
urv x = case x of
  RealV d → d
  _ → error $ "unpack real val failed" ⧺ pprender x

-- | Defining Val algebraic data type
-- data Val =
--   NatV ℕ
--   | RealV 𝔻
--   | PairV Val Val
--   | SFunV 𝕏 (Ex SExp) Env  -- See UVMHS.Core.Init for definition of Ex
--   | PFunV (𝐿 𝕏) (Ex PExp) Env
--   | MatrixV (Matrix Val)


data Val where
  NatV ∷ ℕ → Val
  RealV ∷ 𝔻 → Val
  StrV ∷ 𝕊 → Val
  PairV ∷ Val → Val → Val
  SFunV ∷ 𝕏 → SExp p → Env → Val
  PFunV ∷ 𝐿 𝕏 → PExp p → Env → Val
  MatrixV ∷ Matrix Val → Val
deriving instance Show Val
-- deriving instance Eq Val

instance Pretty Val where
  pretty = \case
    NatV n → pretty n
    RealV d → pretty d
    StrV s → pretty s
    PairV a b → pretty (a :* b)
    SFunV x se e → ppKeyPun "sλ"
    PFunV xs pe e → ppKeyPun "pλ"
    MatrixV m → ppKeyPun "𝕄T"

-- | Converts and integer to a 𝔻
intDouble ∷ ℕ → 𝔻
intDouble = dbl

-- | Converts a natural number to a double
mkDouble ∷ ℕ → 𝔻
mkDouble = dbl

-- | Evaluates an expression from the sensitivity language
seval ∷ (Env) → (SExp p) → (Val)

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
    (MatrixV v₁, MatrixV v₂) → MatrixV $ mapp RealV ( (mapp urv v₁) +++ (mapp urv v₂) )
    (RealV v₁, RealV v₂) → RealV (v₁ + v₂)
    (a, b) → error $ "No pattern for " ⧺ (show𝕊 (a, b))

seval env (MinusSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → MatrixV $ mapp RealV ( (mapp urv v₁) -/ (mapp urv v₂) )
    (RealV v₁, RealV v₂) → RealV (v₁ - v₂)
    (a, b) → error $ "No pattern for " ⧺ (show𝕊 (a, b))

seval env (TimesSE e₁ e₂) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) → MatrixV $ mapp RealV ((mapp urv v₁) <> (mapp urv v₂))
    (RealV v₁, MatrixV v₂) → MatrixV $ mapp RealV (mscale v₁ (mapp urv v₂))
    (RealV v₁, RealV v₂) → RealV (v₁ × v₂)
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

seval env (IdxSE e) =
  case (seval env (extract e)) of
    (NatV d) →
      let posMat ∷ Matrix 𝔻 = ident d
          negMat ∷ Matrix 𝔻 = mscale (neg one) posMat
      in MatrixV (mapp RealV (posMat === negMat))

-- seval env (SMTrE e) =
--   case seval env e of (MatrixV m) → MatrixV $ tr m

-- clip operation for only L2 norm
seval env (MClipSE norm e) =
  case (norm, seval env (extract e)) of
    (L2,   MatrixV v) →  MatrixV $ mapp RealV $ fromRows (map normalize $ toRows $ mapp urv v)
    (LInf, MatrixV v) →  MatrixV $ mapp RealV $ fromRows (map normalize $ toRows $ mapp urv v)
    (l, _) → error $ "Invalid norm for clip: " ⧺ (show𝕊 l)

-- gradient
seval env (MLipGradSE LR e₁ e₂ e₃) =
  case (seval env (extract e₁), seval env (extract e₂), seval env (extract e₃)) of
    (MatrixV θ, MatrixV xs, MatrixV ys) →
      case ((rows θ ≡ 1) ⩓ (cols ys ≡ 1)) of
        True →
          let θ'  ∷ Vector 𝔻 = flatten (mapp urv θ)
              ys' ∷ Vector 𝔻 = flatten (mapp urv ys)
          in MatrixV $ mapp RealV $ asRow $ ngrad θ' (mapp urv xs) ys'
        False →
          error $ "Incorrect matrix dimensions for gradient: " ⧺ (show𝕊 (rows θ, rows ys))
    (a, b, c) → error $ "No pattern for " ⧺ (show𝕊 (a, b, c))

-- create matrix
seval env (MCreateSE l e₁ e₂ i j e₃) =
  case (seval env (extract e₁), seval env (extract e₂)) of
    (NatV v₁, NatV v₂) →
      let row = replicate v₂ 0.0
          m = replicate v₁ row
          m₁ = fromRows m
      in MatrixV (mapp RealV m₁)
      -- MatrixV $ (><) (int v₁) (int v₂) $ replicate (int $ v₁ × v₂) 0.0

-- matrix maps
seval env (MMapSE e₁ x e₂) =
  case (seval env (extract e₁)) of
    (MatrixV v₁) →
      MatrixV $ mapp (\a → (seval ((x ↦ a) ⩌ env) (extract e₂))) v₁

seval env (MMap2SE e₁ e₂ x₁ x₂ e₃) =
  case (seval env (extract e₁),seval env (extract e₂)) of
    (MatrixV v₁, MatrixV v₂) →
      let fn = zipWith (zipWith (\a b → (seval ((x₂ ↦ b) ⩌ ((x₁ ↦ a) ⩌ env)) (extract e₃))))
          v₁' = toRows v₁
          v₂' = toRows v₂
          c = fn v₁' v₂'
      in MatrixV $ fromRows c

-- functions and application
seval env (PFunSE _ args body) =
  PFunV (map fst args) (extract body) env

seval env (SFunSE x _ body) =
  SFunV x (extract body) env

seval env (AppSE e₁ e₂) =
  case seval env (extract e₁) of
    (SFunV x body env') →
      let env'' = (x ↦ (seval env (extract e₂))) ⩌ env'
      in seval env'' body

-- seval env (CSVtoMatrixSE s _) =
--   let csvList ∷ 𝐿 (𝐿 𝔻) = mapp read𝕊 s
--       m ∷ Matrix 𝔻 = fromLists csvList
--   in MatrixV $ mapp RealV m

-- error
seval env e = error $ "Unknown expression: " ⧺ (show𝕊 e)

csvToMatrix ∷ 𝐿 (𝐿 𝕊) → Val
csvToMatrix sss =
  let csvList ∷ 𝐿 (𝐿 𝔻) = mapp read𝕊 sss
      m ∷ Matrix 𝔻 = fromLists csvList
  in MatrixV $ mapp RealV m

schemaToTypes :: MExp r → 𝐿 (Type r)
schemaToTypes me = case me of
  (ConsME τ me) → schemaToTypes₁ me
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
  --TODO: QUESTION: why can't i print τ here?
  _ → error $ "rowToDFRow: type is currently not supported" {- ⧺ pprender τ -}
  -- TODO: QUESTION: why can't i print this tuple here?
rowToDFRow y z = error $ "rowToDFRow: arguments length mismatch" ⧺ (pprender (y :* z))

csvToDF ∷ (Pretty r) ⇒ 𝐿 (𝐿 𝕊) → 𝐿 (Type r) → Val
csvToDF sss τs =
  let csvList ∷ 𝐿 (𝐿 Val) = map (rowToDFRow τs) sss
  in MatrixV $ fromLists csvList

csvToMatrix𝔻 ∷ 𝐿 (𝐿 𝕊) → Matrix 𝔻
csvToMatrix𝔻 sss =
  let csvList ∷ 𝐿 (𝐿 𝔻) = mapp read𝕊 sss
  in fromLists csvList

-- | Evaluates an expression from the privacy language
peval ∷ Env → PExp p → IO (Val)

-- bind and application
peval env (BindPE x e₁ e₂) = do
  v₁ ← peval env (extract e₁)
  v₂ ← peval ((x ↦ v₁) ⩌ env) (extract e₂)
  return v₂

peval env (AppPE f _ as) =
  case seval env (extract f) of
    (PFunV args body env') →
      let vs    ∷ 𝐿 Val = map ((seval env) ∘ extract) as
          env'' ∷ Env = fold env' (\(var :* val) → (⩌ (var ↦ val))) (zip args vs)
      in peval env'' body

-- sample on two matrices and compute on sample
-- peval env (SamplePE size xs ys x y e) =
--   case (seval env (extract size), env ⋕! (extract xs), env ⋕! ys) of
--     (NatV n, MatrixV v1, MatrixV v2) →
--       sampleHelper n v1 v2 x y e env

-- gaussian mechanism for real numbers
peval env (GaussPE r (EDGaussParams ε δ) vs e) =
  case (seval env (extract r), seval env (extract ε), seval env (extract δ), seval env (extract e)) of
    (RealV r', RealV ε', RealV δ', RealV v) → do
      r ← gaussianNoise zero (r' × (root $ 2.0 × (log $ 1.25/δ')) / ε')
      return $ RealV $ v + r
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show𝕊 (a,b,c,d))

-- gaussian mechanism for matrices
peval env (MGaussPE r (EDGaussParams ε δ) vs e) =
  case (seval env (extract r), seval env (extract ε), seval env (extract δ), seval env (extract e)) of
    (RealV r', RealV ε', RealV δ', MatrixV mat) → do
      let σ = (r' × (root $ 2.0 × (log $ 1.25/δ')) / ε')
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists (mapp urv mat)
      return $ MatrixV $ (mapp RealV (fromLists mat'))
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
iter₁ ∷ ℕ → Val → 𝕏 → 𝕏 → ℕ → PExp p → Env → IO (Val)
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

-- | Helper function for PSampleE
-- sampleHelper :: ℕ → Matrix 𝔻 → Matrix  𝔻 → 𝕏 → 𝕏 → PExp p → Env → IO Val
-- sampleHelper n xs ys x y e env = do
--   batch <- minibatch (int n) xs (flatten ys)
--   peval (insertDataSet env (x, y) ((fst1 batch), (snd1 batch))) e

-- GRADIENT --

type Model = Vector 𝔻


-- | Calculates LR loss
-- loss ∷ Model → Matrix 𝔻 → Vector 𝔻 → 𝔻
-- loss θ x y =
--   let θ'       ∷ Matrix 𝔻 = asColumn θ
--       y'       ∷ Matrix 𝔻 = asColumn y
--       exponent ∷ Matrix 𝔻 = -((x <> θ') × y')
--   in (sumElements (mapp (\x → (log (exp(x)+1.0))) exponent)) / (dbl $ rows x)
--
-- sumElements :: Matrix 𝔻 → 𝔻
-- sumElements m = mapp sum m

-- | Averages LR gradient over the whole matrix of examples
ngrad ∷ Model → Matrix 𝔻 → Vector 𝔻 → Vector 𝔻
ngrad θ x y =
  let θ'       ∷ Matrix 𝔻 = asColumn θ
      y'       ∷ Matrix 𝔻 = asColumn y
      exponent ∷ Matrix 𝔻 = (x <> θ') × y'
      scaled   ∷ Matrix 𝔻 = y' × (mapp (\x → 1.0/(exp(x)+1.0) ) exponent)
      gradSum  ∷ Matrix 𝔻 = (tr x) <> scaled
      avgGrad  ∷ Vector 𝔻 = flatten $ mscale (1.0/(dbl $ rows x)) gradSum
  in (scale (neg one) avgGrad)

-- | Obtains a vector in the same direction with L2-norm=1
-- normalize :: Vector 𝔻 → Vector 𝔻
-- normalize v
--   | r > 1     =  scale (1/r) v
--   | otherwise =  v
--   where
--     r = norm_2 v

-- | Performs gradient descent with a fixed learning rate
-- gradientDescent ∷ ℕ → Model → Matrix 𝔻 → Vector 𝔻 → 𝔻 → Model
-- gradientDescent 0 θ x y η = θ
-- gradientDescent n θ x y η = let θ' = θ - (scale η $ ngrad θ x y)
--                             in trace ("training iter " ⧺ (show n) ⧺
--                                       ", loss : " ⧺ (show $ loss θ x y))
--                                gradientDescent (n-1) θ' x y η

-- | Makes a single prediction
predict ∷ Model → (Vector 𝔻 ∧ 𝔻) → 𝔻
predict θ (x :* y) = signum $ x <.> θ

-- dot product
(<.>) :: Vector 𝔻 → Vector 𝔻 → 𝔻
(<.>) a b = sum $ zipWith (×) a b

-- signum ∷ (Ord a,Plus a,Minus a) ⇒ a → a
signum x = case compare x zero of
  LT → neg one
  EQ → zero
  GT → one

isCorrect ∷ (𝔻 ∧ 𝔻) → (ℕ ∧ ℕ)
isCorrect (prediction :* actual) | prediction ≡ actual = (1 :* 0)
                                 | otherwise = (0 :* 1)

-- | Converts a matrix to a model (flatten it)
-- toModel ∷ Matrix 𝔻 → Model
-- toModel = flatten

-- | Calculates the accuracy of a model
accuracy ∷ Matrix 𝔻 → Vector 𝔻 → Model → (ℕ ∧ ℕ)
accuracy x y θ = let pairs ∷ 𝐿 (Vector 𝔻 ∧ 𝔻) = list $ zip (map normalize $ toRows x) (toList y)
                     labels ∷ 𝐿 𝔻 = map (predict θ) pairs
                     correct ∷ 𝐿 (ℕ ∧ ℕ) = map isCorrect $ list $ zip labels (toList y)
                 in fold (0 :* 0) (\a b → ((fst a + fst b) :* (snd a + snd b))) correct

-- | Ensures that labels are either 1 or -1
-- fixLabel ∷ 𝔻 → 𝔻
-- fixLabel x | x ≡ -1.0 = -1.0
--            | x ≡ 1.0 = 1.0
--            | otherwise = trace ("Unexpected label: " ⧺ (show x)) x

-- END GRADIENT --

-- MINIBATCHGRADIENT --

-- | Generates random indicies for sampling
-- randIndices :: ℕ → ℕ → ℕ → GenIO → IO [ℕ]
-- randIndices n a b gen
--   | n == 0    = return []
--   | otherwise = do
--       x <- uniformR (a, b) gen
--       xs' <- randIndices (n - 1) a b gen
--       return (x : xs')

-- | Outputs a single minibatch of data
-- minibatch :: ℤ → Matrix 𝔻 → Vector 𝔻 → IO (Matrix 𝔻, Vector 𝔻)
-- minibatch batchSize xs ys = do
--   gen <- createSystemRandom
--   idxs <- randIndices batchSize 0 (rows xs - 1) gen
--   let bxs = xs ? idxs
--       bys = head $ toColumns $ (asColumn ys) ? idxs
--   return (bxs, bys)

-- | Generates a list of minibatches
-- nminibatch :: ℕ → ℕ → Matrix 𝔻 → Vector 𝔻 → IO [(Matrix 𝔻, Vector 𝔻)]
-- nminibatch n batchSize x y
--   | n == 0    = return []
--   | otherwise = do
--       x' <- minibatch batchSize x y
--       xs <- nminibatch (n - 1) batchSize x y
--       return (x' : xs)

-- | Returns an infinite list of random values sampled from a normal distribution
-- noise :: ℕ → ℕ → 𝔻 → 𝔻 → 𝔻 → IO (𝐿 𝔻)
-- noise n iters lreg eps delta =
--   let stdDev = 4 × lreg × (root (dbl(iters) × (log (1 / delta)))) / (dbl(n) × eps)
--   in normalsIO' (0.0, stdDev)

-- | Generates a list of random numbers sampled from a [0, 1) uniform distribution
-- randUniform :: ℕ → IO[𝔻]
-- randUniform n
--   | n ≡ 0    = return Nil
--   | otherwise = do
--       x <- randomIO
--       xs <- randUniform (n - 1)
--       return (x : xs)

-- | Initializes model and regularization parameter
-- initModel :: ℕ → 𝔻 → 𝔻 → 𝑂 𝔻 →  IO (Vector 𝔻, 𝔻)
-- initModel m l lambda l2 = do
--   rand <- randUniform m
--   case (lambda, l2) of
--     (0, None) → return (fromList $ replicate m 0.0, l)
--     (lambda, Some l2) | lambda > 0 →
--       return ((scale (2.0 × l2) (vector (map (- 0.5) rand))), l + lambda×l2)
--     otherwise → return (fromList $ replicate m 0.0, zero)

-- | Runs gradient descent on an initial model and a set of minibatches
-- mbgradientDescent :: ℕ → ℕ  → Model → [(Matrix 𝔻, Vector 𝔻)] → 𝔻 →  [𝔻] → Model
-- mbgradientDescent 0 m theta batches rate noise = theta
-- mbgradientDescent n m theta batches rate noise =
--   let x = (fst (head batches))
--       y = (snd (head batches))
--       grad = ((ngrad theta x y) + (vector (take m noise)))
--       theta' = theta - (scale rate grad)
--   in trace ("training iter " ⧺ (show n) ⧺
--                ", loss : " ⧺ (show $ loss theta x y) ⧺
--                ", noise :" ⧺ (show $ take 5 noise))
--      mbgradientDescent (n - 1) m theta' (tail batches) rate noise

{- | Runs differentially private, minibatch gradient descent on input matrices
     `x` and `y` and a set of input parameters.
-}
-- privateMBSGD :: Matrix 𝔻
--             → Vector 𝔻
--             → 𝔻
--             → 𝔻
--             → ℕ
--             → 𝔻
--             → 𝔻
--             → ℕ
--             → 𝔻
--             → 𝑂 𝔻
--             → IO Model
-- privateMBSGD x y eps delta iters learningRate l batchSize lambda l2 = do
--   init <- initModel (cols x) l lambda l2
--   normalNoise <- noise (rows x) iters (snd init) eps delta
--   minibatches <- nminibatch iters batchSize x y
--   return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate normalNoise)

-- | Runs noiseless minibatch gradient descent.
-- mbSGD :: Matrix 𝔻
--             → Vector 𝔻
--             → 𝔻
--             → 𝔻
--             → ℕ
--             → 𝔻
--             → 𝔻
--             → ℕ
--             → 𝔻
--             → 𝑂 𝔻
--             → IO Model
-- mbSGD x y eps delta iters learningRate l batchSize lambda l2 = do
--   init <- initModel (cols x) l lambda l2
--   minibatches <- nminibatch iters batchSize x y
--   return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate (iterate (+0.0) 0))

-- END MINIBATCHGRADIENT --
