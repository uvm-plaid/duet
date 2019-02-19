module Duet.Interpreter where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF
import Duet.Quantity

-- libraries
import System.Random
import System.Random.MWC
import System.FilePath
import Data.Random.Normal
import Text.CSV
import Text.Parsec.Error

-- import Data.Csv
-- import System.Environment
-- import Debug.Trace
-- import Numeric.Natural
-- import Control.Exception

type Env p = 𝕏 ⇰ Val p
type Vector v = 𝐿 v
type Matrix v = (ℕ ⇰ (ℕ ⇰ v))

-- helpers

iota :: ℕ → 𝐿 ℕ
iota n = 0 ⧺ (upTo n-1)

replicate :: ℕ → a → 𝐿 a
replicate len v = list $ build len v (\ x → x)

zipWith :: (a → b → c) → 𝐿 a → 𝐿 b → 𝐿 c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil
zipWith f (x:&xs) (y:&ys) = f x y :& zipWith f xs ys

take :: ℕ -> 𝐿 𝔻 -> 𝐿 𝔻
take 0 _ = Nil
take _ Nil= Nil
take n (x:&xs) = x :& take (n-1) xs

iterate :: (a -> a) -> a -> [a]
iterate f a = a : iterate f (f a)

--TODO:question
signum :: a -> a
signum x = case (x ⊑ zero) of
  False -> one
  True -> case (x ≡ zero) of
    False -> -1 × one
    True -> zero

norm_2 :: Vector 𝔻 -> ℕ
norm_2 = root ∘ sum ∘ map (\x -> x×x)

fst1 :: (a,b) -> a
fst1 (x,_) = x

snd1 :: (a,b) -> b
snd1 (_,x) = x

-- matrix ops

cols :: Matrix v → ℕ
cols a =
  let rws = list𝐼 (uniques (keys a)) in
    case rws of
      (x:&xs) → (dsize (a ⋕ x))
      _ → error "cols: empty matrix"

rows :: Matrix v → ℕ
rows = dsize

tr :: Matrix 𝔻 → Matrix 𝔻
tr m = fromLists $ transpose $ toRows m

transpose:: 𝐿 (𝐿 a) → 𝐿 (𝐿 a)
transpose (Nil:&_) = Nil
transpose m = (map head m) :& transpose (map tail m)

flatten :: Matrix 𝔻 → Vector 𝔻
flatten = concat

(<>) :: Matrix 𝔻 → Matrix 𝔻 → Matrix 𝔻
(<>) a b = [ [ sum $ zipWith (×) ar bc | bc <- (tr b) ] | ar <- a ]

scale :: 𝔻 → Vector 𝔻 → Model
scale r v = map (× r) v

--TODO: question
-- minimumBy :: ??
--
-- maximumBy :: ??
--
-- comparing :: ??
--
-- sndParse :: ??
--


vector :: 𝐿 𝔻 → Vector 𝔻
vector x = x

head :: 𝐿 a → a
head (x:&xs) = x
head _ = error "head failed"

tail :: 𝐿 a → 𝐿 a
tail (x:&xs) = xs
tail _ = error "tail failed"

-- sumElements :: 𝔻 → 𝔻

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
fromLists (x:&xs) = (buildCol (iota (count x)) x) ⧺ fromLists xs
fromLists Nil = Nil

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
  (mapLookup (iota (count colLists)) colLists)

-- TODO: question
mapLookup :: 𝐿 ℕ →  𝐿 (ℕ ⇰ a) → 𝐿 (𝐿 a)
mapLookup (i:&idxs) cols = (map ((⋕?) i) cols) ⧺ mapLookup idxs cols
mapLookup Nil cols = Nil

-- extract rows in N
(?) :: Matrix 𝔻 → [ℕ] → Matrix 𝔻
(?) m (n:&ns) = (m ⋕? n) ⩌ (m ? ns)
(?) m Nil = dø

toList :: Vector 𝔻 → 𝐿 𝔻
toList x = x

-- extracts the rows of a matrix as a list of vectors
toRows :: Matrix 𝔻 → 𝐿 (Vector 𝔻)
toRows m = (map values (values m))

-- creates a 1-row matrix from a vector
asRow :: Vector a -> Matrix a
asRow vec = 0 ↦ (buildCol (iota (count vec)) vec)

-- | Returns minimum elementParse
minElem ::  Ord b => [(a, b)] → a
-- TODO: ?
minElem = fst ∘ minimumBy (comparing snd {-sndParse-})

-- | Defining Val algebraic data type
data Val (p ∷ PRIV) =
  NatV ℕ
  | RealV 𝔻
  | PairV (Val p) (Val p)
  | SFunV 𝕏 (SExp p) (Env p)
  | PFunV (𝐿 𝕏) (PExp p) (Env p)
  | MatrixV (Matrix (Val p))
  deriving (Eq, Show)

-- | Converts and integer to a 𝔻
intDouble ∷ ℕ → 𝔻
intDouble = dbl

-- | Converts a natural number to a double
mkDouble ∷ ℕ → 𝔻
mkDouble = dbl

-- | Evaluates an expression from the sensitivity language
seval ∷ (Env p) → (SExp p) → (Val p)

-- literals
seval _ (ℕSE n)        = NatV n
seval _ (ℝSE n)        = RealV n
seval _ (ℝˢSE n)       = RealV n
seval _ (ℕˢSE n)       = NatV n
-- seval env (SRealNatE e) =
--   case (seval env e) of
--     (NatV n) → RealV $ mkDouble n

-- variables
seval env (VarSE x) | x ∈ env  = env ⋕! x
                    | otherwise         = error $ "Unknown variable: " ⧺ (chars x) ⧺ " in environment with bound vars " ⧺ (chars $ show $ keys env)

-- arithmetic
seval env (PlusSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ + v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ + v₂)
    (a, b) → error $ "No pattern for " ⧺ (show (a, b))

seval env (MinusSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ - v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ - v₂)
    (a, b) → error $ "No pattern for " ⧺ (show (a, b))

seval env (TimesSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ <> v₂)
    (RealV v₁, MatrixV v₂) → MatrixV (scale v₁ v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ × v₂)
    (a, b) → error $ "No pattern for " ⧺ (show (a, b))

seval env (DivSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (RealV v₁, RealV v₂) → RealV (v₁ / v₂)
    (a, b) → error $ "No pattern for " ⧺ (show (a, b))

-- matrix operations
seval env (MRowsSE e) =
  case (seval env e) of (MatrixV v) →
                         NatV $ nat $ rows v

seval env (MColsSE e) =
  case (seval env e) of (MatrixV v) →
                         NatV $ nat $ cols v

seval env (IdxSE e) =
  case seval env e of
    (NatV d) →
      let posMat ∷ Matrix 𝔻 = ident d
          negMat ∷ Matrix 𝔻 = scale (-1.0) posMat
      in MatrixV (posMat === negMat)

-- seval env (SMTrE e) =
--   case seval env e of (MatrixV m) → MatrixV $ tr m

-- clip operation for only L2 norm
seval env (MClipSE norm e) =
  case (norm, seval env e) of
    (L2,   MatrixV v) →  MatrixV $ fromRows (map normalize $ toRows v)
    (LInf, MatrixV v) →  MatrixV $ fromRows (map normalize $ toRows v)
    (l, _) → error $ "Invalid norm for clip: " ⧺ (show l)

-- gradient
seval env (MLipGradSE LR e₁ e₂ e₃) =
  case (seval env e₁, seval env e₂, seval env e₃) of
    (MatrixV θ, MatrixV xs, MatrixV ys) →
      case ((rows θ ≡ 1) ⩓ (rows ys ≡ 1)) of
        True →
          let θ'  ∷ Vector 𝔻 = flatten θ
              ys' ∷ Vector 𝔻 = flatten ys
          in MatrixV $ asRow $ ngrad θ' xs ys'
        False →
          error $ "Incorrect matrix dimensions for gradient: " ⧺ (show (rows θ, rows ys))
    (a, b, c) → error $ "No pattern for " ⧺ (show (a, b, c))

-- create matrix
seval env (MCreateSE l e₁ e₂ i j e₃) =
  case (seval env e₁, seval env e₂) of
    (NatV v₁, NatV v₂) →
      MatrixV $ (><) (int v₁) (int v₂) $ replicate (int $ v₁ × v₂) 0.0

-- functions and application
seval env (PFunSE _ args body) =
  PFunV (map fst args) body env

seval env (SFunSE x _ body) =
  SFunV x body env

seval env (AppSE e₁ e₂) =
  case seval env e₁ of
    (SFunV x body env') →
      let env'' = (x ↦ (seval env e₂)) ⩌ env'
      in seval env'' body

-- error
seval env e = error $ "Unknown expression: " ⧺ (show e)

-- | Evaluates an expression from the privacy language
peval ∷ Env p → PExp p → IO (Val p)

-- bind and application
peval env (BindPE x e₁ e₂) = do
  v₁ ← peval env e₁
  v₂ ← peval (x ↦ v₁ ⩌ env) e₂
  return v₂

peval env (AppPE _ f vars) =
  case seval env f of
    (PFunV args body env') →
      let vs    ∷ [Val] = map ((⋕!) env) vars
          --TODO: question
          env'' ∷ Env p = foldr (\(var, val) → (⩌ (var ↦ val))) env' (zip args vs)
      in peval env'' body

-- sample on two matrices and compute on sample
peval env (SamplePE size xs ys x y e) =
  case (seval env size, env ⋕! xs, env ⋕! ys) of
    (NatV n, MatrixV v1, MatrixV v2) →
      sampleHelper n v1 v2 x y e env

-- gaussian mechanism for real numbers
peval env (GaussPE r (EDGaussParams ε δ) vs e) =
  case (seval env r, seval env ε, seval env  δ, seval env e) of
    (RealV r', RealV ε', RealV δ', RealV v) → do
      r ← gaussianNoise 0 (r' × (root $ 2 × (log $ 1.25/δ')) / ε')
      return $ RealV $ v + r
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show (a,b,c,d))

-- gaussian mechanism for matrices
peval env (MGaussPE r (EDGaussParams ε δ) vs e) =
  case (seval env r, seval env ε, seval env  δ, seval env e) of
    (RealV r', RealV ε', RealV δ', MatrixV mat) → do
      let σ = (r' × (root $ 2 × (log $ 1.25/δ')) / ε')
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists mat
      return $ MatrixV $ fromLists mat'
    (a, b, c, d) → error $ "No pattern for: " ⧺ (show (a,b,c,d))

-- evaluate finite iteration
peval env (LoopPE k init xs x₁ x₂ e) =
  case (seval env k, seval env init) of
    (NatV k', initV) →
      iter₁ k' initV x₁ x₂ 0 e env

-- evaluate sensitivity expression and return in the context of the privacy language
peval env (ReturnPE e) =
  return $ seval env e

-- exponential mechanism
-- TODO: question
peval env (ExponentialPE s ε xs x body) =
  case (seval env s, seval env ε, seval env xs) of
    (RealV s', RealV ε', MatrixV xs') →
      let xs''     = map (\row' → fromLists [row']) $ toLists xs'
          envs     = map (\m → (x ↦ (MatrixV m)) ⩌ env) xs''
          getScore = \env1 → case seval env1 body of
            (RealV   r) → r
            (MatrixV m) | size m == (1, 1) → head $ head $ toLists m
            a → error $ "Invalid score: " ⧺ (chars $ sho a)
          scores   = map getScore envs
          δ'       = 1e-5
          σ        = (s' × (root $ 2 × (log $ 1.25/δ')) / ε')
      in do
        scores' ← mapM (\score → gaussianNoise score σ) scores
        return $ MatrixV $ minElem (zip xs'' scores')

-- error
peval env e = error $ "Unknown expression: " ⧺ (show e)


-- | Helper function for loop expressions
iter₁ ∷ ℕ → Val p → 𝕏 → 𝕏 → ℕ → PExp p → Env p → IO (Val p)
iter₁ 0 v _ _ _ _ _ = return v
iter₁ k v t x kp body env = do
  newVal ← peval ((x ↦ v) ⩌ ((t ↦ (NatV $ nat kp)) ⩌ env)) body
  iter₁ (k - 1) newVal t x (kp+1) body env

-- | Empty environment
emptyEnv ∷ Env p
emptyEnv = dø

-- | Read in a dataset and return xs (features) and ys (labels)
readDataSet ∷ 𝕊 → IO (Matrix 𝔻, Vector 𝔻)
readDataSet fileName = do
    Inr(mat) ← parseCSVtoMatrix fileName
    let dataCols ∷ 𝐿 (Vector 𝔻) = toColumns mat
        xs ∷ Matrix 𝔻 = fromColumns $ tail dataCols
        ys ∷ Vector 𝔻 = head dataCols
    return $ (xs, ys)

-- | Place a dataset into the environment
insertDataSet ∷ Env p → (𝕏, 𝕏) → (Matrix 𝔻, Vector 𝔻) → Env p
insertDataSet env (x, y) (xs, ys) =
  ((x ↦ (MatrixV (mapp RealV xs))) ⩌ ((y ↦ (MatrixV $ asRow (map RealV ys))) ⩌ env))

-- | Samples a normal distribution and returns a single value
gaussianNoise ∷ 𝔻 → 𝔻 → IO 𝔻
gaussianNoise c v = normalIO'(c, v)

-- | Helper function for PSampleE
sampleHelper :: ℕ → Matrix 𝔻 → Matrix  𝔻 → 𝕏 → 𝕏 → PExp p → Env p → IO (Val p)
sampleHelper n xs ys x y e env = do
  batch <- minibatch (int n) xs (flatten ys)
  peval (insertDataSet env (x, y) ((fst1 batch), (snd1 batch))) e

-- GRADIENT --

type Model = Vector 𝔻

-- | Converts an Integral number to a double
dbl₁ ∷ ℕ → 𝔻
dbl₁ = dbl

-- | Calculates LR loss
loss ∷ Model → Matrix 𝔻 → Vector 𝔻 → 𝔻
loss θ x y =
  let θ'       ∷ Matrix 𝔻 = asColumn θ
      y'       ∷ Matrix 𝔻 = asColumn y
      exponent ∷ Matrix 𝔻 = -((x <> θ') × y')
      -- TODO: what are sumElements and exp?
  in {-(sumElements -} (log (1.0 + (exp exponent))) / (dbl₁ $ rows x)

-- | Averages LR gradient over the whole matrix of examples
ngrad ∷ Model → Matrix 𝔻 → Vector 𝔻 → Vector 𝔻
ngrad θ x y =
  let θ'       ∷ Matrix 𝔻 = asColumn θ
      y'       ∷ Matrix 𝔻 = asColumn y
      exponent ∷ Matrix 𝔻 = (x <> θ') × y' --TODO: question
      scaled   ∷ Matrix 𝔻 = y' × (1.0/(1.0+exp(exponent)))
      gradSum  ∷ Matrix 𝔻 = (tr x) <> scaled
      avgGrad  ∷ Vector 𝔻 = flatten $ scale (1.0/(dbl $ rows x)) gradSum
  in (- avgGrad)

-- | Obtains a vector in the same direction with L2-norm=1
normalize :: Vector 𝔻 → Vector 𝔻
normalize v
  | r > 1     =  scale (1/r) v
  | otherwise =  v
  where
    r = norm_2 v

-- | Convert a string into a double
readStr ∷ 𝕊 → 𝔻
readStr s = case (read𝕊 s) of
  [(d, _)] → d
  _ → 0.0

-- | Reads a CSV into a matrix
parseCSVtoMatrix ∷ FilePath → IO (ParseError ∨ (Matrix 𝔻))
parseCSVtoMatrix file = do
  Inr(csv) ← parseCSVFromFile file
  let csvList ∷ 𝐿 (𝐿 𝔻) = map (map readStr) csv
      matrix ∷ Matrix 𝔻 = fromLists csvList
  return $ return matrix

-- | Performs gradient descent with a fixed learning rate
gradientDescent ∷ ℕ → Model → Matrix 𝔻 → Vector 𝔻 → 𝔻 → Model
gradientDescent 0 θ x y η = θ
gradientDescent n θ x y η = let θ' = θ - (scale η $ ngrad θ x y)
                            in trace ("training iter " ⧺ (show n) ⧺
                                      ", loss : " ⧺ (show $ loss θ x y))
                               gradientDescent (n-1) θ' x y η

-- | Makes a single prediction
predict ∷ Model → (Vector 𝔻, 𝔻) → 𝔻
predict θ (x, y) = signum $ x <.> θ

isCorrect ∷ (𝔻, 𝔻) → (ℕ, ℕ)
isCorrect (prediction, actual) | prediction == actual = (1, 0)
                               | otherwise = (0, 1)

-- | Converts a matrix to a model (flatten it)
toModel ∷ Matrix 𝔻 → Model
toModel = flatten

-- | Calculates the accuracy of a model
accuracy ∷ Matrix 𝔻 → Vector 𝔻 → Model → (ℕ, ℕ)
accuracy x y θ = let pairs ∷ 𝐿 (Vector 𝔻, 𝔻) = zip (map normalize $ toRows x) (toList y)
                     labels ∷ 𝐿 𝔻 = map (predict θ) pairs
                     correct ∷ 𝐿 (ℕ, ℕ) = map isCorrect $ zip labels (toList y)
                 in fold (0, 0) (\a b → (fst a + fst b, snd a + snd b)) correct

-- | Ensures that labels are either 1 or -1
fixLabel ∷ 𝔻 → 𝔻
fixLabel x | x ≡ -1.0 = -1.0
           | x ≡ 1.0 = 1.0
           | otherwise = trace ("Unexpected label: " ⧺ (show x)) x

-- END GRADIENT --

-- MINIBATCHGRADIENT --

-- | Generates random indicies for sampling
randIndices :: ℕ → ℕ → ℕ → GenIO → IO [ℕ]
randIndices n a b gen
  | n == 0    = return []
  | otherwise = do
      x <- uniformR (a, b) gen
      xs' <- randIndices (n - 1) a b gen
      return (x : xs')

-- | Outputs a single minibatch of data
minibatch :: ℤ → Matrix 𝔻 → Vector 𝔻 → IO (Matrix 𝔻, Vector 𝔻)
minibatch batchSize xs ys = do
  gen <- createSystemRandom
  idxs <- randIndices batchSize 0 (rows xs - 1) gen
  let bxs = xs ? idxs
      bys = head $ toColumns $ (asColumn ys) ? idxs
  return (bxs, bys)

-- | Generates a list of minibatches
nminibatch :: ℕ → ℕ → Matrix 𝔻 → Vector 𝔻 → IO [(Matrix 𝔻, Vector 𝔻)]
nminibatch n batchSize x y
  | n == 0    = return []
  | otherwise = do
      x' <- minibatch batchSize x y
      xs <- nminibatch (n - 1) batchSize x y
      return (x' : xs)

-- | Returns an infinite list of random values sampled from a normal distribution
noise :: ℕ → ℕ → 𝔻 → 𝔻 → 𝔻 → IO [𝔻]
noise n iters lreg eps delta =
  let stdDev = 4 × lreg × (root (dbl(iters) × (log (1 / delta)))) / (dbl(n) × eps)
  in normalsIO' (0, stdDev)

-- | Generates a list of random numbers sampled from a [0, 1) uniform distribution
randUniform :: ℕ → IO[𝔻]
randUniform n
  | n ≡ 0    = return []
  | otherwise = do
      x <- randomIO
      xs <- randUniform (n - 1)
      return (x : xs)

-- | Initializes model and regularization parameter
initModel :: ℕ → 𝔻 → 𝔻 → 𝑂 𝔻 →  IO (Vector 𝔻, 𝔻)
initModel m l lambda l2 = do
  rand <- randUniform m
  case (lambda, l2) of
    (0, None) → return (fromList $ replicate m 0.0, l)
    (lambda, Some l2) | lambda > 0 →
      return ((scale (2 × l2) (vector (map (- 0.5) rand))), l + lambda×l2)
    otherwise → return (fromList $ replicate m 0.0, 0)

-- | Runs gradient descent on an initial model and a set of minibatches
mbgradientDescent :: ℕ → ℕ  → Model → [(Matrix 𝔻, Vector 𝔻)] → 𝔻 →  [𝔻] → Model
mbgradientDescent 0 m theta batches rate noise = theta
mbgradientDescent n m theta batches rate noise =
  let x = (fst (head batches))
      y = (snd (head batches))
      grad = ((ngrad theta x y) + (vector (take m noise)))
      theta' = theta - (scale rate grad)
  in trace ("training iter " ⧺ (show n) ⧺
               ", loss : " ⧺ (show $ loss theta x y) ⧺
               ", noise :" ⧺ (show $ take 5 noise))
     mbgradientDescent (n - 1) m theta' (tail batches) rate noise

{- | Runs differentially private, minibatch gradient descent on input matrices
     `x` and `y` and a set of input parameters.
-}
privateMBSGD :: Matrix 𝔻
            → Vector 𝔻
            → 𝔻
            → 𝔻
            → ℕ
            → 𝔻
            → 𝔻
            → ℕ
            → 𝔻
            → 𝑂 𝔻
            → IO Model
privateMBSGD x y eps delta iters learningRate l batchSize lambda l2 = do
  init <- initModel (cols x) l lambda l2
  normalNoise <- noise (rows x) iters (snd init) eps delta
  minibatches <- nminibatch iters batchSize x y
  return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate normalNoise)

-- | Runs noiseless minibatch gradient descent.
mbSGD :: Matrix 𝔻
            → Vector 𝔻
            → 𝔻
            → 𝔻
            → ℕ
            → 𝔻
            → 𝔻
            → ℕ
            → 𝔻
            → 𝑂 𝔻
            → IO Model
mbSGD x y eps delta iters learningRate l batchSize lambda l2 = do
  init <- initModel (cols x) l lambda l2
  minibatches <- nminibatch iters batchSize x y
  return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate (iterate (+0.0) 0))

-- END MINIBATCHGRADIENT --
