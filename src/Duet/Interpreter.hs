module Duet.Interpreter where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF
import Duet.Quantity

-- libraries
-- import Text.CSV
-- import Text.Parsec.Error
-- import System.Environment
-- import Debug.Trace
-- import Numeric.Natural
-- import Control.Exception
-- import Data.Random.Normal

type Env = 𝕏 ⇰ Val
type Vector v = 𝐿 v
type Matrix v = (ℕ ⇰ (ℕ ⇰ v))

-- | Returns maximum element
maxElem ::  Ord b => [(a, b)] -> a
maxElem = fst . maximumBy (comparing snd)

-- | Returns minimum element
minElem ::  Ord b => [(a, b)] -> a
minElem = fst . minimumBy (comparing snd)

-- | Defining Val algebraic data type
data Val =
  NatV Natural
  | RealV 𝔻
  | PairV Val Val
  | SFunV 𝕏 SExp Env
  | PFunV [𝕏] PExp Env
  | MatrixV (Matrix Val)
  deriving (Eq, Show)

-- | Converts and integer to a 𝔻
intDouble ∷ ℕ → 𝔻
intDouble = fromIntegral

-- | Converts a natural number to a double
mkDouble ∷ Natural → 𝔻
mkDouble = fromIntegral

-- | Evaluates an expression from the sensitivity language
seval ∷ Env → SExp → Val

-- literals
seval _ (ℕSE n)        = NatV n
seval _ (ℝSE n)        = RealV n
seval _ (ℝˢSE n)       = RealV n
seval _ (ℕˢSE n)       = NatV n
seval env (SRealNatE e) =
  case (seval env e) of
    (NatV n) -> RealV $ mkDouble n

-- variables
seval env (VarSE x) | x ∈ env  = env ⋕! x
                    | otherwise         = error $ "Unknown variable: " ++ (chars x) ++ " in environment with bound vars " ++ (chars $ sho $ keys env)

-- arithmetic
seval env (PlusSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ + v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ + v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

seval env (MinusSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ - v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ - v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

seval env (TimesSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ <> v₂)
    (RealV v₁, MatrixV v₂) → MatrixV (scale v₁ v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ * v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

seval env (DivSE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (RealV v₁, RealV v₂) → RealV (v₁ / v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

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
      let posMat ∷ Matrix 𝔻 = ident $ int d
          negMat ∷ Matrix 𝔻 = scale (-1.0) posMat
      in MatrixV (posMat === negMat)

seval env (SMTrE e) =
  case seval env e of (MatrixV m) → MatrixV $ tr m

-- clip operation for only L2 norm
seval env (MClipSE norm e) =
  case (norm, seval env e) of
    (L2,   MatrixV v) →  MatrixV $ fromRows (map normalize $ toRows v)
    (LInf, MatrixV v) →  MatrixV $ fromRows (map normalize $ toRows v)
    (l, _) → error $ "Invalid norm for clip: " ++ (show l)

-- gradient
seval env (SGradE LR _ e₁ e₂ e3) =
  case (seval env e₁, seval env e₂, seval env e3) of
    (MatrixV θ, MatrixV xs, MatrixV ys) →
      if (rows θ == 1 && rows ys == 1)
      then
        let θ'  ∷ Vector 𝔻 = flatten θ
            ys' ∷ Vector 𝔻 = flatten ys
        in MatrixV $ asRow $ ngrad θ' xs ys'
      else
        error $ "Incorrect matrix dimensions for gradient: " ++ (show (rows θ, rows ys))
    (a, b, c) → error $ "No pattern for " ++ (show (a, b, c))

-- create matrix
seval env (MCreateSE l e₁ e₂ i j e₃) =
  case (seval env e₁, seval env e₂) of
    (NatV v₁, NatV v₂) →
      MatrixV $ (><) (int v₁) (int v₂) $ replicate (int $ v₁ * v₂) 0.0

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
seval env e = error $ "Unknown expression: " ++ (show e)

-- | Evaluates an expression from the privacy language
peval ∷ Env → PExp → IO Val

-- bind and application
peval env (BindPE x e₁ e₂) = do
  v₁ ← peval env e₁
  v₂ ← peval (x ↦ v₁ ⩌ env) e₂
  return v₂

peval env (AppPE _ f vars) =
  case seval env f of
    (PFunV args body env') →
      let vs    ∷ [Val] = map ((⋕!) env) vars
          env'' ∷ Env   = foldr (\(var, val) → Map.insert var val) env' (zip args vs)
      in peval env'' body

-- sample on two matrices and compute on sample
peval env (SamplePE size xs ys x y e) =
  case (seval env size, env ⋕! xs, env ⋕! ys) of
    (NatV n, MatrixV v1, MatrixV v2) ->
      sampleHelper n v1 v2 x y e env

-- gaussian mechanism for real numbers
peval env (GaussPE r ε δ vs e) =
  case (seval env r, seval env ε, seval env  δ, seval env e) of
    (RealV r', RealV ε', RealV δ', RealV v) → do
      r ← gaussianNoise 0 (r' * (sqrt $ 2 * (log $ 1.25/δ')) / ε')
      return $ RealV $ v + r
    (a, b, c, d) → error $ "No pattern for: " ++ (show (a,b,c,d))

-- gaussian mechanism for matrices
peval env (MGaussPE r ε δ vs e) =
  case (seval env r, seval env ε, seval env  δ, seval env e) of
    (RealV r', RealV ε', RealV δ', MatrixV mat) → do
      let σ = (r' * (sqrt $ 2 * (log $ 1.25/δ')) / ε')
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists mat
      return $ MatrixV $ fromLists mat'
    (a, b, c, d) → error $ "No pattern for: " ++ (show (a,b,c,d))

-- evaluate finite iteration
peval env (LoopPE δ' k init xs x₁ x₂ e) =
  case (seval env k, seval env init) of
    (NatV k', initV) →
      iter k' initV x₁ x₂ 0 e env

-- evaluate sensitivity expression and return in the context of the privacy language
peval env (ReturnPE e) =
  return $ seval env e

-- exponential mechanism
peval env (ExponentialPE s ε xs x body) =
  case (seval env s, seval env ε, seval env xs) of
    (RealV s', RealV ε', MatrixV xs') →
      let xs''     = map (\row' → fromLists [row']) $ toLists xs'
          envs     = map (\m → Map.insert x (MatrixV m) env) xs''
          getScore = \env1 → case seval env1 body of
            (RealV   r) → r
            (MatrixV m) | size m == (1, 1) → head $ head $ toLists m
            a → error $ "Invalid score: " ++ (chars $ sho a)
          scores   = map getScore envs
          δ'       = 1e-5
          σ        = (s' * (sqrt $ 2 * (log $ 1.25/δ')) / ε')
      in do
        scores' ← mapM (\score → gaussianNoise score σ) scores
        --putStrLn $ "picked: " ++ (show $ maxElem (zip xs'' scores))
        return $ MatrixV $ minElem (zip xs'' scores')

-- error
peval env e = error $ "Unknown expression: " ++ (show e)


-- | Helper function for loop expressions
iter ∷ Natural → Val → 𝕏 → 𝕏 → ℕ → PExp → Env → IO Val
iter 0 v _ _ _ _ _ = return v
iter k v t x kp body env = do
  newVal ← peval (x ↦ v ⩌ (t ↦ (NatV $ nat kp) ⩌ env) body)
  iter (k - 1) newVal t x (kp+1) body env

-- | Empty environment
emptyEnv ∷ Env
emptyEnv = dø

-- | Read in a dataset and return xs (features) and ys (labels)
readDataSet ∷ 𝕊 → IO (Matrix 𝔻, Vector 𝔻)
readDataSet fileName = do
    Right(mat) ← parseCSVtoMatrix fileName
    let dataCols ∷ [Vector 𝔻] = toColumns mat
        xs ∷ Matrix 𝔻 = fromColumns $ tail dataCols
        ys ∷ Vector 𝔻 = head dataCols
    return $ (xs, ys)

-- | Place a dataset into the environment
insertDataSet ∷ Env → (𝕏, 𝕏) → (Matrix 𝔻, Vector 𝔻) → Env
insertDataSet env (x, y) (xs, ys) =
  (x ↦ (MatrixV xs) ⩌ (y ↦ (MatrixV $ asRow ys) ⩌ env))

-- | Samples a normal distribution and returns a single value
gaussianNoise ∷ 𝔻 → 𝔻 → IO 𝔻
gaussianNoise c v = normalIO'(c, v)

-- | Helper function for PSampleE
sampleHelper :: Natural -> Matrix 𝔻 -> Matrix  𝔻 -> 𝕏 -> 𝕏 -> PExp -> Env -> IO Val
sampleHelper n xs ys x y e env = do
  batch <- minibatch (int n) xs (flatten ys)
  peval (insertDataSet env (x, y) ((fst batch), (snd batch))) e

-- GRADIENT --

type Model = Vector 𝔻

-- | Converts an Integral number to a double
dbl ∷ (Integral a) ⇒ a → 𝔻
dbl = fromIntegral

-- | Calculates LR loss
loss ∷ Model → Matrix 𝔻 → Vector 𝔻 → 𝔻
loss θ x y =
  let θ'       ∷ Matrix 𝔻 = asColumn θ
      y'       ∷ Matrix 𝔻 = asColumn y
      exponent ∷ Matrix 𝔻 = -((x <> θ') * y')
  in (sumElements (log (1.0 + (exp exponent)))) / (dbl $ rows x)

-- | Averages LR gradient over the whole matrix of examples
ngrad ∷ Model → Matrix 𝔻 → Vector 𝔻 → Vector 𝔻
ngrad θ x y =
  let θ'       ∷ Matrix 𝔻 = asColumn θ
      y'       ∷ Matrix 𝔻 = asColumn y
      exponent ∷ Matrix 𝔻 = (x <> θ') * y'
      scaled   ∷ Matrix 𝔻 = y' * (1.0/(1.0+exp(exponent)))
      gradSum  ∷ Matrix 𝔻 = (tr x) <> scaled
      avgGrad  ∷ Vector 𝔻 = flatten $ scale (1.0/(dbl $ rows x)) gradSum
  in (- avgGrad)

-- | Obtains a vector in the same direction with L2-norm=1
normalize :: Vector 𝔻 -> Vector 𝔻
normalize v
  | r > 1     =  scale (1/r) v
  | otherwise =  v
  where
    r = norm_2 v

-- | Convert a string into a double
readStr ∷ 𝕊 → 𝔻
readStr s = case (reads s) of
  [(d, _)] → d
  _ → 0.0

-- | Reads a CSV into a matrix
parseCSVtoMatrix ∷ FilePath → IO (Either ParseError (Matrix 𝔻))
parseCSVtoMatrix file = do
  Right(csv) ← parseCSVFromFile file
  let csvList ∷ [[𝔻]] = map (map readStr) csv
      matrix ∷ Matrix 𝔻 = fromLists csvList
  return $ return matrix

-- | Performs gradient descent with a fixed learning rate
gradientDescent ∷ ℕ → Model → Matrix 𝔻 → Vector 𝔻 → 𝔻 → Model
gradientDescent 0 θ x y η = θ
gradientDescent n θ x y η = let θ' = θ - (scale η $ ngrad θ x y)
                            in trace ("training iter " ++ (show n) ++
                                      ", loss : " ++ (show $ loss θ x y))
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
accuracy x y θ = let pairs ∷ [(Vector 𝔻, 𝔻)] = zip (map normalize $ toRows x) (toList y)
                     labels ∷ [𝔻] = map (predict θ) pairs
                     correct ∷ [(ℕ, ℕ)] = map isCorrect $ zip labels (toList y)
                 in foldl' (\a b → (fst a + fst b, snd a + snd b)) (0, 0) correct

-- | Ensures that labels are either 1 or -1
fixLabel ∷ 𝔻 → 𝔻
fixLabel x | x == -1.0 = -1.0
           | x == 1.0 = 1.0
           | otherwise = trace ("Unexpected label: " ++ (show x)) x

-- END GRADIENT --

-- MINIBATCHGRADIENT --

-- | Generates random indicies for sampling
randIndices :: ℕ -> ℕ -> ℕ -> GenIO -> IO [ℕ]
randIndices n a b gen
  | n == 0    = return []
  | otherwise = do
      x <- uniformR (a, b) gen
      xs' <- randIndices (n - 1) a b gen
      return (x : xs')

-- | Outputs a single minibatch of data
minibatch :: ℕ -> Matrix 𝔻 -> Vector 𝔻 -> IO (Matrix 𝔻, Vector 𝔻)
minibatch batchSize xs ys = do
  gen <- createSystemRandom
  idxs <- randIndices batchSize 0 (rows xs - 1) gen
  let bxs = xs ? idxs
      bys = head $ toColumns $ (asColumn ys) ? idxs
  return (bxs, bys)

-- | Generates a list of minibatches
nminibatch :: ℕ -> ℕ -> Matrix 𝔻 -> Vector 𝔻 -> IO [(Matrix 𝔻, Vector 𝔻)]
nminibatch n batchSize x y
  | n == 0    = return []
  | otherwise = do
      x' <- minibatch batchSize x y
      xs <- nminibatch (n - 1) batchSize x y
      return (x' : xs)

-- | Returns an infinite list of random values sampled from a normal distribution
noise :: ℕ -> ℕ -> 𝔻 -> 𝔻 -> 𝔻 -> IO [𝔻]
noise n iters lreg eps delta =
  let stdDev = 4 * lreg * (sqrt (fromIntegral(iters) * (log (1 / delta)))) / (fromIntegral(n) * eps)
  in normalsIO' (0, stdDev)

-- | Generates a list of random numbers sampled from a [0, 1) uniform distribution
randUniform :: ℕ -> IO[𝔻]
randUniform n
  | n == 0    = return []
  | otherwise = do
      x <- randomIO
      xs <- randUniform (n - 1)
      return (x : xs)

-- | Initializes model and regularization parameter
initModel :: ℕ -> 𝔻 -> 𝔻 -> 𝑂 𝔻 ->  IO (Vector 𝔻, 𝔻)
initModel m l lambda l2 = do
  rand <- randUniform m
  case (lambda, l2) of
    (0, None) -> return (fromList $ replicate m 0.0, l)
    (lambda, Some l2) | lambda > 0 ->
      return ((scale (2 * l2) (vector (map (subtract 0.5) rand))), l + lambda*l2)
    otherwise -> return (fromList $ replicate m 0.0, 0)

-- | Runs gradient descent on an initial model and a set of minibatches
mbgradientDescent :: ℕ -> ℕ  -> Model -> [(Matrix 𝔻, Vector 𝔻)] -> 𝔻 ->  [𝔻] -> Model
mbgradientDescent 0 m theta batches rate noise = theta
mbgradientDescent n m theta batches rate noise =
  let x = (fst (head batches))
      y = (snd (head batches))
      grad = ((ngrad theta x y) + (vector (take m noise)))
      theta' = theta - (scale rate grad)
  in trace ("training iter " ++ (show n) ++
               ", loss : " ++ (show $ loss theta x y) ++
               ", noise :" ++ (show $ take 5 noise))
     mbgradientDescent (n - 1) m theta' (tail batches) rate noise

{- | Runs differentially private, minibatch gradient descent on input matrices
     `x` and `y` and a set of input parameters.
-}
privateMBSGD :: Matrix 𝔻
            -> Vector 𝔻
            -> 𝔻
            -> 𝔻
            -> ℕ
            -> 𝔻
            -> 𝔻
            -> ℕ
            -> 𝔻
            -> 𝑂 𝔻
            -> IO Model
privateMBSGD x y eps delta iters learningRate l batchSize lambda l2 = do
  init <- initModel (cols x) l lambda l2
  normalNoise <- noise (rows x) iters (snd init) eps delta
  minibatches <- nminibatch iters batchSize x y
  return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate normalNoise)

-- | Runs noiseless minibatch gradient descent.
mbSGD :: Matrix 𝔻
            -> Vector 𝔻
            -> 𝔻
            -> 𝔻
            -> ℕ
            -> 𝔻
            -> 𝔻
            -> ℕ
            -> 𝔻
            -> 𝑂 𝔻
            -> IO Model
mbSGD x y eps delta iters learningRate l batchSize lambda l2 = do
  init <- initModel (cols x) l lambda l2
  minibatches <- nminibatch iters batchSize x y
  return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate (iterate (+0.0) 0))

-- END MINIBATCHGRADIENT --
