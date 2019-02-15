{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MinibatchGradient where

-- libraries
-- import Numeric.LinearAlgebra
-- import Data.Random.Normal
-- import System.Random
-- import System.Environment
-- import Debug.Trace
-- import System.Random.MWC

-- our code
import Gradient hiding (main, runtest)


-- | Generates random indicies for sampling
randIndices :: Int -> Int -> Int -> GenIO -> IO [Int]
randIndices n a b gen
  | n == 0    = return []
  | otherwise = do
      x <- uniformR (a, b) gen
      xs' <- randIndices (n - 1) a b gen
      return (x : xs')

-- | Outputs a single minibatch of data
minibatch :: Int -> Matrix Double -> Vector Double -> IO (Matrix Double, Vector Double)
minibatch batchSize xs ys = do
  gen <- createSystemRandom
  idxs <- randIndices batchSize 0 (rows xs - 1) gen
  let bxs = xs ? idxs
      bys = head $ toColumns $ (asColumn ys) ? idxs
  return (bxs, bys)

-- | Generates a list of minibatches
nminibatch :: Int -> Int -> Matrix Double -> Vector Double -> IO [(Matrix Double, Vector Double)]
nminibatch n batchSize x y
  | n == 0    = return []
  | otherwise = do
      x' <- minibatch batchSize x y
      xs <- nminibatch (n - 1) batchSize x y
      return (x' : xs)

-- | Returns an infinite list of random values sampled from a normal distribution
noise :: Int -> Int -> Double -> Double -> Double -> IO [Double]
noise n iters lreg eps delta =
  let stdDev = 4 * lreg * (sqrt (fromIntegral(iters) * (log (1 / delta)))) / (fromIntegral(n) * eps)
  in normalsIO' (0, stdDev)

-- | Generates a list of random numbers sampled from a [0, 1) uniform distribution
randUniform :: Int -> IO[Double]
randUniform n
  | n == 0    = return []
  | otherwise = do
      x <- randomIO
      xs <- randUniform (n - 1)
      return (x : xs)

-- | Initializes model and regularization parameter
initModel :: Int -> Double -> Double -> Maybe Double ->  IO (Vector Double, Double)
initModel m l lambda l2 = do
  rand <- randUniform m
  case (lambda, l2) of
    (0, Nothing) -> return (fromList $ replicate m 0.0, l)
    (lambda, Just l2) | lambda > 0 ->
      return ((scale (2 * l2) (vector (map (subtract 0.5) rand))), l + lambda*l2)
    otherwise -> return (fromList $ replicate m 0.0, 0)

-- | Runs gradient descent on an initial model and a set of minibatches
mbgradientDescent :: Int -> Int  -> Model -> [(Matrix Double, Vector Double)] -> Double ->  [Double] -> Model
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
privateMBSGD :: Matrix Double
            -> Vector Double
            -> Double
            -> Double
            -> Int
            -> Double
            -> Double
            -> Int
            -> Double
            -> Maybe Double
            -> IO Model
privateMBSGD x y eps delta iters learningRate l batchSize lambda l2 = do
  init <- initModel (cols x) l lambda l2
  normalNoise <- noise (rows x) iters (snd init) eps delta
  minibatches <- nminibatch iters batchSize x y
  return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate normalNoise)

-- | Runs noiseless minibatch gradient descent.
mbSGD :: Matrix Double
            -> Vector Double
            -> Double
            -> Double
            -> Int
            -> Double
            -> Double
            -> Int
            -> Double
            -> Maybe Double
            -> IO Model
mbSGD x y eps delta iters learningRate l batchSize lambda l2 = do
  init <- initModel (cols x) l lambda l2
  minibatches <- nminibatch iters batchSize x y
  return (mbgradientDescent iters (cols x) (fst init) minibatches learningRate (iterate (+0.0) 0))

-- | Runs the test
runtest args = do
  putStrLn "loading data"
  Right(mat) ← parseCSVtoMatrix (head args)
  let dataCols :: [Vector Double] = toColumns mat
      x :: Matrix Double = fromColumns $ tail dataCols
      y :: Vector Double = cmap fixLabel $ head dataCols
  putStrLn "done loading data; running training"
  do
    -- toy parameters
    θ <- privateMBSGD x y 0.01 0.01 100 0.1 1 50 0 Nothing
    putStrLn "done running training; running accuracy"
    let (correct, incorrect) = accuracy x y θ
    putStrLn $ "Accuracy: " ++
      (show $ (dbl correct) / (dbl $ correct + incorrect))


{- | Test privateMBSGD on toy data
     Examples:
     wget https://people.eecs.berkeley.edu/~jnear/files/adult_train.csv
     wget wget https://people.eecs.berkeley.edu/~jnear/files/adult_test.csv
-}
main :: IO ()
main = do
  args <- getArgs
  runtest args
  putStrLn "done"
