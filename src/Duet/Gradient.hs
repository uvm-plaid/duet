{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Duet.Gradient where

-- libraries
-- import Prelude hiding ((<>))
-- import Data.List
-- import Numeric.LinearAlgebra hiding (normalize)
-- import Text.CSV
-- import Text.Parsec.Error
-- import System.Environment
-- import Debug.Trace

type Model = Vector Double

-- | Converts an Integral number to a double
dbl ∷ (Integral a) ⇒ a → Double
dbl = fromIntegral

-- | Calculates LR loss
loss ∷ Model → Matrix Double → Vector Double → Double
loss θ x y =
  let θ'       ∷ Matrix Double = asColumn θ
      y'       ∷ Matrix Double = asColumn y
      exponent ∷ Matrix Double = -((x <> θ') * y')
  in (sumElements (log (1.0 + (exp exponent)))) / (dbl $ rows x)

-- | Averages LR gradient over the whole matrix of examples
ngrad ∷ Model → Matrix Double → Vector Double → Vector Double
ngrad θ x y =
  let θ'       ∷ Matrix Double = asColumn θ
      y'       ∷ Matrix Double = asColumn y
      exponent ∷ Matrix Double = (x <> θ') * y'
      scaled   ∷ Matrix Double = y' * (1.0/(1.0+exp(exponent)))
      gradSum  ∷ Matrix Double = (tr x) <> scaled
      avgGrad  ∷ Vector Double = flatten $ scale (1.0/(dbl $ rows x)) gradSum
  in (- avgGrad)

-- | Obtains a vector in the same direction with L2-norm=1
normalize :: Vector Double -> Vector Double
normalize v
  | r > 1     =  scale (1/r) v
  | otherwise =  v
  where
    r = norm_2 v

-- | Convert a string into a double
readStr ∷ String → Double
readStr s = case (reads s) of
  [(d, _)] → d
  _ → 0.0

-- | Reads a CSV into a matrix
parseCSVtoMatrix ∷ FilePath → IO (Either ParseError (Matrix Double))
parseCSVtoMatrix file = do
  Right(csv) ← parseCSVFromFile file
  let csvList ∷ [[Double]] = map (map readStr) csv
      matrix ∷ Matrix Double = fromLists csvList
  return $ return matrix

-- | Performs gradient descent with a fixed learning rate
gradientDescent ∷ Int → Model → Matrix Double → Vector Double → Double → Model
gradientDescent 0 θ x y η = θ
gradientDescent n θ x y η = let θ' = θ - (scale η $ ngrad θ x y)
                            in trace ("training iter " ++ (show n) ++
                                      ", loss : " ++ (show $ loss θ x y))
                               gradientDescent (n-1) θ' x y η

-- | Makes a single prediction
predict ∷ Model → (Vector Double, Double) → Double
predict θ (x, y) = signum $ x <.> θ

isCorrect ∷ (Double, Double) → (Int, Int)
isCorrect (prediction, actual) | prediction == actual = (1, 0)
                               | otherwise = (0, 1)

-- | Converts a matrix to a model (flatten it)
toModel ∷ Matrix Double → Model
toModel = flatten

-- | Calculates the accuracy of a model
accuracy ∷ Matrix Double → Vector Double → Model → (Int, Int)
accuracy x y θ = let pairs ∷ [(Vector Double, Double)] = zip (map normalize $ toRows x) (toList y)
                     labels ∷ [Double] = map (predict θ) pairs
                     correct ∷ [(Int, Int)] = map isCorrect $ zip labels (toList y)
                 in foldl' (\a b → (fst a + fst b, snd a + snd b)) (0, 0) correct

-- | Ensures that labels are either 1 or -1
fixLabel ∷ Double → Double
fixLabel x | x == -1.0 = -1.0
           | x == 1.0 = 1.0
           | otherwise = trace ("Unexpected label: " ++ (show x)) x

-- Runs the test
runtest args = do
  putStrLn "loading data"
  Right(mat) ← parseCSVtoMatrix (head args)
  let dataCols ∷ [Vector Double] = toColumns mat
      x ∷ Matrix Double = fromColumns $ tail dataCols
      y ∷ Vector Double = head dataCols
      θ ∷ Vector Double = fromList $ replicate (cols x) 0.0
  putStrLn "done loading data; running training"
  -- toy parameters
  let θ' = gradientDescent 100 θ x y 0.1
  putStrLn "done running training; running accuracy"
  let (correct, incorrect) = accuracy x y θ'
  putStrLn $ "Accuracy: " ++
    (show $ (dbl correct) / (dbl $ correct + incorrect))


{- |  Test sgd on toy data
      Examples:
      wget https://people.eecs.berkeley.edu/~jnear/files/adult_train.csv
      wget https://people.eecs.berkeley.edu/~jnear/files/adult_test.csv
-}
main ∷ IO ()
main = do
  args ← getArgs
  runtest args
  putStrLn "done"
