{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables,Strict,StrictData #-}

module Duet.Interpreter where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF
import Duet.Quantity

-- libraries
-- import Prelude hiding ((<>))
-- import Data.Map (Map)
-- import qualified Data.Map as Map
-- import Data.List
-- import Data.Ord
-- import Numeric.LinearAlgebra hiding (LU, normalize) -- to use norm from Syntax.hs
-- import Text.CSV
-- import Text.Parsec.Error
-- import System.Environment
-- import Debug.Trace
-- import Numeric.Natural
-- import Control.Exception
-- import Data.Random.Normal

-- our code
-- import CustomPrelude hiding (iter, (<>))
-- import Syntax
import Gradient hiding (main, runtest)
import MinibatchGradient hiding (main, runtest, mbSGD)

type Env = Map Var Val

-- | Returns maximum element
maxElem ::  Ord b => [(a, b)] -> a
maxElem = fst . maximumBy (comparing snd)

-- | Returns minimum element
minElem ::  Ord b => [(a, b)] -> a
minElem = fst . minimumBy (comparing snd)

-- | Defining Val algebraic data type
data Val =
  NatV Natural
  | RealV Double
  | PairV Val Val
  | SFunV Var SExp Env
  | PFunV [Var] PExp Env
  | MatrixV (Matrix Double)
  deriving (Eq, Show)

-- | Converts and integer to a double
intDouble ∷ Int → Double
intDouble = fromIntegral

-- | Converts a natural number to a double
mkDouble ∷ Natural → Double
mkDouble = fromIntegral

-- | Evaluates an expression from the sensitivity language
seval ∷ Env → SExp → Val

-- literals
seval _ (SNatE n)        = NatV n
seval _ (SRealE n)       = RealV n
seval _ (SSingRealE n)   = RealV n
seval _ (SSingNatE n)    = NatV n
seval env (SRealNatE e) =
  case (seval env e) of
    (NatV n) -> RealV $ mkDouble n

-- variables
seval env (SVarE x) | Map.member x env  = env Map.! x
                    | otherwise         = error $ "Unknown variable: " ++ (chars x) ++ " in environment with bound vars " ++ (chars $ sho $ keys env)

-- arithmetic
seval env (SPlusE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ + v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ + v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

seval env (SMinusE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ - v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ - v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

seval env (SMultE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (MatrixV v₁, MatrixV v₂) → MatrixV (v₁ <> v₂)
    (RealV v₁, MatrixV v₂) → MatrixV (scale v₁ v₂)
    (RealV v₁, RealV v₂) → RealV (v₁ * v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

seval env (SDivE e₁ e₂) =
  case (seval env e₁, seval env e₂) of
    (RealV v₁, RealV v₂) → RealV (v₁ / v₂)
    (a, b) → error $ "No pattern for " ++ (show (a, b))

-- matrix operations
seval env (SMRowsE e) =
  case (seval env e) of (MatrixV v) →
                         NatV $ nat $ rows v

seval env (SMColsE e) =
  case (seval env e) of (MatrixV v) →
                         NatV $ nat $ cols v

seval env (SMIdE e) =
  case seval env e of
    (NatV d) →
      let posMat ∷ Matrix Double = ident $ int d
          negMat ∷ Matrix Double = scale (-1.0) posMat
      in MatrixV (posMat === negMat)

seval env (SMTrE e) =
  case seval env e of (MatrixV m) → MatrixV $ tr m

-- clip operation for only L2 norm
seval env (SClipE norm e) =
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
        let θ'  ∷ Vector Double = flatten θ
            ys' ∷ Vector Double = flatten ys
        in MatrixV $ asRow $ ngrad θ' xs ys'
      else
        error $ "Incorrect matrix dimensions for gradient: " ++ (show (rows θ, rows ys))
    (a, b, c) → error $ "No pattern for " ++ (show (a, b, c))

-- create matrix
seval env (SMCreateE l e₁ e₂ i j e₃) =
  case (seval env e₁, seval env e₂) of
    (NatV v₁, NatV v₂) →
      MatrixV $ (><) (int v₁) (int v₂) $ replicate (int $ v₁ * v₂) 0.0

-- functions and application
seval env (SPFunE _ args body) =
  PFunV (map fst args) body env

seval env (SSFunE x _ body) =
  SFunV x body env

seval env (SAppE e₁ e₂) =
  case seval env e₁ of
    (SFunV x body env') →
      let env'' = (Map.insert x (seval env e₂) env')
      in seval env'' body

-- error
seval env e = error $ "Unknown expression: " ++ (show e)

-- | Evaluates an expression from the privacy language
peval ∷ Env → PExp → IO Val

-- bind and application
peval env (PBindE x e₁ e₂) = do
  v₁ ← peval env e₁
  v₂ ← peval (Map.insert x v₁ env) e₂
  return v₂

peval env (PAppE _ f vars) =
  case seval env f of
    (PFunV args body env') →
      let vs    ∷ [Val] = map ((Map.!) env) vars
          env'' ∷ Env   = foldr (\(var, val) → Map.insert var val) env' (zip args vs)
      in peval env'' body

-- sample on two matrices and compute on sample
peval env (PSampleE size xs ys x y e) =
  case (seval env size, env Map.! xs, env Map.! ys) of
    (NatV n, MatrixV v1, MatrixV v2) ->
      sampleHelper n v1 v2 x y e env

-- gaussian mechanism for real numbers
peval env (PGaussE r ε δ vs e) =
  case (seval env r, seval env ε, seval env  δ, seval env e) of
    (RealV r', RealV ε', RealV δ', RealV v) → do
      r ← gaussianNoise 0 (r' * (sqrt $ 2 * (log $ 1.25/δ')) / ε')
      return $ RealV $ v + r
    (a, b, c, d) → error $ "No pattern for: " ++ (show (a,b,c,d))

-- gaussian mechanism for matrices
peval env (PMGaussE r ε δ vs e) =
  case (seval env r, seval env ε, seval env  δ, seval env e) of
    (RealV r', RealV ε', RealV δ', MatrixV mat) → do
      let σ = (r' * (sqrt $ 2 * (log $ 1.25/δ')) / ε')
      mat' ← mapM (\row → mapM (\val → gaussianNoise val σ) row) $ toLists mat
      return $ MatrixV $ fromLists mat'
    (a, b, c, d) → error $ "No pattern for: " ++ (show (a,b,c,d))

-- evaluate finite iteration
peval env (PLoopE δ' k init xs x₁ x₂ e) =
  case (seval env k, seval env init) of
    (NatV k', initV) →
      iter k' initV x₁ x₂ 0 e env

-- evaluate sensitivity expression and return in the context of the privacy language
peval env (PReturnE e) =
  return $ seval env e

-- exponential mechanism
peval env (PExpE s ε xs x body) =
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
iter ∷ Natural → Val → Var → Var → Int → PExp → Env → IO Val
iter 0 v _ _ _ _ _ = return v
iter k v t x kp body env = do
  newVal ← peval (Map.insert x v $ Map.insert t (NatV $ nat kp) env) body
  iter (k - 1) newVal t x (kp+1) body env

-- | Empty environment
emptyEnv ∷ Env
emptyEnv = Map.empty

-- | Read in a dataset and return xs (features) and ys (labels)
readDataSet ∷ String → IO (Matrix Double, Vector Double)
readDataSet fileName = do
    Right(mat) ← parseCSVtoMatrix fileName
    let dataCols ∷ [Vector Double] = toColumns mat
        xs ∷ Matrix Double = fromColumns $ tail dataCols
        ys ∷ Vector Double = head dataCols
    return $ (xs, ys)

-- | Place a dataset into the environment
insertDataSet ∷ Env → (Var, Var) → (Matrix Double, Vector Double) → Env
insertDataSet env (x, y) (xs, ys) =
  Map.insert x (MatrixV xs) $ Map.insert y (MatrixV $ asRow ys) env

-- | Samples a normal distribution and returns a single value
gaussianNoise ∷ Double → Double → IO Double
gaussianNoise c v = normalIO'(c, v)

-- | Helper function for PSampleE
sampleHelper :: Natural -> Matrix Double -> Matrix  Double -> Var -> Var -> PExp -> Env -> IO Val
sampleHelper n xs ys x y e env = do
  batch <- minibatch (int n) xs (flatten ys)
  peval (insertDataSet env (x, y) ((fst batch), (snd batch))) e
