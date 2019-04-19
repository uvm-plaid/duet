module Duet.UVMHS
  ( module UVMHS
  , module Duet.UVMHS
  ) where

import UVMHS

import qualified Prelude as HS
import qualified GHC.Stats  as HS
import qualified System.Mem as HS
import qualified Data.Time.Clock as Time

infixl 3 ⨺,⨹

type Time = Time.UTCTime
type TimeD = Time.NominalDiffTime

secondsTimeD ∷ TimeD → 𝔻
secondsTimeD = HS.realToFrac

instance Zero TimeD where {zero = HS.fromIntegral 0}
instance Plus TimeD where {(+) = (HS.+)}
instance Additive TimeD
instance One TimeD where {one = HS.fromIntegral 1}
instance Times TimeD where {(×) = (HS.*)}
instance Multiplicative TimeD

(⨺) ∷ Time → Time → TimeD
(⨺) = Time.diffUTCTime

(⨹) ∷ Time → TimeD → Time
(⨹) = flip Time.addUTCTime

now ∷ IO Time
now = Time.getCurrentTime

gc ∷ IO ()
gc = HS.performGC

time ∷ (a → b) → a → IO (b ∧ TimeD)
time f x = do
  gc
  t₁ ← now
  let y = f x
  t₂ ← now
  return $ (y :* t₂ ⨺ t₁)

timeIO ∷ IO a → IO (a ∧ TimeD)
timeIO xM = do
  gc
  t₁ ← now
  x ← xM
  t₂ ← now
  return $ (x :* t₂ ⨺ t₁)

profile ∷ (a → b) → a → IO (TimeD,𝔻)
profile f x = do
  gc
  s₁ ← HS.getRTSStats
  let (n₁,u₁) = (HS.major_gcs s₁,HS.cumulative_live_bytes s₁)
  t₁ ← now
  let _ = f x
  t₂ ← now
  s₂ ← HS.getRTSStats
  let (n₂,u₂) = (HS.major_gcs s₂,HS.cumulative_live_bytes s₂)
  return (t₂ ⨺ t₁,dbl (HS.fromIntegral u₂ - HS.fromIntegral u₁ ∷ ℕ) / dbl (HS.fromIntegral n₂ - HS.fromIntegral n₁ ∷ ℕ))

xcolsplit ∷ Vᴍ m n a → Vᴍ 1 n (Vᴍ m 1 a)
xcolsplit xys@(Vᴍ _ _ _) = matrix (s𝕟32 @ 1) (xcols xys) $ \ _ j → matrix (rowsVᴍ xys) (s𝕟32 @ 1) $ \ i _ → indexVᴍ i j xys
