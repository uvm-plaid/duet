module Duet.AddToUVMHS where

import UVMHS

import qualified Data.Map.Strict as Map

deleteView ∷ (Ord k) ⇒ k → k ⇰ v → 𝑂 (v ∧ (k ⇰ v))
deleteView k kvs
  | k ⋵ kvs = Some (kvs ⋕! k :* delete k kvs)
  | otherwise = None

without ∷ (Ord k) ⇒ 𝑃 k → k ⇰ v → k ⇰ v
without ks kvs = 𝐷 $ Map.withoutKeys (un𝐷 kvs) $ un𝑃 ks
