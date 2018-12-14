module Duet.AddToUVMHS where

import UVMHS hiding (log)
import qualified UVMHS

import qualified Data.Map.Strict as Map

infixl 5 ⨵

deleteView ∷ (Ord k) ⇒ k → k ⇰ v → 𝑂 (v ∧ (k ⇰ v))
deleteView k kvs
  | k ⋵ kvs = Some (kvs ⋕! k :* delete k kvs)
  | otherwise = None

without ∷ (Ord k) ⇒ 𝑃 k → k ⇰ v → k ⇰ v
without ks kvs = 𝐷 $ Map.withoutKeys (un𝐷 kvs) $ un𝑃 ks

(⨵) ∷ (Functor f,Multiplicative a) ⇒ a → f a → f a
x ⨵ xs = map (x ×) xs

class Root a where root ∷ a → a
class Log a where log ∷ a → a

instance Root 𝔻 where root = sqrt
instance Log 𝔻 where log = UVMHS.log

class HasPrism a b where hasPrism ∷ a ⌲ b
class HasLens a b where hasLens ∷ a ⟢ b

instance HasPrism a a where hasPrism = refl
instance HasLens a a where hasLens = refl

ι ∷ (HasPrism a b) ⇒ b → a
ι = construct hasPrism

ιview ∷ ∀ b a. (HasPrism a b) ⇒ a → 𝑂 b
ιview = view hasPrism

π ∷ (HasLens a b) ⇒ a → b
π = access hasLens
