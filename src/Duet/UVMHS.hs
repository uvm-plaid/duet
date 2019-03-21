module Duet.UVMHS 
  ( module UVMHS
  , module Duet.UVMHS
  ) where

import UVMHS

mapJoin ∷ (Ord k,Ord v₁,Ord v₂) ⇒ k ⇰ 𝑃 v₁ → k ⇰ 𝑃 v₂ → k ⇰ 𝑃 (v₁ ∧ v₂)
mapJoin = interWith $ \ vs₁ vs₂ → pow $ list vs₁ ⧆ list vs₂

class BFunctor t where
  bmap ∷ (a → b → c) → t a → t b → t c

zipWith :: (ToStream a t₁,ToStream b t₂) ⇒ (a → b → c) → t₁ → t₂ → 𝑆 c
zipWith f xs ys = map (\ (x :* y) → f x y) $ zip xs ys
