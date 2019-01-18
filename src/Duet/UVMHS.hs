module Duet.UVMHS 
  ( module UVMHS
  , module Duet.UVMHS
  ) where

import UVMHS

mapJoin ∷ (Ord k,Ord v₁,Ord v₂) ⇒ k ⇰ 𝑃 v₁ → k ⇰ 𝑃 v₂ → k ⇰ 𝑃 (v₁ ∧ v₂)
mapJoin = interWith $ \ vs₁ vs₂ → pow $ list vs₁ ⧆ list vs₂
