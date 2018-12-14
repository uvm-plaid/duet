module Duet.Var where

import UVMHS

data 𝕏 = 𝕏 
  { 𝕩name ∷ 𝕊 
  , 𝕩Gen ∷ 𝑂 ℕ
  }
  deriving (Eq,Ord,Show)
makeLenses ''𝕏

instance Pretty 𝕏 where
  pretty (𝕏 x None) = ppText x
  pretty (𝕏 x (Some n)) = concat [pretty x,ppText "@",pretty n]

var ∷ 𝕊 → 𝕏
var x = 𝕏 x None
