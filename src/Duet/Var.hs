module Duet.Var where

import UVMHS

data 𝕏 = 𝕏 
  { 𝕩name ∷ 𝕊 
  , 𝕩Gen ∷ 𝑂 ℕ
  }
  deriving (Eq,Ord,Show)
makeLenses ''𝕏
makePrettySum ''𝕏

var ∷ 𝕊 → 𝕏
var x = 𝕏 x None
