module Duet.Pretty where

import UVMHS

import Duet.Syntax
import Duet.Quantity

instance (Pretty e) ⇒ Pretty (Quantity e) where
  pretty Zero = ppKeyPun "⊥"
  pretty (Quantity e) = pretty e
  pretty Inf = ppKeyPun "⊤"

instance Pretty Kind where
  pretty = \case
    ℕK → ppKeyPun "ℕ"
    ℝK → ppKeyPun "ℝ⁺"

instance Pretty Norm where
  pretty = \case
    L1 → ppKeyPun "L1"
    L2 → ppKeyPun "L2"
    LInf → ppKeyPun "L∞"

instance Pretty Clip where
  pretty = \case
    NormClip ℓ → pretty ℓ
    UClip → ppKeyPun "U"

deriving instance (Pretty r) ⇒ Pretty (Sens r)

instance (Pretty r) ⇒ Pretty (Pr p r) where
  pretty = \case
    EpsPriv r → pretty r
    EDPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂
    RenyiPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂
    ZCPriv r  → pretty r
    TCPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂

deriving instance (Pretty r) ⇒ Pretty (Priv p r)

instance (Pretty r) ⇒ Pretty (Type r) where
  pretty = \case
    ℕˢT r → concat[ppKeyPun "ℕ",ppPun "[",pretty r,ppPun "]"]
    ℝˢT r → concat[ppKeyPun "ℝ⁺",ppPun "[",pretty r,ppPun "]"]
    ℕT → ppKeyPun "ℕ"
    ℝT → ppKeyPun "ℝ"
    𝔻T → ppKeyPun "𝔻 "
    𝕀T r → concat[ppKeyPun "𝕀",ppPun "[",pretty r,ppPun "]"]
    𝔻𝔽T as → ppAtLevel 2 $ ppSeparated $ list
             [ ppKeyPun "𝔻𝔽"
             , ppPun "["
             , ppAlign $ ppSeparated $ list $ inbetween (ppPun ",") $ mapOn as $ \ (n :* t) → 
                 ppBotLevel $ concat [ppAlign $ ppPun n,ppPun ":",ppAlign $ pretty t]
             , ppPun "]"
             ]
    𝕄T ℓ c ηₘ ηₙ τ → ppAtLevel 10 $ ppSeparated $ list
      [ concat
        [ ppKeyPun "𝕄 "
        , ppPun "["
        , ppAlign $ pretty ℓ
        , ppSpace 1
        , ppAlign $ pretty c
        , ppPun "|"
        , ppAlign $ pretty ηₘ
        , ppPun ","
        , ppAlign $ pretty ηₙ
        , ppPun "]"
        ]
      , pretty τ
      ]
    τ₁ :+: τ₂ → ppAtLevel 5 $ ppSeparated $ list
      [ pretty τ₁
      , ppPun "+"
      , ppBump $ pretty τ₂
      ]
    τ₁ :×: τ₂ → ppAtLevel 6 $ ppSeparated $ list
      [ pretty τ₁
      , ppPun "×"
      , ppBump $ pretty τ₂
      ]
    τ₁ :&: τ₂ → ppAtLevel 6 $ ppSeparated $ list
      [ pretty τ₁
      , ppPun "&"
      , ppBump $ pretty τ₂
      ]
    τ₁ :⊸: (ς :* τ₂) → ppAtLevel 2 $ ppSeparated $ list
      [ ppBump $ pretty τ₁
      , ppBotLevel $ concat [ppPun "⊸[",ppAlign $ pretty ς,ppPun "]"]
      , pretty τ₂
      ]
    (ακs :* PArgs τps) :⊸⋆: τ → ppAtLevel 2 $ ppSeparated $ list
      [ concat
        [ ppPun "∀"
        , ppSpace 1
        , ppAlign $ ppSeparated $ list $ inbetween (ppPun ",") $ mapOn ακs $ \ (α :* κ) → 
           ppBotLevel $ concat [ppAlign $ pretty α,ppPun ":",ppAlign $ pretty κ]
        ]
      , ppSeparated 
          $ list
          $ mapFirst (\ s → ppSeparated $ list [ppPun ".",s])
          $ mapAfterFirst (\ s → ppSeparated $ list [ppPun ",",s]) 
          $ mapOn τps $ \ (τ' :* p) →
              ppBotLevel $ concat [ppAlign $ pretty τ',ppPun "@",ppAlign $ pretty p]
      , concat [ppPun "⇒",ppSpace 1,ppAlign $ pretty τ]
      ]
