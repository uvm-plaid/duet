module Duet.UVMHS 
  ( module UVMHS
  , module Duet.UVMHS
  ) where

import UVMHS

instance (Times a) ⇒ Times (Vᴍ m n a) where (×) = xmap2 (×)

(✖) ∷ (Additive a,Times a) ⇒ Vᴍ m n a → Vᴍ n o a → Vᴍ m o a
(✖) = xproduct


xbmapM' ∷ (Monad m) ⇒ (a → m b) → Vᴍ n o a → m (Bᴍ n o b)
xbmapM' f xs@(Vᴍ _ _ _) = do
  xs' ← mapM (mapM f) $ xlist2' xs
  return $ xb𝐿 xs' $ \ (Bᴍ _ _ xs'') → Bᴍ (xrows xs) (xcols xs) xs''

xlist2' ∷ Vᴍ m n a → 𝐿 (𝐿 a)
xlist2' = list ∘ map list ∘ xiter2'

xiter2' ∷ Vᴍ m n a → 𝐼 (𝐼 a)
xiter2' = map iter ∘ iter ∘ xsplit

