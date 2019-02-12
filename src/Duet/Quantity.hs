module Duet.Quantity where

import UVMHS

import Duet.RNF

data Quantity a = Zero | Quantity a | Inf
  deriving (Eq,Ord,Show)

makePrisms ''Quantity

instance (HasPrism a b) ⇒ HasPrism (Quantity a) b where hasPrism = (hasPrism @ a @ b) ⊚ (quantityL @ a)

instance Zero (Quantity a) where zero = Zero
instance (Plus a) ⇒ Plus (Quantity a) where
  Zero + x = x
  x + Zero = x
  Inf + _ = Inf
  _ + Inf = Inf
  Quantity x + Quantity y = Quantity $ x + y
instance (Plus a) ⇒ Additive (Quantity a)

instance (One a) ⇒ One (Quantity a) where one = Quantity one
instance (Times a) ⇒ Times (Quantity a) where
  Zero × _ = Zero
  _ × Zero = Zero
  Inf × _ = Inf
  _ × Inf = Inf
  Quantity x × Quantity y = Quantity $ x × y
instance (Multiplicative a) ⇒ Multiplicative (Quantity a)

instance Null (Quantity a) where null = Zero
instance (Append a) ⇒ Append (Quantity a) where 
  Zero ⧺ x = x
  x ⧺ Zero = x
  Inf ⧺ _ = Inf
  _ ⧺ Inf = Inf
  Quantity x ⧺ Quantity y = Quantity $ x ⧺ y
instance Append a ⇒ Monoid (Quantity a)

instance (Unit a) ⇒ Unit (Quantity a) where unit = Quantity unit
instance (Cross a) ⇒ Cross (Quantity a) where
  Zero ⨳ _ = Zero
  _ ⨳ Zero = Zero
  Inf ⨳ _ = Inf
  _ ⨳ Inf = Inf
  Quantity x ⨳ Quantity y = Quantity $ x ⨳ y
instance (Prodoid a) ⇒ Prodoid (Quantity a)

instance Bot (Quantity a) where bot = Zero
instance (Join a) ⇒ Join (Quantity a) where
  Zero ⊔ y = y
  x ⊔ Zero = x
  Inf ⊔ _ = Inf
  _ ⊔ Inf = Inf
  Quantity x ⊔ Quantity y = Quantity $ x ⊔ y
instance (Join a) ⇒ JoinLattice (Quantity a)

instance (POrd a) ⇒ POrd (Quantity a) where
  Zero ⊑ _ = True
  Quantity x ⊑ Quantity y = x ⊑ y
  _ ⊑ Inf = True
  _ ⊑ _ = False

instance Top (Quantity a) where top = Inf
instance (Meet a) ⇒ Meet (Quantity a) where
  Zero ⊓ _ = Zero
  _ ⊓ Zero = Zero
  x ⊓ Inf = x
  Inf ⊓ y = y
  Quantity x ⊓ Quantity y = Quantity $ x ⊓ y
instance (Meet a) ⇒ MeetLattice (Quantity a)
instance (Join a,Meet a) ⇒ Lattice (Quantity a)

instance Functor Quantity where
  map f = \case
    Zero → Zero
    Quantity x → Quantity $ f x
    Inf → Inf

-- ⌉s′⌈ˢ ≡ truncate s s′
-- ⌉Σ⌈ˢ ≡ map (Sens ∘ truncate s ∘ unSens) Σ
truncate ∷ Quantity a → Quantity b → Quantity a
truncate _ Zero         = Zero
truncate p Inf          = p
truncate p (Quantity _) = p

class 
  (Functor p
  ,∀ a. Eq a ⇒ Eq (p a)
  ,∀ a. Additive a ⇒ Additive (p a)
  ,∀ a. Append a ⇒ Append (p a)
  ,∀ a. Join a ⇒ Join (p a)
  ) ⇒ Privacy p where
  edLoopBounds ∷ RNF → RNF → p RNF → p RNF
  loopBounds ∷ RNF → p RNF → p RNF
