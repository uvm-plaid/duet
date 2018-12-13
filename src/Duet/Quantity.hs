module Duet.Quantity where

import UVMHS

import Duet.RExp

data Quantity a = Zero | Quantity a | Inf
  deriving (Eq,Ord,Show)
makePrettySum ''Quantity

instance (Additive a) ⇒ Additive (Quantity a) where
  zero = Zero
  Zero + x = x
  x + Zero = x
  Inf + _ = Inf
  _ + Inf = Inf
  Quantity x + Quantity y = Quantity $ x + y
instance (Multiplicative a) ⇒ Multiplicative (Quantity a) where
  one = Quantity one
  Zero × _ = Zero
  _ × Zero = Zero
  Inf × _ = Inf
  _ × Inf = Inf
  Quantity x × Quantity y = Quantity $ x × y

instance Null (Quantity a) where null = Zero
instance (Append a) ⇒ Append (Quantity a) where 
  Zero ⧺ x = x
  x ⧺ Zero = x
  Inf ⧺ _ = Inf
  _ ⧺ Inf = Inf
  Quantity x ⧺ Quantity y = Quantity $ x ⧺ y
instance Append a ⇒ Monoid (Quantity a)

instance Bot (Quantity a) where bot = Zero
instance (Join a) ⇒ Join (Quantity a) where
  Zero ⊔ y = y
  x ⊔ Zero = x
  Inf ⊔ _ = Inf
  _ ⊔ Inf = Inf
  Quantity x ⊔ Quantity y = Quantity $ x ⊔ y
instance (Join a) ⇒ JoinLattice (Quantity a)

instance Functor Quantity where
  map f = \case
    Zero → Zero
    Quantity x → Quantity $ f x
    Inf → Inf

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
