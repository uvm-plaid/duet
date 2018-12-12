module Duet.Quantity where

import UVMHS

data Quantity a = Zero | Quantity a | Inf
  deriving (Eq,Ord,Show)
makePrettySum ''Quantity

instance Null (Quantity a) where null = Zero
instance (Append a) ⇒ Append (Quantity a) where
  Zero ⧺ x = x
  x ⧺ Zero = x
  Inf ⧺ _ = Inf
  _ ⧺ Inf = Inf
  Quantity x ⧺ Quantity y = Quantity $ x ⧺ y

instance Append a ⇒ Monoid (Quantity a)

instance Functor Quantity where
  map f = \case
    Zero → Zero
    Quantity x → Quantity $ f x
    Inf → Inf

truncate ∷ Quantity a → Quantity b → Quantity b
truncate Zero         _ = Zero
truncate Inf          p = p
truncate (Quantity _) p = p

class (∀ a. Append a ⇒ Append (p a)) ⇒ Privacy p
