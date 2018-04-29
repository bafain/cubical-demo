module Cubical.Equivalence.HAE where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') (f : A → B) where
  -- Definition 4.2.1
  record ishae : Set (ℓ-max ℓ ℓ') where
    field
      g : B → A
      η : Homotopy (g ∘ f) (idFun A)
      ε : Homotopy (f ∘ g) (idFun B)
      τ : ∀ (x : A) → cong f (η x) ≡ ε (f x)
