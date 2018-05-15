module Cubical.Equivalence.Properties where

open import Cubical.PathPrelude
open import Cubical.Fiberwise
open import Cubical.NType.Properties

module _ {ℓa ℓb : _} {A : Set ℓa} {B : Set ℓb} (f : A → B) (equivf : isEquiv _ _ f) where
  thm2-11-1 : isEmbedding f
  thm2-11-1 = λ a → fiberEquiv _ _ (λ a' → cong {x = a} {y = a'} f) (contrEquiv contrSingl contrFiberf)
    where
      contrFiberf : ∀ {b} → isContr (fiber f b)
      contrFiberf {b} = equivf b
