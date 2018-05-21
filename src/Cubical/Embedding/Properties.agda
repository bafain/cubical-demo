module Cubical.Embedding.Properties {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) where

open import Cubical.FromStdLib
open import Cubical.PathPrelude renaming (isEmbedding to isFullyFaithful)

open import Cubical.Equivalence.Properties
open import Cubical.Fiberwise
open import Cubical.Lemmas
open import Cubical.NType
open import Cubical.NType.Properties

private
  isEmbedding : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ-max ℓ ℓ')
  isEmbedding f = ∀ y → isProp (fiber f y)

module _ (embedf : isEmbedding f) where
  module _ {ℓ''} {C : Set ℓ''} where
    private
     fiber′ : (k : C → B) → Set (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
     fiber′ k = Σ (C → A) (λ g → Homotopy k (f ∘ g))

    embed₁′ : ∀ k → isProp (fiber′ k)
    embed₁′ k = equivPreservesNType {n = S ⟨-2⟩} AC∞ (piPresNType (S ⟨-2⟩) (embedf ∘ k))

    embed₁ : isEmbedding (f ∘_)
    embed₁ k = equivPreservesNType {n = S ⟨-2⟩} (inverseEquiv (_ , totalEquiv _ _ _ λ g → snd FUNEXT)) (embed₁′ k)

    left-cancel₁ : {g h : C → A} → Homotopy (f ∘ g) (f ∘ h) → Homotopy g h
    left-cancel₁ {g} {h} fg≡fh = λ c → happly (cong fst (embed₁′ (f ∘ g) (g , λ _ → refl) (h , fg≡fh))) c

  module _ {x y} (fx≡fy : f x ≡ f y) where
    left-cancel₀ : x ≡ y
    left-cancel₀ = left-cancel₁ {ℓ-zero} (λ _ → fx≡fy) tt
