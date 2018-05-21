module Cubical.Equivalence.Properties where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.GradLemma

-- Lemma 2.4.12
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (A≃B : A ≃ B) where
  private
    f : A → B
    f = A≃B .fst

    f⁻¹ : B → A
    f⁻¹ = inverse A≃B

    ff⁻¹ : ∀ b → f (f⁻¹ b) ≡ b
    ff⁻¹ = λ b → sym (A≃B .snd b .fst .snd)

    f⁻¹f : ∀ a → f⁻¹ (f a) ≡ a
    f⁻¹f = λ a → cong fst (A≃B .snd (f a) .snd (a , refl))

  -- (ii)
  inverseEquiv : B ≃ A
  inverseEquiv = inverse A≃B , gradLemma f⁻¹ f f⁻¹f ff⁻¹

  module _ {ℓ''} {C : Set ℓ''} (B≃C : B ≃ C) where
    private
      g : B → C
      g = B≃C .fst

      g⁻¹ : C → B
      g⁻¹ = inverse B≃C

      gg⁻¹ : ∀ c → g (g⁻¹ c) ≡ c
      gg⁻¹ = λ c → sym (B≃C .snd c .fst .snd)

      g⁻¹g : ∀ b → g⁻¹ (g b) ≡ b
      g⁻¹g = λ b → cong fst (B≃C .snd (g b) .snd (b , refl))

      h : A → C
      h = g ∘ f

      h⁻¹ : C → A
      h⁻¹ = f⁻¹ ∘ g⁻¹

      hh⁻¹ : ∀ c → h (h⁻¹ c) ≡ c
      hh⁻¹ c = cong g (ff⁻¹ (g⁻¹ c)) ◾ gg⁻¹ c

      h⁻¹h : ∀ a → h⁻¹ (h a) ≡ a
      h⁻¹h a = cong f⁻¹ (g⁻¹g (f a)) ◾ f⁻¹f a

    -- (iii)
    compEquiv : A ≃ C
    compEquiv = h , gradLemma (g ∘ f) h⁻¹ hh⁻¹ h⁻¹h

infix  3 _≃-qed _□
infixr 2 _≃⟨⟩_ _≃⟨_⟩_

_≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Set ℓ) {B : Set ℓ'} → A ≃ B → A ≃ B
_ ≃⟨⟩ A≃B = A≃B

_≃⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) {B : Set ℓ'} {C : Set ℓ''} → A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ A≃B ⟩ B≃C = compEquiv A≃B B≃C

_≃-qed _□ : ∀ {ℓ} (A : Set ℓ) → A ≃ A
_ ≃-qed  = idEquiv
_□ = _≃-qed
