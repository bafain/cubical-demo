{-# OPTIONS --cubical #-}
module Cubical.PushOut.Properties where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.GradLemma

open import Cubical.PushOut

-- Proposition 1.8.4 in Brunerie
module _ {ℓ} {A B : Set ℓ} (f : A → B) where
  unit : PushOut (idFun A) f ≃ B
  unit = h , gradLemma h g (λ _ → refl) (primPushOutElim _ (λ a → sym (push a)) (λ _ → refl) (λ c i j → push c (i ∨ ~ j)))
    where
      g : B → PushOut (idFun A) f
      g = inr

      h : PushOut (idFun A) f → B
      h = primPushOutElim _ f (idFun B) (λ _ → refl)

-- Proposition 1.8.5 in Brunerie
module _ {ℓ} {A B C X : Set ℓ} (f : C → A) (g : C → B) where
  dist : PushOut (f ×₁ idFun X) (g ×₁ idFun X) ≃ (PushOut f g × X)
  dist = h₂ , gradLemma h₂ h₁ h₂h₁≡id h₁h₂≡id
    where
      h₁ : PushOut f g × X → PushOut (f ×₁ idFun X) (g ×₁ idFun X)
      h₁ (y , x) = primPushOutElim _ (λ a → inl (a , x)) (λ b → inr (b , x)) (λ c → push (c , x)) y

      h₂ : PushOut (f ×₁ idFun X) (g ×₁ idFun X) → PushOut f g × X
      h₂ = primPushOutElim _ (λ { (a , x) → inl a , x }) (λ { (b , x) → inr b , x }) λ { (c , x) → cong (_, x) (push c) }

      h₂h₁≡id : ∀ px → h₂ (h₁ px) ≡ px
      h₂h₁≡id (y , x) = primPushOutElim (λ y → h₂ (h₁ (y , x)) ≡ (y , x)) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) y

      h₁h₂≡id : ∀ p → h₁ (h₂ p) ≡ p
      h₁h₂≡id = primPushOutElim _ (λ _ → refl) (λ _ → refl) λ _ _ → refl
