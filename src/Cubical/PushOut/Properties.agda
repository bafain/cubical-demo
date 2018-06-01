{-# OPTIONS --cubical #-}
module Cubical.PushOut.Properties where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Properties
open import Cubical.GradLemma
open import Cubical.NType.Properties
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

module _ {ℓ} {A B C P : Set ℓ} {f : C → A} {g : C → B} {i : A → P} {j : B → P} {H : Homotopy (i ∘ f) (j ∘ g)} where
  open PO.Cocone f g
  open PO.Canonical f g

  private
    c = cocone i j H

  module _ where
    private
      [i,j] : PushOut f g → P
      [i,j] = inverse (_ , lem682 P) c

      h : ∀ {P'} → Homotopy (toCocone 𝒫 {P'} ∘ (_∘ [i,j])) (toCocone c {P'})
      h = hid

      to : isPushOut c → isEquiv _ _ [i,j]
      to poc = inverse (pre-equiv [i,j]) (λ X → inverse (thm471 (_∘ [i,j]) (toCocone 𝒫) (inverse (∼-preserves-isEquiv h) (poc X))) (lem682 X))

      from : isEquiv _ _ [i,j] → isPushOut c
      from equiv[ij] E = ∼-preserves-isEquiv h .fst (compEquiv (_ , pre-equiv [i,j] .fst equiv[ij] _) (_ , lem682 E) .snd)

    unique : isPushOut c ≃ isEquiv _ _ [i,j]
    unique = _ , lem3-3-3 (propIsPushOut c) (propIsEquiv _) to from
