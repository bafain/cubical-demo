{-# OPTIONS --cubical #-}
module Cubical.PushOut.Properties where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Properties
open import Cubical.Fiberwise
open import Cubical.GradLemma
open import Cubical.Lemmas
open import Cubical.NType.Properties
open import Cubical.PushOut as PO

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

module _ {ℓ} {A B C P P' : Set ℓ} (f : C → A) (g : C → B) (P≃P' : P ≃ P') where
  open PO.Cocone f g

  private
    p : P → P'
    p = P≃P' .fst

    p⁻¹ : P' → P
    p⁻¹ = inverse P≃P'

    to : P -cocone → P' -cocone
    to (cocone i j h) = cocone (p ∘ i) (p ∘ j) (left-whisker p h)

    from : P' -cocone → P -cocone
    from (cocone i j h) = cocone (p⁻¹ ∘ i) (p⁻¹ ∘ j) (left-whisker p⁻¹ h)

    tofrom∼id : ∀ c → to (from c) ≡ c
    tofrom∼id (cocone i j h) r = cocone (λ a   → inverse-section (P≃P' .snd) (i a)   r)
                                        (λ b   → inverse-section (P≃P' .snd) (j b)   r)
                                        (λ c s → inverse-section (P≃P' .snd) (h c s) r)

    fromto∼id : ∀ c → from (to c) ≡ c
    fromto∼id (cocone i j h) r = cocone (λ a   → inverse-retraction (P≃P' .snd) (i a)   r)
                                        (λ b   → inverse-retraction (P≃P' .snd) (j b)   r)
                                        (λ c s → inverse-retraction (P≃P' .snd) (h c s) r)

  cocone-preserves-≃₁ : P -cocone ≃ P' -cocone
  cocone-preserves-≃₁ = to , gradLemma _ from tofrom∼id fromto∼id

module _ {ℓ} {A B C C' P : Set ℓ} {f : C → A} {g : C → B} (C'≃C : C' ≃ C) (let open PO.Cocone) (c : _-cocone f g P) where
  private
    m   = C'≃C .fst
    m⁻¹ = inverse C'≃C
    open _-cocone c using (i; j; h)

  module _ where
    cocone-preserves-≃₂ : ∀ E → _-cocone f g E ≃ _-cocone (f ∘ m) (g ∘ m) E
    cocone-preserves-≃₂ E =   _-cocone f g E
                            ≃⟨ cocone-Σ-equiv f g E ⟩
                              _
                            ≃⟨ _ , totalEquiv _ _ _ (λ i → totalEquiv _ _ _ (λ j → pre-equiv-d m (C'≃C .snd))) ⟩
                              _
                            ≃⟨ inverseEquiv (cocone-Σ-equiv (f ∘ m) (g ∘ m) E) ⟩
                             _-cocone (f ∘ m) (g ∘ m) E □

  private
    module _ where
      c' : _-cocone (f ∘ m) (g ∘ m) P
      c' = cocone i j (right-whisker m h)

    open PO hiding (P)

  isPushOut-preserves-≃ : isPushOut c ≃ isPushOut c'
  isPushOut-preserves-≃ = _ , lem492-d λ E → compEquiv-r _ _ (cocone-preserves-≃₂ E .snd)

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
