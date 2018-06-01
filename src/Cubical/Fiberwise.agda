{-# OPTIONS --cubical #-}
module Cubical.Fiberwise where

open import Cubical.PathPrelude
open import Cubical.FromStdLib
open import Cubical.Equivalence.Properties
open import Cubical.NType
open import Cubical.NType.Properties
open import Cubical.Lemmas
open import Cubical.GradLemma
open import Cubical.Sigma

module _ {a p q} {A : Set a} (P : A → Set p) (Q : A → Set q)
         (f : ∀ x → P x → Q x)
         where
  total : (Σ A P) → (Σ A Q)
  total = (\ p → p .fst , f (p .fst) (p .snd))

  module _ where
    private
      h : ∀ {xv} → fiber total (xv) → fiber (f (xv .fst)) (xv .snd)
      h {xv} (p , eq) = pathJ (\ xv eq → fiber (f (xv .fst)) (xv .snd)) ((p .snd) , refl) xv (sym eq)
      g : ∀ {xv} → fiber (f (xv .fst)) (xv .snd) → fiber total xv
      g {xv} (p , eq) = ((xv .fst) , p) , (\ i → _ , eq i)
      h-g : ∀ {xv} y → h {xv} (g {xv} y) ≡ y
      h-g {x , v} (p , eq) = pathJ (λ _ eq₁ → h (g (p , sym eq₁)) ≡ (p , sym eq₁)) (pathJprop (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) ((p , refl))) v (sym eq)
      g-h : ∀ {xv} y → g {xv} (h {xv} y) ≡ y
      g-h {xv} ((a , p) , eq) = pathJ (λ _ eq₁ → g (h ((a , p) , sym eq₁)) ≡ ((a , p) , sym eq₁)) ((cong g (pathJprop (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) (p , refl)))
                                      )
                                  (xv .fst , xv .snd) (sym eq)

    -- Thm 4.7.6
    fibers-total : ∀ {xv} → fiber total (xv) ≃ fiber (f (xv .fst)) (xv .snd)
    fibers-total {xv} = h , gradLemma h g h-g g-h

    fibers-f : ∀ {xv} → fiber (f (xv .fst)) (xv .snd) ≃ fiber total (xv)
    fibers-f {xv} = g , gradLemma g h g-h h-g

  -- half of Thm 4.7.7
  fiberEquiv : ([tf] : isEquiv (Σ A P) (Σ A Q) total)
               → ∀ x → isEquiv (P x) (Q x) (f x)
  fiberEquiv [tf] x y = equivPreservesNType {n = ⟨-2⟩} fibers-total ([tf] (x , y))

  totalEquiv : (∀ x → isEquiv (P x) (Q x) (f x)) → isEquiv (Σ A P) (Σ A Q) total
  totalEquiv equivf xv = equivPreservesNType {n = ⟨-2⟩} fibers-f (equivf (xv .fst) (xv .snd))

module ContrToUniv {ℓ : Level} {U : Set ℓ} {ℓr} (_~_ : U → U → Set ℓr)
       (idTo~ : ∀ {A B} → A ≡ B → A ~ B )
       (c : ∀ A → isContr (Σ U \ X → A ~ X))
       where

  lemma : ∀ {A B} → isEquiv _ _ (idTo~ {A} {B})
  lemma {A} {B} = fiberEquiv (λ z → A ≡ z) (λ z → A ~ z) (\ B → idTo~ {A} {B})
                  (λ y → sigPresContr ((_ , refl) , (\ z → snd contrSingl z))
                                      \ a → hasLevelPath ⟨-2⟩ (HasLevel+1 ⟨-2⟩ (c A)) _ _)
                  B

module _ {ℓa ℓb : _} {A : Set ℓa} {B : A → Set ℓb} where
  lem4-8-1 : ∀ a → fiber (fst {B = B}) a ≃ B a
  lem4-8-1 a =   fiber fst a
               ≃⟨ inverseEquiv Σ-assoc ⟩
                 Σ A (λ x → Σ (B x) λ _ → a ≡ x)
               ≃⟨ _ , totalEquiv _ _ _ (λ x → ×-comm .snd) ⟩
                 Σ A (λ x → Σ (a ≡ x) λ _ → B x)
               ≃⟨ Σ-assoc ⟩
                 Σ (Σ A λ x → a ≡ x) (λ xp → B (xp .fst))
               ≃⟨ lem3-11-9-ii _ _ contrSingl ⟩
                 B a □

module _ {ℓ : _} {A : Set ℓ} {B : Set ℓ} where
  lem4-8-2 : ∀ (f : A → B) → A ≃ Σ B (fiber f)
  lem4-8-2 f =   A
               ≃⟨ inverseEquiv (lem3-11-9-i A (singl ∘ f) (λ _ → contrSingl)) ⟩
                 Σ A (λ a → singl (f a))
               ≃⟨ Σ-swap ⟩
                 Σ B (λ b → Σ A (λ a → f a ≡ b ))
               ≃⟨ _ , totalEquiv _ _ _ (λ b → totalEquiv _ _ _ λ a → sym-equiv) ⟩
                 (Σ B λ b → fiber f b) □
