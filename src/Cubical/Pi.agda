{-# OPTIONS --cubical #-}
module Cubical.Pi where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Properties
open import Cubical.Fiberwise
open import Cubical.Lemmas
open import Cubical.NType
open import Cubical.NType.Properties
open import Cubical.Sigma

-- Exercise 2.17 (iii-Π-r)
module _ {ℓ} {X : Set ℓ} {A B : X → Set ℓ} (A≃B : (x : X) → A x ≃ B x) where
  private
    e : (x : X) → A x → B x
    e x = A≃B x .fst

    to : ((x : X) → A x) → ((x : X) → B x)
    to a x = e x (a x)

    h : ∀ b → ((x : X) → fiber (e x) (b x)) ≃ fiber to b
    h b =   ((x : X) → fiber (e x) (b x))
          ≃⟨ prop ⟩
            Σ ((x : X) → (A x)) (λ a → Homotopy b (to a))
          ≃⟨ _ , totalEquiv _ _ _ (λ _ → inverseEquiv FUNEXT .snd) ⟩
            fiber to b □

  ex2-17-iii-Π-r : ((x : X) → A x) ≃ ((x : X) → B x)
  ex2-17-iii-Π-r = to , λ b → equivPreservesNType {n = ⟨-2⟩} (h b) (piPresNType ⟨-2⟩ (λ x → A≃B x .snd (b x)))
