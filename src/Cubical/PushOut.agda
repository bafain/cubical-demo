{-# OPTIONS --cubical #-}
module Cubical.PushOut where

open import Cubical.PathPrelude hiding (glue)
open import Cubical.Equivalence.HAE
open import Cubical.Sub
open import Cubical.FromStdLib
open import Cubical.NType
open import Cubical.NType.Properties

postulate
  P : ∀ {l} → {A B C : Set l} → (f : C → A) (g : C → B) → Set l
  inl : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → A → P f g
  inr : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → B → P f g
  push : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → (c : C) → inl {C = C} {f} {g} (f c) ≡ inr (g c)

{-# BUILTIN PUSHOUT P #-}
{-# BUILTIN PUSHOUTINL inl #-}
{-# BUILTIN PUSHOUTINR inr #-}
{-# BUILTIN PUSHOUTPUSH push #-}


primitive
  primPushOutHComp : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → (φ : I) → (u : (i : I) → Partial (P f g) φ) → Sub {l} (P f g) φ (u i0) → P f g
  primPushOutForward : ∀ {l : I → Level} → {A B C : (i : I) → Set (l i)} → {f : ∀ i → C i → A i} {g : ∀ i → C i → B i} →
                    (r : I) → (u : P (f r) (g r)) → P (f i1) (g i1)
  primPushOutElim : ∀ {l m} → {A B C : Set l} → {f : C → A} {g : C → B} → (M : P f g -> Set m)
                    → (il : ∀ a → M (inl a)) (ir : ∀ b → M (inr b))
                    → (p : ∀ c → PathP (\ i → M (push c i)) (il (f c)) (ir (g c)))
                    → ∀ x → M x

module _ {ℓ} {A B C : Set ℓ} where
  module _ (f : C → A) (g : C → B) where
    PushOut : Set ℓ
    PushOut = P f g

  -- Definition 6.8.1
  module Cocone (f : C → A) (g : C → B) where
    record _-cocone (D : Set ℓ) : Set ℓ where
      constructor cocone
      field
        i : A → D
        j : B → D
        h : Homotopy (i ∘ f) (j ∘ g)

  module _ {f : C → A} {g : C → B} where
    open Cocone f g

    module _ {P : Set ℓ} (c : P -cocone) where
      open _-cocone c

      toCocone : ∀ {E : Set ℓ} → (P → E) → E -cocone
      toCocone t = record { i = t ∘ i
                          ; j = t ∘ j
                          ; h = cong t ∘ h }

      isPushOut : Set (ℓ-suc ℓ)
      isPushOut = ∀ E → isEquiv (P → E) (E -cocone) toCocone

      propIsPushOut : isProp isPushOut
      propIsPushOut = piPresNType ⟨-1⟩ (λ x → propIsEquiv _)

  module Canonical (f : C → A) (g : C → B) where
    open Cocone f g

    glue : ∀ c → inl (f c) ≡ inr (g c)
    glue = push

    glue′ : ∀ {c0 c1 : C} (c : c0 ≡ c1) → inl {f = f} {g = g} (f c0) ≡ inr (g c1)
    glue′{c0} {_} c = glue c0 ◾ cong (inr ∘ g) c

    𝒫 = cocone inl inr glue

    module _ (E : Set ℓ) where
      private
        s : E -cocone → (PushOut f g → E)
        s c = let open _-cocone c in primPushOutElim _ i j h

      lem682 : isEquiv (PushOut f g → E) (E -cocone) (toCocone 𝒫)
      lem682 = thm426 _ _ _ record { g = s
                                   ; η = λ t → funExt (primPushOutElim _ (λ a → refl) (λ b → refl) (λ c i → refl))
                                   ; ε = λ c → refl
                                   ; τ = λ t → refl
                                   }
