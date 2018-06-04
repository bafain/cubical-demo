{-# OPTIONS --cubical #-}
module Cubical.PushOut where

open import Cubical.PathPrelude hiding (glue)
open import Cubical.Equivalence.HAE
open import Cubical.Equivalence.Homotopy
open import Cubical.Fiberwise
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

    module _ (D : Set ℓ) where
      private
        D-cocone-Σ : Set ℓ
        D-cocone-Σ = Σ (A → D) λ i → Σ (B → D) λ j → Homotopy (i ∘ f) (j ∘ g)

        to-Σ : D -cocone → D-cocone-Σ
        to-Σ (cocone i j h) = i , j , h

        from-Σ : D-cocone-Σ → D -cocone
        from-Σ (i , j , h) = cocone i j h

        to-Σ-equiv : isEquiv _ _ to-Σ
        to-Σ-equiv = λ c → (from-Σ c , refl) , λ { (c' , c≡toc') r → from-Σ (c≡toc' r) , λ s → c≡toc' (r ∧ s) }

      cocone-Σ-equiv : D -cocone ≃ D-cocone-Σ
      cocone-Σ-equiv = _ , to-Σ-equiv

    module _ {D : Set ℓ} (c c' : D -cocone) where
      private
        _D-cocone-Σ-≡_ : D -cocone → D -cocone → Set ℓ
        cocone i j H D-cocone-Σ-≡ cocone i' j' H' = Σ (i ≡ i') λ i≡i' → Σ (j ≡ j') λ j≡j' → PathP (λ r → Homotopy (i≡i' r ∘ f) (j≡j' r ∘ g)) H H'

        _D-cocone-≡_ : D -cocone → D -cocone → Set ℓ
        cocone i j H D-cocone-≡ cocone i' j' H' = Σ (i ≡ i') λ i≡i' → Σ (j ≡ j') λ j≡j' → H · happly (cong (_∘ g) j≡j') ≡ happly (cong (_∘ f) i≡i') · H'

        D-cocone-Σ-≡-contr : isContr (Σ (D -cocone) λ c' → c D-cocone-Σ-≡ c')
        D-cocone-Σ-≡-contr = (c , refl , refl , refl)
                           , λ { (_ , i≡i' , j≡j' , H≡H') r → cocone (i≡i' r) (j≡j' r) (H≡H' r)
                                                            , (λ s → i≡i' (r ∧ s)) , (λ s → j≡j' (r ∧ s)) , λ s → H≡H' (r ∧ s) }

        D-cocone-≡-contr : isContr (Σ (D -cocone) λ c' → c D-cocone-≡ c')
        D-cocone-≡-contr = equivPreservesNType {n = ⟨-2⟩} (_ , totalEquiv _ _ _ (λ c' → h c' .snd)) D-cocone-Σ-≡-contr
          where
            h : ∀ c' → c D-cocone-Σ-≡ c' ≃ c D-cocone-≡ c'
            h _ = _ , totalEquiv _ _ _ (λ P → totalEquiv _ _ _ (λ Q → homotopy-≡ .snd))

      cocone-≡ : (c ≡ c') ≃ c D-cocone-≡ c'
      cocone-≡ = r c' , fiberEquiv _ _ r (contrEquiv contrSingl D-cocone-≡-contr) c'
        where
          r : ∀ c' → c ≡ c' → c D-cocone-≡ c'
          r = pathJ _ (D-cocone-≡-contr .fst .snd)

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
