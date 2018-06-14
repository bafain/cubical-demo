{-# OPTIONS --cubical #-}
module Cubical.Flattening where

open import Cubical.FromStdLib
open import Cubical.PathPrelude         hiding (glue)

open import Cubical.PushOut     as PO

-- Proposition 1.9.2 in Brunerie16
module PushOut {ℓ ℓ'}
               {A B C : Set ℓ}
               (f : C → A) (g : C → B)
               (P : PushOut f g → Set ℓ')
               (let Pinl : A → Set ℓ'; Pinl = P ∘ inl)
               (let Pinr : B → Set ℓ'; Pinr = P ∘ inr)
               (let Ppush : (c : C) → Pinl (f c) ≡ Pinr (g c); Ppush c i = P (push c i)) where

  open import Cubical.GradLemma
  open import Cubical.PushOut.Properties

  private
    -- P : PushOut f g → Set ℓ
    -- P = primPushOutElim _ Pinl Pinr Ppush

    left : Σ C (λ z → Σ (Pinl (f z)) λ u → Σ (Pinr (g z)) λ v → PathP (λ i → Ppush z i) u v) → Σ A (λ x → Pinl x)
    left (z , u , _ , _) = f z , u

    right : Σ C (λ z → Σ (Pinl (f z)) λ u → Σ (Pinr (g z)) λ v → PathP (λ i → Ppush z i) u v) → Σ B (λ y → Pinr y)
    right (z , _ , v , _) = g z , v

    open PO.Cocone left right
    open PO.Canonical left right

    i : Σ A (λ x → Pinl x) → Σ (PushOut f g) P
    i (x , u) = inl x , u

    j : Σ B (λ y → Pinr y) → Σ (PushOut f g) P
    j (y , v) = inr y , v

    h : Homotopy (i ∘ left) (j ∘ right)
    h (z , _ , _ , w) i = push z i , w i -- id∼transp {A = λ i → Ppush z i} u i

    c : Σ (PushOut f g) P -cocone
    c = cocone i j h

    [i,j] : PushOut left right → Σ (PushOut f g) P
    [i,j] = inverse (_ , lem682 _) (cocone i j h)

    p : ∀ z → PathP (λ i → P (push z i) → PushOut left right) (inl ∘ (f z ,_)) (inr ∘ (g z ,_))
    p z = funExtP (λ w → push (z , _ , _ , w))

    [i,j]⁻¹ : Σ (PushOut f g) P → PushOut left right
    [i,j]⁻¹ (a , w) = primPushOutElim (λ a → ∀ (w : P a) → PushOut left right)
                                      (λ a w → inl (a , w))
                                      (λ b w → inr (b , w))
                                      -- (λ c → toPathP⁻¹ (funExt (λ w → push (c , w) ◾ sym (transp-refl (inr (right (c , w)))))))
                                      (λ z → p z)
                                      a
                                      w

    [i,j]⁻¹-β-i : ∀ x → [i,j]⁻¹ (i x) ≡ inl x
    [i,j]⁻¹-β-i xu = refl

    [i,j]⁻¹-β-j : ∀ x → [i,j]⁻¹ (j x) ≡ inr x
    [i,j]⁻¹-β-j xv = refl

    [i,j]⁻¹-β-h : ∀ zuvw → cong [i,j]⁻¹ (h zuvw) ≡ push zuvw
    [i,j]⁻¹-β-h zuvw = funExtP-β (λ w → push (zuvw .fst , _ , _ , w)) (zuvw .snd .snd .snd)

    [i,j]⁻¹[i,j]∼id : Homotopy ([i,j]⁻¹ ∘ [i,j]) (idFun _)
    [i,j]⁻¹[i,j]∼id = primPushOutElim _ [i,j]⁻¹-β-i [i,j]⁻¹-β-j (λ zuvw i j → [i,j]⁻¹-β-h zuvw j i)

    [i,j][i,j]⁻¹∼id : Homotopy ([i,j] ∘ [i,j]⁻¹) (idFun _)
    [i,j][i,j]⁻¹∼id (a , w) = primPushOutElim (λ a → ∀ w → [i,j] ([i,j]⁻¹ (a , w)) ≡ (a , w))
                                              (λ _ _ → refl)
                                              (λ _ _ → refl)
                                              (λ z → funExtP (λ w i j → [i,j] (funExtP-β (λ w → push (z , _ , _ , w)) w j i)))
                                              a
                                              w

  flatteningLemma : isPushOut (cocone i j h)
  flatteningLemma = inverse unique (gradLemma _ [i,j]⁻¹ [i,j][i,j]⁻¹∼id [i,j]⁻¹[i,j]∼id)

open import Cubical.CoEqualizer as CoEq

module CoEqualizer {ℓ}
                   {A B : Set ℓ}
                   (f g : A → B)
                   (let open TheCoEq A B f g renaming (coeq to inj; coeq-path to coeq))
                   (P : CoEq → Set ℓ)
                   (let Pinj : B → Set ℓ; Pinj = P ∘ inj)
                   (let Pcoeq : (a : A) → Pinj (f a) ≡ Pinj (g a); Pcoeq a i = P (coeq a i)) where
  private
    record Pm (a : A) : Set ℓ where
      constructor pm
      field
        {α0} : Pinj (f a)
        {α1} : Pinj (g a)
        α    : PathP (λ i → Pcoeq a i) α0 α1
    -- Pm a = Σ (Pinj (f a)) λ x → Σ (Pinj (g a)) λ y → PathP (λ i → Pcoeq a i) x y

    Σf : Σ A Pm → Σ B Pinj
    Σf (a , pm α) = f a , α i0

    Σg : Σ A Pm → Σ B Pinj
    Σg (a , pm α) = g a , α i1

    Σi : Σ B Pinj → Σ CoEq P
    Σi (b , z) = inj b , z

    Σif≡Σig : Homotopy (Σi ∘ Σf) (Σi ∘ Σg)
    Σif≡Σig (a , pm α) i = coeq a i , α i

    open TheCoEq _ _ Σf Σg renaming (CoEq to ΣCoEq; coeq to Σinj; coeq-path to Σcoeq; module Elim to ΣElim)
    open ΣElim             renaming (coeq-elim to ΣCoEq-elim; coeq-elim-path to ΣCoEq-elim-β₁)

    u : ΣCoEq → Σ CoEq P
    u = ΣCoEq-elim Σi Σif≡Σig

    open Elim renaming (coeq-elim-path to coeq-elim-β₁)

    h₀ : ∀ a → PathP (λ i → P (coeq a i) → ΣCoEq) (curry Σinj (f a)) (curry Σinj (g a))
    abstract h₀ a = funExtP (λ α → Σcoeq (a , pm α))

    u⁻¹ : Σ CoEq P → ΣCoEq
    u⁻¹ (b , z) = coeq-elim {C = λ b → ∀ (z : P b) → ΣCoEq}
                            (curry Σinj)
                            h₀
                            b
                            z

    uu⁻¹≡id : Homotopy (u ∘ u⁻¹) (idFun _)
    uu⁻¹≡id (b , z) = {!!}

    h₁ : ∀ (f : Σ CoEq P → ΣCoEq) (σpm : Σ A Pm) → cong (f ∘ u) (Σcoeq σpm) ≡ cong f (Σif≡Σig σpm) -- PathP (λ i → u (Σcoeq σpm i) ≡ Σif≡Σig σpm i) refl refl
    abstract h₁ f σpm i j = f (ΣCoEq-elim-β₁ Σi Σif≡Σig σpm i j)

    h₂ : ∀ a (pma : Pm a) (let open Pm pma) → cong u⁻¹ (Σif≡Σig (a , pma)) ≡ papplyP (h₀ a) α -- PathP (λ i → u⁻¹ (Σif≡Σig (a , pma) i) ≡ h₀ a i (α i)) refl refl
    abstract h₂ a (pm α) i j = coeq-elim-β₁ {C = λ b → ∀ (z : P b) → ΣCoEq} (curry Σinj) h₀ a i j (α j)

    h₁₂ : ∀ a (pma : Pm a) (let open Pm pma) → cong (u⁻¹ ∘ u) (Σcoeq (a , pma)) ≡ papplyP (h₀ a) α
    abstract h₁₂ a pma = trans (h₁ u⁻¹ (a , pma)) (h₂ a pma)

    h₃ : ∀ a (pma : Pm a) (let open Pm pma) → papplyP (h₀ a) α ≡ Σcoeq (a , pma) -- PathP (λ i → h₀ a i (α i) ≡ Σcoeq (a , pma) i) refl refl
    abstract h₃ a (pm α) = funExtP-β (λ α → Σcoeq (a , pm α)) α

    h₁₂₃ : ∀ (σpm : Σ A Pm) → cong (u⁻¹ ∘ u) (Σcoeq σpm) ≡ Σcoeq σpm
    abstract h₁₂₃ (a , pma) = trans (h₁₂ a pma) (h₃ a pma)

    u⁻¹u≡id : Homotopy (u⁻¹ ∘ u) (idFun _)
    u⁻¹u≡id = ΣCoEq-elim (λ _ → refl) λ { σpm → rotate (h₁₂₃ σpm) }
