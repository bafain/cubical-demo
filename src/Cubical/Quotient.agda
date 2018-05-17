-- The graph quotient colim(Γ) (Definition 1.2 in Rijke17) of
-- a graph Γ = (Γ₀,Γ₁) (Definition 1.1 in Rijke17) is the coequalizer
-- of the two projections
--
--   src : ΣΓ₁ → Γ₀  and  tgt : ΣΓ₁ → Γ₀
--
-- (Remark 1.3 in Rijke17), where ΣΓ₁ = Σ (i,j : Γ₀) Γ₁(i,j).
module Cubical.Quotient {ℓ}
                        (Γ₀ : Set ℓ)
                        (Γ₁ : Γ₀ → Γ₀ → Set ℓ) where

open import Cubical.PathPrelude
open import Cubical.FromStdLib
open import Cubical.CoEqualizer

private
  ΣΓ₁ : Set ℓ
  ΣΓ₁ = Σ Γ₀ (λ i → Σ Γ₀ (λ j → Γ₁ i j))

  src : ΣΓ₁ → Γ₀
  src = fst

  tgt : ΣΓ₁ → Γ₀
  tgt = fst ∘ snd

open TheCoEq _ _ src tgt

-- colim(Γ)
quot : Set ℓ
quot = CoEq

constr₀ : Γ₀ → quot
constr₀ = coeq

[_] = constr₀

constr₁ : ∀ {i j} (i~j : Γ₁ i j) → [ i ] ≡ [ j ]
constr₁ i~j = coeq-path (_ , _ , i~j)

module _ {T : quot → Set ℓ}
         (f : ∀ i → T [ i ])
         (well-defined : ∀ {i j} (i~j : Γ₁ i j) → PathP (λ x → T (constr₁ i~j x)) (f i) (f j)) where
  open Elim {C = T} f (λ { (i , j , i~j) → well-defined i~j })

  elim : ∀ [i] → T [i]
  elim = coeq-elim

  elim-β₀ : ∀ i → elim [ i ] ≡ f i
  elim-β₀ i = coeq-elim-beta i

  elim-β₁ : ∀ {i j} (i~j : Γ₁ i j) → cong-d elim (constr₁ i~j) ≡ well-defined i~j
  elim-β₁ i~j = coeq-elim-path (_ , _ , i~j)
