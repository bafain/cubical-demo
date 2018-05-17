open import Cubical.FromStdLib

-- The sequential colimit of (A, a) is defined to be the graph
-- quotient of the graph Γ = (Γ₀,Γ₁) with vertices
--
--   (n,x), (m,y) : Σ (n : ℕ) A(n)
--
-- and edges
--
--   (p,q) : Σ (p : n + 1 ≡ m) aₙ(x) ≡ₚ y
--
-- from (n,x) to (m,y).[Rijke17]
module Cubical.SeqColimit {ℓ} {A : ℕ → Set ℓ} (a^ : (n : ℕ) → A n → A (suc n)) where

open import Cubical.PathPrelude

Γ₀ : Set ℓ
Γ₀ = Σ ℕ λ n → A n

Γ₁ : Γ₀ → Γ₀ → Set ℓ
Γ₁ (n , x) my = (suc n , a^ n x) ≡ my -- ≃ Σ (suc n ≡ m) λ n+1≡m → PathP (λ i → A (n+1≡m i)) (a^ n x) my

open import Cubical.Quotient Γ₀ Γ₁ renaming (elim to quot-elim; elim-β₀ to quot-elim-β₀; elim-β₁ to quot-elim-β₁)

-- a∞
colim : Set ℓ
colim = quot

in^ : (n : ℕ) → A n → colim
in^ n x = [ n , x ]

in^_-path : ∀ n x → in^ n x ≡ in^ (suc n) (a^ n x) -- ≃ in^ n ≡ in^ (suc n) ∘ a^ n
in^_-path n x = constr₁ refl

module _ {T : colim → Set ℓ}
         (f^ : (n : ℕ) → (x : A n) → T (in^ n x))
         (f^_-path : ∀ n x → PathP (λ i → T (in^ n -path x i)) (f^ n x) (f^ (suc n) (a^ n x))) where
  private
    f : (nx : Γ₀) → T [ nx ]
    f (n , x) = f^ n x

    well-defined : ∀ {nx my} (nx~my : Γ₁ nx my) → PathP (λ i → T (constr₁ nx~my i)) (f nx) (f my)
    well-defined {nx@(n , x)} {my} nx~my = pathJ (λ my nx~my → PathP (λ i → T (constr₁ nx~my i)) (f nx) (f my)) (f^ n -path x) my nx~my

  elim : (x : colim) → T x
  elim = quot-elim f well-defined

  elim-β₀ : ∀ n x → elim (in^ n x) ≡ f^ n x
  elim-β₀ n x = quot-elim-β₀ {T} f well-defined (n , x)

  elim-β₁ : ∀ n x → cong-d elim (in^ n -path x) ≡ f^ n -path x
  elim-β₁ n x = trans (quot-elim-β₁ {T} f well-defined refl)
                      (pathJprop (λ my nx~my → PathP (λ i → T (constr₁ nx~my i)) (f (n , x)) (f my)) (f^ n -path x))
