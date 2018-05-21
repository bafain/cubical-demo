-- Definition 2.1 in Rijke17 (Join of maps)
module Cubical.Join {ℓ} {A B X : Set ℓ} where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.PushOut renaming (inl to po-inl; inr to po-inr)
open import Cubical.PullBack as PB

module _ (f : A → X) (g : B → X) where
  open PB.Canonical f g

  Join : Set ℓ
  Join = PushOut π₁ π₂

module _ {f : A → X} {g : B → X} where
  inl : A → Join f g
  inl = po-inl

  inr : B → Join f g
  inr = po-inr

  join : ∀ {a b} (_ : f a ≡ g b) → inl a ≡ inr b
  join fa≡gb = push (_ , _ , fa≡gb)

  module _ {T : Join f g → Set ℓ}
           (i : (a : A) → T (inl a))
           (j : (b : B) → T (inr b))
           (p : ∀ {a b} (fa≡gb : f a ≡ g b) → PathP (λ i → T (join fa≡gb i)) (i a) (j b)) where
    elim : (x : Join f g) → T x
    elim = primPushOutElim _ i j λ { (a , b , fa≡gb) → p fa≡gb }

    elim-β₀-1 : ∀ a → elim (inl a) ≡ i a
    elim-β₀-1 _ = refl

    elim-β₀-2 : ∀ b → elim (inr b) ≡ j b
    elim-β₀-2 _ = refl

    elim-β₁ : ∀ {a b} (fa≡gb : f a ≡ g b) → cong-d elim (join fa≡gb) ≡ p fa≡gb
    elim-β₁ _ = refl

module _ (f : A → X) (g : B → X) where
  infixr 2 _∗_
  _∗_ : Join f g → X
  _∗_ = elim f g (idFun _)

  _∗_-β₀-1 : Homotopy (_∗_ ∘ inl) f
  _∗_-β₀-1 = elim-β₀-1 f g (idFun _)

  _∗_-β₀-2 : Homotopy (_∗_ ∘ inr) g
  _∗_-β₀-2 = elim-β₀-2 f g (idFun _)

  _∗_-β₁ : ∀ {a b} (fa≡gb : f a ≡ g b) → cong-d _∗_ (join fa≡gb) ≡ fa≡gb
  _∗_-β₁ = elim-β₁ f g (idFun _)
