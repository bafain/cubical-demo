module Cubical.Equivalence.HAE where

open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.Lemmas
open import Cubical.Sigma

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') (f : A → B) where
  -- Definition 4.2.1
  record ishae : Set (ℓ-max ℓ ℓ') where
    field
      g : B → A
      η : Homotopy (g ∘ f) (idFun A)
      ε : Homotopy (f ∘ g) (idFun B)
      τ : ∀ (x : A) → cong f (η x) ≡ ε (f x)

  module _ (ishaef : ishae) where
    open ishae ishaef

    module _ (y : B) where
      c : fiber f y
      c = g y , sym (ε y)

      module _ {x : A} {p : y ≡ f x} where
        γ : g y ≡ x
        γ = cong g p ◾ η x

        εy⁻¹◾fγ≡p : sym (ε y) ◾ cong f γ ≡ p
        εy⁻¹◾fγ≡p = sym (ε y) ◾ cong f (cong g p ◾ η x)
                       ≡⟨ cong (sym (ε y) ◾_) (sym (trans-cong f (cong g p) _ (η x))) ⟩
                     sym (ε y) ◾ (cong f (cong g p) ◾ cong f (η x))
                       ≡⟨ cong (sym (ε y) ◾_) (cong (_ ◾_) (τ x)) ⟩
                     sym (ε y) ◾ (cong f (cong g p) ◾ ε (f x))
                       ≡⟨ cong (sym (ε y) ◾_) (sym (lem2-4-3 ε p)) ⟩
                     sym (ε y) ◾ (ε y ◾ p)
                       ≡⟨ trans-assoc ⟩
                     (sym (ε y) ◾ ε y) ◾ p
                       ≡⟨ cong (_◾ p) (trans-inv-l (ε y)) ⟩
                     refl ◾ p
                       ≡⟨ trans-id-l p ⟩
                     p ∎

        c≡x,p : c ≡ (x , p)
        c≡x,p = coe (sym (lemPathSig c (x , p))) (γ , toPathP εy⁻¹◾fγ≡p)

      thm426 : isContr (fiber f y)
      thm426 = (c , λ { (x , p) → c≡x,p })
