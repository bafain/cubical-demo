{-# OPTIONS --cubical #-}
module Cubical.Lemmas where

open import Cubical.PathPrelude
open import Cubical.Comp

module _ {ℓ} (A : (i : I) → Set ℓ) {φ : I} (u : (i : I) → Partial (A i) φ) (a0 : A i0 [ φ ↦ u i0 ]) where
  comp-uniq : (x : (i : I) → A i [ (~ i) ∨ φ ↦ (λ { (i = i0) → ouc a0 ; (φ = i1) → u i itIsOne }) ])
            → ouc (x i1) ≡ comp A u a0 -- [ φ ↦ refl ]
  comp-uniq x j = comp A (λ { k (j = i0) → ouc (x k) ; k (φ = i1) → u k itIsOne }) (inc (ouc a0))

-- Lemma 2.1.4
module _ {ℓ} {A : Set ℓ} where
  module _ {x y : A} (p : x ≡ y) where
    -- (i)
    trans-id : trans p (\ i → y) ≡ p
    trans-id i j = Cubical.Comp.fill (λ _ → A) _
                               (λ { i (j = i0) → x
                                  ; i (j = i1) → y })
                               (inc (p j))
                               (~ i)

    -- (i)
    trans-id-l : trans (\ i → x) p ≡ p
    trans-id-l i j = comp (λ _ → A)
                               (λ { k (j = i0) → x
                                  ; k (j = i1) → p k
                                  ; k (i = i1) → p (k ∧ j) })
                               (inc x)

    -- (ii)
    trans-inv-r : p ◾ sym p ≡ refl
    trans-inv-r i j = comp-uniq _ (λ { k (j = i0) → x ; k (j = i1) → (sym p) k })
                                  (inc (p j))
                                  (λ k → inc (p (~ k ∧ j)))
                                  (~ i)

    -- (ii)
    trans-inv-l : sym p ◾ p ≡ refl
    trans-inv-l i j = comp-uniq _ (λ { k (j = i0) → y ; k (j = i1) → p k })
                                  (inc ((sym p) j))
                                  (λ k → inc (p (k ∨ ~ j)))
                                  (~ i)
    --              = trans-inv-r (sym p)

  module _ {x y z a : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ a} where
    -- (iv)
    trans-assoc : (trans p (trans q r)) ≡ trans (trans p q) r
    trans-assoc = pathJ (\ y p → (q : y ≡ z) → (trans p (trans q r)) ≡ trans (trans p q) r)
                        (\ q → trans (trans-id-l _) (cong (λ q → trans q r) (sym (trans-id-l _))))
                        y p q

trans-cong : ∀ {l l'} {A : Set l} {B : Set l'}{x y} (f : A → B)(eq : x ≡ y) z (eq' : y ≡ z)
               → trans (\ i → f (eq i)) (\ i → f (eq' i)) ≡ (\ i → f (trans eq eq' i))
trans-cong f eq = pathJ _ (trans (trans-id (λ z → f (eq z))) \ j i →  f (trans-id eq (~ j) i) )

module _ {ℓa ℓb : _} {A : Set ℓa} {B : Set ℓb} where
  module _ {f g : A → B} {x y : A} (H : ∀ x → f x ≡ g x) (p : x ≡ y) where
    -- Lemma 2.4.3:
    lem2-4-3 : trans (H x) (cong g p) ≡ trans (cong f p) (H y)
    lem2-4-3 = pathJ (λ y p → trans (H x) (cong g p) ≡ trans (cong f p) (H y))
                     (trans (trans-id (H x)) (sym (trans-id-l (H x)))) y p
