{-# OPTIONS --cubical #-}
module Cubical.Lemmas where

open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.Comp

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

    -- (iii)
    inv-involution : sym (sym p) ≡ p
    inv-involution = refl

  module _ {x y z a : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ a} where
    -- (iv)
    trans-assoc : (trans p (trans q r)) ≡ trans (trans p q) r
    trans-assoc = pathJ (\ y p → (q : y ≡ z) → (trans p (trans q r)) ≡ trans (trans p q) r)
                        (\ q → trans (trans-id-l _) (cong (λ q → trans q r) (sym (trans-id-l _))))
                        y p q

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} (H : Homotopy f g) where
  htrans-id : H · hid ≡ H
  htrans-id = funExt λ a → trans-id (H a)

  htrans-id-l : hid · H ≡ H
  htrans-id-l = funExt λ a → trans-id-l (H a)

  htrans-inv-r : H · hinv H ≡ hid
  htrans-inv-r = funExt λ a → trans-inv-r (H a)

  htrans-inv-l : hinv H · H ≡ hid
  htrans-inv-l = funExt λ a → trans-inv-l (H a)

  module _ {h : A → B} (H' : Homotopy g h) {i : A → B} (H'' : Homotopy h i) where
    htrans-assoc : H · (H' · H'') ≡ (H · H') · H''
    htrans-assoc = funExt λ _ → trans-assoc

trans-cong : ∀ {l l'} {A : Set l} {B : Set l'}{x y} (f : A → B)(eq : x ≡ y) z (eq' : y ≡ z)
               → trans (\ i → f (eq i)) (\ i → f (eq' i)) ≡ (\ i → f (trans eq eq' i))
trans-cong f eq = pathJ _ (trans (trans-id (λ z → f (eq z))) \ j i →  f (trans-id eq (~ j) i) )

module _ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i1} where
  fromPathP-equiv : isEquiv (PathP A x y) (transp A x ≡ y) fromPathP
  fromPathP-equiv = pathToEquiv PathP≡Path .snd

module _ {ℓa ℓb : _} {A : Set ℓa} {B : Set ℓb} where
  module _ {f g : A → B} {x y : A} (H : ∀ x → f x ≡ g x) (p : x ≡ y) where
    -- Lemma 2.4.3:
    lem2-4-3 : trans (H x) (cong g p) ≡ trans (cong f p) (H y)
    lem2-4-3 = pathJ (λ y p → trans (H x) (cong g p) ≡ trans (cong f p) (H y))
                     (trans (trans-id (H x)) (sym (trans-id-l (H x)))) y p

module _ {ℓa ℓb ℓr : _} {A : Set ℓa} {B : A → Set ℓb} {R : (a : A) → B a → Set ℓr} where
  ac : (∀ x → Σ (B x) λ y → R x y) → Σ ((x : A) → B x) λ f → ∀ x → R x (f x)
  ac g = fst ∘ g , snd ∘ g

  ac⁻¹ : (Σ ((x : A) → B x) λ f → ∀ x → R x (f x)) → ∀ x → Σ (B x) λ y → R x y
  ac⁻¹ f = λ x → fst f x , snd f x

  AC∞ : (∀ x → Σ (B x) λ y → R x y) ≃ Σ ((x : A) → B x) λ f → ∀ x → R x (f x)
  AC∞ = ac , λ f → (ac⁻¹ f , refl) , λ fibf i → ac⁻¹ (snd fibf i) , λ j → snd fibf (i ∧ j)

module _ {ℓa ℓb : _} {A : Set ℓa} {B : A → Set ℓb} where
  FUNEXT : {f g : (x : A) → B x} → (f ≡ g) ≃ ((x : A) → f x ≡ g x)
  FUNEXT = happly , λ f~g → (funExt f~g , refl) , λ fibf~g i → funExt (snd fibf~g i) , λ j → snd fibf~g (i ∧ j)
