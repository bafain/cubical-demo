{-# OPTIONS --cubical #-}
module Cubical.PullBack {ℓ} {A B C : Set ℓ} where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Homotopy
open import Cubical.Fiberwise
open import Cubical.NType
open import Cubical.NType.Properties

module Cone (f : A → C) (g : B → C) where
  record _-cone (T : Set ℓ) : Set ℓ where
    constructor cone
    field
      p₁      : T → A
      p₂      : T → B
      fp₁∼gp₂ : Homotopy (f ∘ p₁) (g ∘ p₂)

module _ {f : A → C} {g : B → C} where
  open Cone f g

  module _ (T : Set ℓ) where
    private
      T-cone-Σ : Set ℓ
      T-cone-Σ = Σ (T → A) λ p → Σ (T → B) λ q → Homotopy (f ∘ p) (g ∘ q)

      to-Σ : T -cone → T-cone-Σ
      to-Σ c = let open _-cone c in p₁ , p₂ , fp₁∼gp₂

      from-Σ : T-cone-Σ → T -cone
      from-Σ (p₁ , p₂ , fp₁∼gp₂) = cone p₁ p₂ fp₁∼gp₂

    cone-Σ-equiv : T -cone ≃ T-cone-Σ
    cone-Σ-equiv = to-Σ , λ σ → (from-Σ σ , refl) , λ σ≡c i → from-Σ (σ≡c .snd i) , λ j → σ≡c .snd (i ∧ j)

  module _ {T : Set ℓ} (c c' : T -cone) where
    private
      _T-cone-Σ-≡_ : T -cone → T -cone → Set ℓ
      cone p q H T-cone-Σ-≡ cone p' q' H' = Σ (p ≡ p') λ P → Σ (q ≡ q') λ Q → PathP (λ i → Homotopy (f ∘ P i) (g ∘ Q i)) H H'

      _T-cone-≡_ : T -cone → T -cone → Set ℓ
      cone p q H T-cone-≡ cone p' q' H' = Σ (p ≡ p') λ P → Σ (q ≡ q') λ Q → H · happly (cong (g ∘_) Q) ≡ happly (cong (f ∘_) P) · H'

      T-cone-Σ-≡-contr : isContr (Σ (T -cone) λ c' → c T-cone-Σ-≡ c')
      T-cone-Σ-≡-contr = (c , refl , refl , refl)
                         , λ { (_ , p≡p' , q≡q' , H≡H') i → cone (p≡p' i) (q≡q' i) (H≡H' i)
                                                          , (λ j → p≡p' (i ∧ j)) , (λ j → q≡q' (i ∧ j)) , λ j → H≡H' (i ∧ j) }

      T-cone-≡-contr : isContr (Σ (T -cone) λ c' → c T-cone-≡ c')
      T-cone-≡-contr = equivPreservesNType {n = ⟨-2⟩} (_ , totalEquiv _ _ _ (λ c' → h c' .snd)) T-cone-Σ-≡-contr
        where
          h : ∀ c' → c T-cone-Σ-≡ c' ≃ c T-cone-≡ c'
          h _ = _ , totalEquiv _ _ _ (λ P → totalEquiv _ _ _ (λ Q → homotopy-≡ .snd))

    cone-≡ : (c ≡ c') ≃ (c T-cone-≡ c')
    cone-≡ = r c' , fiberEquiv (λ c' → c ≡ c') (λ c' → c T-cone-≡ c') r (contrEquiv contrSingl T-cone-≡-contr) c'
      where
        r : ∀ c' → c ≡ c' → c T-cone-≡ c'
        r = pathJ _ (T-cone-≡-contr .fst .snd)

module _ {f : A → C} {g : B → C} where
  open Cone f g

  module _ {P : Set ℓ} (c : P -cone) where
    module _ {T : Set ℓ} where
      open _-cone c

      toCone : (T → P) → T -cone
      toCone ⟨q₁,q₂⟩ = cone (p₁ ∘ ⟨q₁,q₂⟩) (p₂ ∘ ⟨q₁,q₂⟩) (right-whisker ⟨q₁,q₂⟩ fp₁∼gp₂)

    isPullBack : Set (ℓ-suc ℓ)
    isPullBack = ∀ T → isEquiv (T → P) (T -cone) toCone

    propIsPullBack : isProp isPullBack
    propIsPullBack = piPresNType ⟨-1⟩ λ _ → propIsEquiv toCone

module _ (f : A → C) (g : B → C) where
  PullBack : Set ℓ
  PullBack = Σ A λ a → Σ B λ b → f a ≡ g b

module Canonical (f : A → C) (g : B → C) where
  open Cone f g

  π₁ : PullBack f g → A
  π₁ (a , _ , _) = a

  π₂ : PullBack f g → B
  π₂ (_ , b , _) = b

  pull : Homotopy (f  ∘ π₁) (g ∘ π₂)
  pull (_a , _b , fa≡gb) = fa≡gb

  𝒫 = cone π₁ π₂ pull

  ⟨_,_,_⟩ : {T : Set ℓ} → (p₁ : T → A) → (p₂ : T → B) → Homotopy (f ∘ p₁) (g ∘ p₂) → T → PullBack f g
  ⟨ p₁ , p₂ , fp₁∼gp₂ ⟩ t = p₁ t , p₂ t , fp₁∼gp₂ t

  prop : isPullBack 𝒫
  prop T = λ c → (fromCone c , refl)
                 , λ { (⟨p₁,p₂⟩ , c≡p) → λ i → fromCone (c≡p i) , λ j → c≡p (i ∧ j) }
    where
      fromCone : T -cone → T → PullBack f g
      fromCone c = let open _-cone c in ⟨ p₁ , p₂ , fp₁∼gp₂ ⟩
