{-# OPTIONS --cubical #-}
module Cubical.Equivalence.Properties where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.GradLemma
open import Cubical.NType.Properties
open import Cubical.NType

-- Lemma 2.4.12
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (A≃B : A ≃ B) where
  private
    f : A → B
    f = A≃B .fst

    f⁻¹ : B → A
    f⁻¹ = inverse A≃B

    ff⁻¹ : ∀ b → f (f⁻¹ b) ≡ b
    ff⁻¹ = λ b → sym (A≃B .snd b .fst .snd)

    f⁻¹f : ∀ a → f⁻¹ (f a) ≡ a
    f⁻¹f = λ a → cong fst (A≃B .snd (f a) .snd (a , refl))

  -- (ii)
  inverseEquiv : B ≃ A
  inverseEquiv = inverse A≃B , gradLemma f⁻¹ f f⁻¹f ff⁻¹

  module _ {ℓ''} {C : Set ℓ''} (B≃C : B ≃ C) where
    private
      g : B → C
      g = B≃C .fst

      g⁻¹ : C → B
      g⁻¹ = inverse B≃C

      gg⁻¹ : ∀ c → g (g⁻¹ c) ≡ c
      gg⁻¹ = λ c → sym (B≃C .snd c .fst .snd)

      g⁻¹g : ∀ b → g⁻¹ (g b) ≡ b
      g⁻¹g = λ b → cong fst (B≃C .snd (g b) .snd (b , refl))

      h : A → C
      h = g ∘ f

      h⁻¹ : C → A
      h⁻¹ = f⁻¹ ∘ g⁻¹

      hh⁻¹ : ∀ c → h (h⁻¹ c) ≡ c
      hh⁻¹ c = cong g (ff⁻¹ (g⁻¹ c)) ◾ gg⁻¹ c

      h⁻¹h : ∀ a → h⁻¹ (h a) ≡ a
      h⁻¹h a = cong f⁻¹ (g⁻¹g (f a)) ◾ f⁻¹f a

    -- (iii)
    compEquiv : A ≃ C
    compEquiv = h , gradLemma (g ∘ f) h⁻¹ hh⁻¹ h⁻¹h

infix  3 _≃-qed _□
infixr 2 _≃⟨⟩_ _≃⟨_⟩_

_≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Set ℓ) {B : Set ℓ'} → A ≃ B → A ≃ B
_ ≃⟨⟩ A≃B = A≃B

_≃⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) {B : Set ℓ'} {C : Set ℓ''} → A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ A≃B ⟩ B≃C = compEquiv A≃B B≃C

_≃-qed _□ : ∀ {ℓ} (A : Set ℓ) → A ≃ A
_ ≃-qed  = idEquiv
_□ = _≃-qed

module _ {ℓ} {A B : Set ℓ} where
  private
    module _ {f : A → B} {g : A → B} (H : Homotopy f g) (equivf : isEquiv _ _ f) where
      f⁻¹     = inverse            (_ , equivf)
      ff⁻¹∼id = inverse-section    equivf
      f⁻¹f∼id = inverse-retraction equivf

      ∼-preserves-isEquiv′ : isEquiv _ _ g
      ∼-preserves-isEquiv′ = gradLemma _ f⁻¹ (λ b → g (f⁻¹ b) ≡⟨ sym (H (f⁻¹ b)) ⟩ f (f⁻¹ b) ≡⟨ ff⁻¹∼id b ⟩ b ∎)
                                             (λ a → f⁻¹ (g a) ≡⟨ cong f⁻¹ (sym (H a)) ⟩ f⁻¹ (f a) ≡⟨ f⁻¹f∼id a ⟩ a ∎)

  module _ {f : A → B} {g : A → B} (H : Homotopy f g) where
    ∼-preserves-isEquiv : isEquiv _ _ f ≃ isEquiv _ _ g
    ∼-preserves-isEquiv = ∼-preserves-isEquiv′ H , lem3-3-3 (propIsEquiv _) (propIsEquiv _) _ (∼-preserves-isEquiv′ (hinv H))

module _ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C) where
  module _ (equivgf : isEquiv _ _ (g ∘ f)) where
    private
      gf⁻¹ : C → A
      gf⁻¹ = inverse (_ , equivgf)

      to : isEquiv _ _ f → isEquiv _ _ g
      to equivf = gradLemma _ (f ∘ gf⁻¹) (inverse-section equivgf) fgf⁻¹g~id
        where
          f⁻¹ : B → A
          f⁻¹ = inverse (_ , equivf)

          fgf⁻¹g~id : Homotopy (f ∘ gf⁻¹ ∘ g) (idFun _)
          fgf⁻¹g~id b =   f (gf⁻¹ (g b))
                        ≡⟨ cong (f ∘ gf⁻¹ ∘ g) (sym (inverse-section equivf _)) ⟩
                          f (gf⁻¹ (g (f (f⁻¹ b))))
                        ≡⟨ cong f (inverse-retraction equivgf _) ⟩
                          f (f⁻¹ b)
                        ≡⟨ inverse-section equivf _ ⟩
                          b ∎

      from : isEquiv _ _ g → isEquiv _ _ f
      from equivg = gradLemma _ (gf⁻¹ ∘ g) fgf⁻¹g~id (inverse-retraction equivgf)
        where
          g⁻¹ : C → B
          g⁻¹ = inverse (_ , equivg)

          fgf⁻¹g~id : Homotopy (f ∘ gf⁻¹ ∘ g) (idFun _)
          fgf⁻¹g~id b =   f (gf⁻¹ (g b))
                        ≡⟨ sym (inverse-retraction equivg _) ⟩
                          g⁻¹ (g (f (gf⁻¹ (g b))))
                        ≡⟨ cong g⁻¹ (inverse-section equivgf _) ⟩
                          g⁻¹ (g b)
                        ≡⟨ inverse-retraction equivg _ ⟩
                          b ∎

    thm471 : isEquiv _ _ f ≃ isEquiv _ _ g
    thm471 = _ , lem3-3-3 (propIsEquiv _) (propIsEquiv _) to from

  module _ (equivg : isEquiv _ _ g) where
    compEquiv-r : isEquiv _ _ f ≃ isEquiv _ _ (g ∘ f)
    compEquiv-r = (λ equivf → compEquiv (_ , equivf) (_ , equivg) .snd)
                , lem3-3-3 (propIsEquiv _) (propIsEquiv _) _ (λ equivgf → inverse (thm471 equivgf) equivg)

  module _ (equivf : isEquiv _ _ f) where
    compEquiv-l : isEquiv _ _ g ≃ isEquiv _ _ (g ∘ f)
    compEquiv-l = (λ equivg → compEquiv (_ , equivf) (_ , equivg) .snd)
                , lem3-3-3 (propIsEquiv _) (propIsEquiv _) _ (λ equivgf → thm471 equivgf .fst equivf)

module _ {ℓ} {A B : Set ℓ} (f : A → B) where
  private
    h : ∀ {C : Set ℓ} → C ≃ (⊤ {ℓ} → C)
    h = (λ a _ → a) , λ A → (A tt , refl) , λ { (a' , A≡a') i → A≡a' i tt , λ j → A≡a' (i ∧ j) }

  -- using function extensionality
  lem492 : isEquiv A B f ≃ ∀ (X : Set ℓ) → isEquiv (X → A) (X → B) (f ∘_)
  lem492 = to , lem3-3-3 (propIsEquiv _) (piPresNType ⟨-1⟩ λ _ → propIsEquiv _) to from
    where
      to : isEquiv A B f → ∀ (X : Set ℓ) → isEquiv (X → A) (X → B) (f ∘_)
      to equivf X  = let f⁻¹ = inverse (f , equivf)
                     in gradLemma (f ∘_)
                                  (f⁻¹ ∘_)
                                  (λ g → funExt λ x → inverse-section    equivf (g x))
                                  (λ g → funExt λ x → inverse-retraction equivf (g x))
      from : (∀ (X : Set ℓ) → isEquiv (X → A) (X → B) (f ∘_)) → isEquiv A B f
      from equivf∘ = let A≃B = A ≃⟨ h ⟩ (⊤ → A) ≃⟨ _ , equivf∘ _ ⟩ (⊤ → B) ≃⟨ inverseEquiv h ⟩ B □
                     in A≃B .snd

module _ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} (A≃B : (x : X) → A x ≃ B x) where
  private
    f : (x : X) → A x → B x
    f x = A≃B x .fst

    equivf : (x : X) → isEquiv _ _ (f x)
    equivf x = A≃B x .snd

  lem492-d : isEquiv ((x : X) → A x) ((x : X) → B x) (λ g x → f x (g x))
  lem492-d = let  f⁻¹ : (x : X) → B x → A x
                  f⁻¹ x = inverse (f x , equivf x)
             in gradLemma (λ g x → f x (g x))
                          (λ g x → f⁻¹ x (g x))
                          (λ g → funExt λ x → inverse-section    (equivf x) (g x))
                          (λ g → funExt λ x → inverse-retraction (equivf x) (g x))
