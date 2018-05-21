{-# OPTIONS --cubical #-}
module Cubical.Embedding.Properties {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) where

open import Cubical.FromStdLib
open import Cubical.PathPrelude renaming (isEmbedding to isFullyFaithful)
open import Cubical.Comp

open import Cubical.Equivalence.Properties
open import Cubical.Fiberwise
open import Cubical.Lemmas
open import Cubical.NType
open import Cubical.NType.Properties

private
  isEmbedding : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ-max ℓ ℓ')
  isEmbedding f = ∀ y → isProp (fiber f y)

module _ (embedf : isEmbedding f) where
  module _ {ℓ''} {C : Set ℓ''} where
    private
     fiber′ : (k : C → B) → Set (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
     fiber′ k = Σ (C → A) (λ g → Homotopy k (f ∘ g))

    embed₁′ : ∀ k → isProp (fiber′ k)
    embed₁′ k = equivPreservesNType {n = S ⟨-2⟩} AC∞ (piPresNType (S ⟨-2⟩) (embedf ∘ k))

    embed₁ : isEmbedding (f ∘_)
    embed₁ k = equivPreservesNType {n = S ⟨-2⟩} (inverseEquiv (_ , totalEquiv _ _ _ λ g → snd FUNEXT)) (embed₁′ k)

    left-cancel₁ : {g h : C → A} → Homotopy (f ∘ g) (f ∘ h) → Homotopy g h
    left-cancel₁ {g} {h} fg≡fh = λ c → happly (cong fst (embed₁′ (f ∘ g) (g , λ _ → refl) (h , fg≡fh))) c

  module _ {x y} (fx≡fy : f x ≡ f y) where
    left-cancel₀ : x ≡ y
    left-cancel₀ = left-cancel₁ {ℓ-zero} (λ _ → fx≡fy) tt

  ff : isFullyFaithful _ _ f
  ff a = fiberEquiv _ _ (λ _ → cong f) (contrEquiv contrSingl h)
    where
      h : isContr (fiber f (f a))
      h = lemContr' (embedf (f a)) (a , refl)

module _ (fff : isFullyFaithful _ _ f) where
  module _ {b} {b'} (β : b ≡ b') (fibb : fiber f b) (fibb' : fiber f b')
    (let a      = fibb .fst
         b≡fa   = fibb .snd
         a'     = fibb' .fst
         b'≡fa' = fibb' .snd)
    where

    private
      -- b ----> g a
      -- |
      -- |
      -- v
      -- b' ---> g a'
      ga≡ga' : (j i : I) → B
      ga≡ga' j i = Cubical.Comp.fill (λ _ → B)
                                     _
                                     (λ { j (i = i0) → b≡fa j
                                        ; j (i = i1) → b'≡fa' j })
                                     (inc (β i))
                                     j
      a≡a' : a ≡ a'
      a≡a' = inverse (_ , fff a a') (λ i → ga≡ga' i1 i)

      ga≡a'≡ga≡ga' : (λ i → ga≡ga' i1 i) ≡ cong f a≡a'
      ga≡a'≡ga≡ga' = fff a a' (λ i → ga≡ga' i1 i) .fst .snd

    embed-d : PathP (λ i → fiber f (β i)) fibb fibb'
    embed-d i = a≡a' i , ouc (trans-φ {φ = i ∨ ~ i} {z = inc (f (a≡a' i))} (λ j → ga≡ga' j i) (inc (λ j → ga≡a'≡ga≡ga' j i)))
    -- actually, isContr (fiber g (p i)) so that [ ~ i ↦ x ; i ↦ y ] could be extended

  embed : isEmbedding f
  embed b = embed-d refl

prop : isFullyFaithful _ _ f ≃ isEmbedding f
prop = embed , lem3-3-3 propIsEmbedding propIsPropFiber embed ff
  where
    propIsEmbedding = piPresNType (S ⟨-2⟩) λ x → piPresNType (S ⟨-2⟩) λ y → propIsEquiv (cong f)
    propIsPropFiber = piPresNType (S ⟨-2⟩) λ x → propIsProp
