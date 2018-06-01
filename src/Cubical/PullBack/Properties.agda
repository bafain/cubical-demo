{-# OPTIONS --cubical #-}
module Cubical.PullBack.Properties {ℓ} where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Properties
open import Cubical.Fiberwise
open import Cubical.Lemmas
open import Cubical.NType
open import Cubical.NType.Properties
open import Cubical.PullBack as PB

private
  module _ {A B C D : Set ℓ}
           {f : A → D} {g : B → D} {p : C → A} {q : C → B}
           (H : Homotopy (f ∘ p) (g ∘ q)) where
    Q : ∀ a → fiber p a → fiber g (f a)
    Q a (c , a≡pc) = q c , cong f a≡pc ◾ H c

module _ {A B C D : Set ℓ}
         {f : A → D} {g : B → D}
         (let open PB.Cone f g)
         (c : C -cone) where
  open _-cone
  open PB.Canonical f g

  private
    p = c .p₁
    q = c .p₂
    H = c .fp₁∼gp₂

  unique : isPullBack c ≃ isEquiv _ _ ⟨ p , q , H ⟩
  unique = to , lem3-3-3 (propIsPullBack c) (propIsEquiv ⟨ p , q , H ⟩) to from
    where
      h : ∀ {C'} → Homotopy (toCone 𝒫 ∘ (⟨ p , q , H ⟩ ∘_)) (toCone c {C'})
      h = hid

      to : isPullBack c → isEquiv _ _ ⟨ p , q , H ⟩
      to pbc = inverse (lem492 ⟨ p , q , H ⟩) (λ _ → inverse (thm471 _ _ (pbc _)) (prop _))

      from : isEquiv _ _ ⟨ p , q , H ⟩ → isPullBack c
      from equiv⟨p,q⟩ _ = compEquiv (_ , lem492 ⟨ p , q , H ⟩ .fst equiv⟨p,q⟩ _) (_ , prop _) .snd

  lem7-6-8 : isPullBack c ≃ (∀ a → isEquiv _ _ (Q H a))
  lem7-6-8 = to , lem3-3-3 (propIsPullBack c) (piPresNType ⟨-1⟩ λ a → propIsEquiv (Q H a)) to from
    where
      H' : Homotopy (total _ _ (Q H) ∘ lem4-8-2 p .fst) ⟨ p , q , H ⟩
      H' c = λ i → p c , q c , trans-id-l (H c) i

      to : isPullBack c → (∀ a → isEquiv _ _ (Q H a))
      to pbc a = fiberEquiv _ _ (Q H) (thm471 _ _ (∼-preserves-isEquiv (hinv H') .fst (unique .fst pbc)) .fst (lem4-8-2 p .snd)) a

      from : (∀ a → isEquiv _ _ (Q H a)) → isPullBack c
      from equivQ = inverse unique (∼-preserves-isEquiv H' .fst (compEquiv (lem4-8-2 p) (_ , totalEquiv _ _ _ equivQ) .snd))
