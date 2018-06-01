module Cubical.PullBack.Properties {ℓ} where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Properties
open import Cubical.NType.Properties
open import Cubical.PullBack as PB

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
