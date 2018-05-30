{-# OPTIONS --cubical #-}
module Cubical.Equivalence.Path {ℓ} {A : Set ℓ} where

open import Cubical.PathPrelude
open import Cubical.FromStdLib

open import Cubical.Equivalence.Embedding
open import Cubical.Equivalence.Properties
open import Cubical.Lemmas

module _ {x y z : A} {p : x ≡ y} where
  trans-equiv-1 : isEquiv (y ≡ z) (x ≡ z) (p ◾_)
  trans-equiv-1 = subst {P = λ hole → isEquiv (y ≡ z) (x ≡ z) hole} (funExt (λ q → lem2-11-2-i q (sym p))) (pathToEquiv (λ i → p (~ i) ≡ z) .snd)

  trans-equiv-2 : isEquiv (z ≡ x) (z ≡ y) (_◾ p)
  trans-equiv-2 = pathToEquiv (λ i → z ≡ p i) .snd

  module _ {q q' : y ≡ z} where
    trans-left-cancel : (q ≡ q') ≃ (p ◾ q ≡ p ◾ q')
    trans-left-cancel = _ , thm2-11-1 _ trans-equiv-1 q q'

  module _ {q q' : z ≡ x} where
    trans-right-cancel : (q ≡ q') ≃ (q ◾ p ≡ q' ◾ p)
    trans-right-cancel = _ , thm2-11-1 _ trans-equiv-2 q q'

module _ {x y x' y' : A} {p : x ≡ y} {p' : x' ≡ y'} {χ : x ≡ x'} {ψ : y ≡ y'} where
  private
    h : χ ◾ (sym χ ◾ p) ≡ p
    h = trans-assoc ◾ cong (_◾ p) (trans-inv-r χ) ◾ trans-id-l p

    h' : χ ◾ (sym χ ◾ p ◾ ψ) ≡ p ◾ ψ
    h' = trans-assoc ◾ cong (_◾ ψ) h

  path-≡ : PathP (λ i → χ i ≡ ψ i) p p' ≃ (p ◾ ψ ≡ χ ◾ p')
  path-≡ =   PathP (λ i → χ i ≡ ψ i) p p'
           ≃⟨ _ , fromPathP-equiv ⟩
             transp (λ i → χ i ≡ ψ i) p ≡ p'
           ≃⟨ pathToEquiv (λ i → transp-path p χ ψ i ≡ p') ⟩
             sym χ ◾ p ◾ ψ ≡ p'
           ≃⟨ trans-left-cancel ⟩
             χ ◾ (sym χ ◾ p ◾ ψ) ≡ χ ◾ p'
           ≃⟨ pathToEquiv (λ i → h' i ≡ χ ◾ p') ⟩
             p ◾ ψ ≡ χ ◾ p' □
