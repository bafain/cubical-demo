{-# OPTIONS --cubical #-}
module Cubical.Equivalence.Homotopy {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where

open import Cubical.PathPrelude
open import Cubical.FromStdLib

open import Cubical.Equivalence.Embedding
open import Cubical.Equivalence.Properties
open import Cubical.Lemmas

module _ {f g h : A → B} {f∼g : Homotopy f g} where
  htrans-equiv-1 : isEquiv (Homotopy g h) (Homotopy f h) (f∼g ·_)
  htrans-equiv-1 = subst {P = λ hole → isEquiv (Homotopy g h) (Homotopy f h) hole} (funExt l) (pathToEquiv (λ i → Homotopy (λ a → f∼g a (~ i)) h) .snd)
    where
      l : ∀ (g∼h : Homotopy g h) → transp (λ i → Homotopy (λ a → f∼g a (~ i)) h) g∼h ≡ f∼g · g∼h
      l g∼h =   transp (λ i → Homotopy (λ a → f∼g a (~ i)) h) g∼h
              ≡⟨ transp-homotopy g∼h (sym (funExt f∼g)) refl ⟩
                f∼g · g∼h · hid
              ≡⟨ htrans-id (f∼g · g∼h) ⟩
                f∼g · g∼h ∎

  htrans-equiv-2 : isEquiv (Homotopy h f) (Homotopy h g) (_· f∼g)
  htrans-equiv-2 = subst {P = λ hole → isEquiv (Homotopy h f) (Homotopy h g) hole} (funExt l) (pathToEquiv (λ i → Homotopy h (λ a → f∼g a i)) .snd)
    where
      l : ∀ (h∼f : Homotopy h f) → transp (λ i → Homotopy h (λ a → f∼g a i)) h∼f ≡ h∼f · f∼g
      l h∼f =   transp (λ i → Homotopy h (λ a → f∼g a i)) h∼f
              ≡⟨ transp-homotopy h∼f refl (funExt f∼g) ⟩
                hid · h∼f · f∼g
              ≡⟨ cong (_· f∼g) (htrans-id-l h∼f) ⟩
                h∼f · f∼g ∎

  module _ {I I' : Homotopy g h} where
    htrans-left-cancel : (I ≡ I') ≃ (f∼g · I ≡ f∼g · I')
    htrans-left-cancel = _ , thm2-11-1 _ htrans-equiv-1 I I'

  module _ {I I' : Homotopy h f} where
    htrans-right-cancel : (I ≡ I') ≃ (I · f∼g ≡ I' · f∼g)
    htrans-right-cancel = _ , thm2-11-1 _ htrans-equiv-2 I I'

module _ {f g f' g' : A → B} {f∼g : Homotopy f g} {f'∼g' : Homotopy f' g'} {f≡f' : f ≡ f'} {g≡g' : g ≡ g'} where
  private
    f∼f' = happly f≡f'
    g∼g' = happly g≡g'

    h : f∼f' · (hinv f∼f' · f∼g) ≡ f∼g
    h = htrans-assoc _ _ _ ◾ cong (_· f∼g) (htrans-inv-r f∼f') ◾ htrans-id-l f∼g

    h' : f∼f' · (hinv f∼f' · f∼g · g∼g') ≡ f∼g · g∼g'
    h' = htrans-assoc _ _ _ ◾ cong (_· g∼g') h

  homotopy-≡ : PathP (λ i → Homotopy (f≡f' i) (g≡g' i)) f∼g f'∼g' ≃ (f∼g · g∼g' ≡ f∼f' · f'∼g')
  homotopy-≡ =   PathP (λ i → Homotopy (f≡f' i) (g≡g' i)) f∼g f'∼g'
               ≃⟨ _ , fromPathP-equiv ⟩
                 transp (λ i → Homotopy (f≡f' i) (g≡g' i)) f∼g ≡ f'∼g'
               ≃⟨ pathToEquiv (λ i → transp-homotopy f∼g f≡f' g≡g' i ≡ f'∼g') ⟩
                 hinv f∼f' · f∼g · g∼g' ≡ f'∼g'
               ≃⟨ htrans-left-cancel ⟩
                 f∼f' · (hinv f∼f' · f∼g · g∼g') ≡ f∼f' · f'∼g'
               ≃⟨ pathToEquiv (λ i → h' i ≡ f∼f' · f'∼g') ⟩
                 f∼g · g∼g' ≡ f∼f' · f'∼g' □
