{-# OPTIONS --cubical #-}
module Cubical.PullBack.Properties {ℓ} where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Equivalence.Properties
open import Cubical.Fiberwise
open import Cubical.GradLemma
open import Cubical.Lemmas
open import Cubical.NType
open import Cubical.NType.Properties
open import Cubical.Pi
open import Cubical.PullBack as PB
open import Cubical.Sigma          using (Σ-swap)

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

  module _ (equivg : isEquiv _ _ g) where
    private
      to : (∀ a → isEquiv _ _ (Q H a)) → isEquiv _ _ p
      to   equivQ a = equivPreservesNType {n = ⟨-2⟩} (inverseEquiv (_ , equivQ a)) (equivg (f a))

      from : isEquiv _ _ p → (∀ a → isEquiv _ _ (Q H a))
      from equivp a = contrEquiv (equivp a) (equivg (f a))

    preserves-isEquiv₁ : isPullBack c ≃ isEquiv _ _ p
    preserves-isEquiv₁ =   isPullBack c
                         ≃⟨ lem7-6-8 ⟩
                           (∀ a → isEquiv _ _ (Q H a))
                         ≃⟨ to , lem3-3-3 (piPresNType ⟨-1⟩ λ a → propIsEquiv (Q H a)) (propIsEquiv p) to from ⟩
                           isEquiv _ _ p □

module _ {ℓ} {A B D C C' : Set ℓ} (f : A → D) (g : B → D) (C≃C' : C ≃ C') where
  open PB.Cone f g

  private
    c : C → C'
    c = C≃C' .fst

    c⁻¹ : C' → C
    c⁻¹ = inverse C≃C'

    to : C -cone → C' -cone
    to (cone p q H) = cone (p ∘ c⁻¹) (q ∘ c⁻¹) (right-whisker c⁻¹ H)

    from : C' -cone → C -cone
    from (cone p q H) = cone (p ∘ c) (q ∘ c) (right-whisker c H)

    tofrom∼id : ∀ c → to (from c) ≡ c
    tofrom∼id (cone p q H) i = cone (λ c'   → p (inverse-section (C≃C' .snd) c' i))
                                    (λ c'   → q (inverse-section (C≃C' .snd) c' i))
                                    (λ c' j → H (inverse-section (C≃C' .snd) c' i) j)

    fromto∼id : ∀ c → from (to c) ≡ c
    fromto∼id (cone p q H) i = cone (λ c   → p (inverse-retraction (C≃C' .snd) c i))
                                    (λ c   → q (inverse-retraction (C≃C' .snd) c i))
                                    (λ c j → H (inverse-retraction (C≃C' .snd) c i) j)

  cone-preserves-≃ : C -cone ≃ C' -cone
  cone-preserves-≃ = to , gradLemma _ from tofrom∼id fromto∼id

module _ {A B C D : Set ℓ} {f : A → D} {g : B → D} (let open PB.Cone f g) (c : C -cone) (equivf : isEquiv _ _ f) where
  open _-cone c

  private
    c' = cone-comm .fst c

  preserves-isEquiv₂ : isPullBack c ≃ isEquiv _ _ p₂
  preserves-isEquiv₂ =   isPullBack c
                       ≃⟨ isPullBack-comm c ⟩
                         isPullBack c'
                       ≃⟨ preserves-isEquiv₁ c' equivf ⟩
                         isEquiv _ _ p₂ □

-- Exercise 2.12
module _ {A B C D B' D' : Set ℓ}
         (f : A → D) (g : B → D) (p : C → A) (q : C → B)
         (f' : D → D') (q' : B → B') (g' : B' → D')
         (H : Homotopy (f ∘ p) (g ∘ q))
         (H' : Homotopy (f' ∘ g) (g' ∘ q'))
         (let open PB.Cone)
         (let left  = cone {f = f}  {g = g}  p q  H)
         (let right = cone {f = f'} {g = g'} g q' H')
         (pbr : isPullBack right) where
  private
    H'∘H : Homotopy (f' ∘ f ∘ p) (g' ∘ q' ∘ q)
    H'∘H = λ c → cong f' (H c) ◾ H' (q c)

    left∘right : _-cone (f' ∘ f) g' C
    left∘right = cone p (q' ∘ q) H'∘H

    Q-functorial : ∀ a → Homotopy (Q H'∘H a) (Q {f = f'} {g = g'} H' (f a) ∘ Q {f = f} H a)
    Q-functorial a (c , a≡pc) i = q' (q c) , h i
      where
        h : cong (f' ∘ f) a≡pc ◾ (cong f' (H c) ◾ H' (q c)) ≡ cong f' (cong f a≡pc ◾ H c) ◾ H' (q c)
        h =   cong (f' ∘ f) a≡pc ◾ (cong f' (H c) ◾ H' (q c))
            ≡⟨ trans-assoc ⟩
              cong (f' ∘ f) a≡pc ◾ cong f' (H c) ◾ H' (q c)
            ≡⟨ cong (_◾ H' (q c)) (cong (_◾ cong f' (H c)) (cong-∘ f f' a≡pc)) ⟩
              cong f' (cong f a≡pc) ◾ cong f' (H c) ◾ H' (q c)
            ≡⟨ cong (_◾ H' (q c)) (trans-cong f' (cong f a≡pc) _ (H c)) ⟩
              cong f' (cong f a≡pc ◾ H c) ◾ H' (q c) ∎

  paste : isPullBack left ≃ isPullBack left∘right
  paste =   isPullBack left
          ≃⟨ lem7-6-8 left ⟩
            (∀ a → isEquiv (fiber p a) (fiber g (f a)) (Q H a))
          ≃⟨ ex2-17-iii-Π-r (λ a → compEquiv-r _ _ (lem7-6-8 right .fst pbr (f a))) ⟩
            (∀ a → isEquiv (fiber p a) (fiber g' (f' (f a))) (Q {f = f'} {g = g'} H' (f a) ∘ Q {f = f} H a))
          ≃⟨ ex2-17-iii-Π-r (λ a → ∼-preserves-isEquiv (hinv (Q-functorial a))) ⟩
            (∀ a → isEquiv (fiber p a) (fiber g' (f' (f a))) (Q H'∘H a))
          ≃⟨ inverseEquiv (lem7-6-8 left∘right) ⟩
            isPullBack left∘right □

module _ {A B : Set ℓ} where
  open PB.Cone (⊤-intro {A = A}) (⊤-intro {A = B})

  private
    c : (A × B) -cone
    c = cone fst snd hid

    from : PullBack (⊤-intro {A = A}) (⊤-intro {A = B}) → A × B
    from (a , b , _) = a , b

  ×-pullback : Σ ((A × B) -cone) λ c → isPullBack c
  ×-pullback = c , inverse (unique c) λ x → (from x , refl) , λ { (y , x≡y) i → from (x≡y i) , λ j → x≡y (i ∧ j) }
