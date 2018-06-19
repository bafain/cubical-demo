{-# OPTIONS --cubical #-}
module Cubical.Join.Properties where

open import Cubical.FromStdLib
open import Cubical.PathPrelude

open import Cubical.Flattening
open import Cubical.GradLemma
open import Cubical.Join
open import Cubical.PullBack using (PullBack)
import Cubical.PullBack as PB
open import Cubical.PushOut using (PushOut; isPushOut; lem682)
import Cubical.PushOut as PO
open import Cubical.PushOut.Properties using (unique; isPushOut-preserves-≃)

module _ {ℓ} (A B X : Set ℓ) (f : A → X) (g : B → X) where
  private
    fibf : ∀ x → fiber f x → ⊤ {ℓ}
    fibf x (a , x≡fa) = tt

    fibg : ∀ x → fiber g x → ⊤ {ℓ}
    fibg x (b , x≡gb) = tt

  thm22 : ∀ x → Join (fibf x) (fibg x) ≃ fiber (f ∗ g) x
  thm22 x = _ , unique .fst s
    where
      left-back-bot : Set ℓ
      left-back-bot = PullBack f g

      left-back-top : Set ℓ
      left-back-top = Σ left-back-bot λ { (a , b , fa≡gb) →
                      Σ (x ≡ f a) λ x≡fa →
                      Σ (x ≡ g b) λ x≡gb →
                      PathP (λ i → x ≡ (f ∗ g) (join fa≡gb i)) x≡fa x≡gb }

      right-front-top : Set ℓ
      right-front-top = fiber (f ∗ g) x

      left-back : left-back-top → left-back-bot
      left-back (x , _) = x

      front-top : fiber f x → fiber (f ∗ g) x
      front-top (a , x≡fa) = inl a , x≡fa

      i = front-top

      right-top : fiber g x → fiber (f ∗ g) x
      right-top (b , x≡gb) = inr b , x≡gb

      j = right-top

      left-top : left-back-top → fiber f x
      left-top ((a , _ , _) , x≡fa , _ , _) = a , x≡fa

      back-top : left-back-top → fiber g x
      back-top ((_ , b , _) , _ , x≡gb , _) = b , x≡gb

      h : Homotopy (front-top ∘ left-top) (right-top ∘ back-top)
      h ((_ , _ , fa≡gb) , x≡fa , x≡gb , x≡fa≡x≡gb) i = join fa≡gb i , x≡fa≡x≡gb i

      open PB.Canonical f g using () renaming (π₁ to left-bot; π₂ to back-bot)

      top : isPushOut (record { i = i ; j = j ; h = h } )
      top = flatteningLemma left-bot back-bot (λ y → x ≡ (f ∗ g) y)

      open PB.Canonical (fibf x) (fibg x)

      private
        refl≡fa≡gb : {a : A} {b : B} → (x≡fa : x ≡ f a) → (x≡gb : x ≡ g b) → PathP (λ i → x ≡ _) x≡fa x≡gb
        refl≡fa≡gb x≡fa x≡gb i j = fill (λ j → X)
                                        (i ∨ ~ i)
                                        (λ { j (i = i0) → x≡fa j
                                           ; j (i = i1) → x≡gb j
                                           })
                                        x
                                        j

        m : left-back-top → PullBack (fibf x) (fibg x)
        m ((a , b , _) , x≡fa , x≡gb , _) = (a , x≡fa) , (b , x≡gb) , refl

        m⁻¹ : PullBack (fibf x) (fibg x) → left-back-top
        m⁻¹ ((a , x≡fa) , (b , x≡gb) , _) = (a , b , λ i → refl≡fa≡gb x≡fa x≡gb i i1) , x≡fa , x≡gb , refl≡fa≡gb x≡fa x≡gb

        π₁≡left-top∘m⁻¹ : π₁ ≡ left-top ∘ m⁻¹
        π₁≡left-top∘m⁻¹ = refl

        π₂≡back-top∘m⁻¹ : π₂ ≡ back-top ∘ m⁻¹
        π₂≡back-top∘m⁻¹ = refl

        m⁻¹m∼id : Homotopy (m⁻¹ ∘ m) (idFun _)
        m⁻¹m∼id ((a , b , _) , x≡fa , x≡gb , α) i = (a , b , _)
                                                  , x≡fa
                                                  , x≡gb
                                                  , λ j k → primComp (λ _ → X)
                                                                     _
                                                                     (λ { l (k = i0) → x
                                                                        ; l (j = i0) → x≡fa (k ∧ l)
                                                                        ; l (j = i1) → x≡gb (k ∧ l)
                                                                        ; l (i = i1) → α j (k ∧ l)
                                                                        })
                                                                     x

        mm⁻¹∼id : Homotopy (m ∘ m⁻¹) (idFun _)
        mm⁻¹∼id _ = refl

      open PO.Cocone

      s : isPushOut (cocone i j (right-whisker m⁻¹ h))
      s = isPushOut-preserves-≃ (_ , gradLemma m⁻¹ m m⁻¹m∼id mm⁻¹∼id) (cocone i j h) .fst top
