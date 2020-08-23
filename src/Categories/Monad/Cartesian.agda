{-# OPTIONS --without-K --safe #-}

module Categories.Monad.Cartesian where

open import Level
open import Categories.Category
open import Categories.Monad
open import Categories.Diagram.Pullback
open import Categories.Diagram.IsPullback
open import Categories.NaturalTransformation.Cartesian

-- See https://ncatlab.org/nlab/show/cartesian+monad.
-- NOTE: Should I require ℰ to be cartesian here?
record CartesianMonad {o ℓ e} {ℰ : Category o ℓ e} (T : Monad ℰ) : Set (o ⊔ ℓ ⊔ e) where
  private
    module T = Monad T
    open T.F renaming (F₀ to T₀; F₁ to T₁; F-resp-≈ to T-resp-≈)
  field
    has-pullbacks : ∀ {X Y Z} (f : ℰ [ X , Z ]) (g : ℰ [ Y , Z ]) → Pullback ℰ f g
    preserves-pullbacks : ∀ {P X Y Z} (p₁ : ℰ [ P , X ]) (p₂ : ℰ [ P , Y ]) (f : ℰ [ X , Z ]) (g : ℰ [ Y , Z ]) → IsPullback ℰ p₁ p₂ f g → IsPullback ℰ (T₁ p₁) (T₁ p₂) (T₁ f) (T₁ g)
    cartesian-η : CartesianNaturalTransformation T.η
    cartesian-μ : CartesianNaturalTransformation T.μ
