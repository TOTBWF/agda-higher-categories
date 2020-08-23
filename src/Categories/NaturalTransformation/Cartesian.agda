{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.Cartesian where

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Diagram.IsPullback

-- See https://ncatlab.org/nlab/show/equifibered+natural+transformation
CartesianNaturalTransformation : ∀ {o ℓ e o′ ℓ′ e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′} {F G : Functor 𝒞 𝒟} (α : NaturalTransformation F G) → Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′)
CartesianNaturalTransformation {𝒞 = 𝒞} {𝒟 = 𝒟} {F = F} {G = G} α = ∀ {X Y} → (f : 𝒞 [ X , Y ]) → IsPullback 𝒟 (F.F₁ f) (α.η X) (α.η Y) (G.F₁ f)
  where
    module F = Functor F
    module G = Functor G
    module α = NaturalTransformation α
