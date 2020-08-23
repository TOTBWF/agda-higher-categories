{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Monad

-- The 1-category of T-Spans, defined on page 108 of https://arxiv.org/abs/math/0305049
-- Also see https://ncatlab.org/nlab/show/multicategory
module Categories.Category.Construction.T-Spans {o ℓ e} {ℰ : Category o ℓ e} (T : Monad ℰ) where

open import Level
open import Categories.Morphism.Reasoning ℰ

private
  module ℰ = Category ℰ
  module T = Monad T

open ℰ
open HomReasoning
open Equiv
open T.F renaming (F₀ to T₀; F₁ to T₁; F-resp-≈ to T-resp-≈)

record T-Span (X Y : Obj) : Set (o ⊔ ℓ) where
  field
    M : Obj
    dom : M ⇒ T₀ X
    cod : M ⇒ Y

open T-Span

record T-Span⇒ {X Y : Obj} (f f′ : T-Span X Y) : Set (o ⊔ ℓ ⊔ e) where
  field
    arr : M f ⇒ M f′
    commute-dom : dom f′ ∘ arr ≈ dom f
    commute-cod : cod f′ ∘ arr ≈ cod f

open T-Span⇒

-- The 1-category with T-Spans as objects, and T-Span maps as morphisms
T-Spans : Obj → Obj → Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
T-Spans X Y = record
  { Obj = T-Span X Y
  ; _⇒_ = T-Span⇒
  ; _≈_ = λ f g → arr f ≈ arr g
  ; id = record
    { arr = id
    ; commute-dom = identityʳ
    ; commute-cod = identityʳ
    }
  ; _∘_ = λ {f g h} α β → record
    { arr = arr α ∘ arr β
    ; commute-dom = begin
      dom h ∘ arr α ∘ arr β ≈⟨ pullˡ (commute-dom α) ⟩
      dom g ∘ arr β ≈⟨ commute-dom β ⟩
      dom f ∎
    ; commute-cod = begin
      cod h ∘ arr α ∘ arr β ≈⟨ pullˡ (commute-cod α) ⟩
      cod g ∘ arr β ≈⟨ commute-cod β ⟩
      cod f ∎
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }
