{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core using (Category)

-- 'agda-categories' doesn't really have a great way about talking about _specific_
-- pullback squares, which we need for the definition of a Cartesian Monad.
-- To work around this, let's just hack together a quick module that defines a predicate
-- version of 'Pullback'
module Categories.Diagram.IsPullback {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open Equiv

open import Level
open import Categories.Diagram.Pullback 𝒞
open import Categories.Morphism.Reasoning 𝒞 as Square
  renaming (glue to glue-square) hiding (id-unique)

private
  variable
    A B X Y Z : Obj
    f g h h₁ h₂ i i₁ i₂ j k : A ⇒ B

record IsPullback {P : Obj} (p₁ : P ⇒ X) (p₂ : P ⇒ Y) (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    commute   : f ∘ p₁ ≈ g ∘ p₂
    universal : ∀ {h₁ : A ⇒ X} {h₂ : A ⇒ Y} → f ∘ h₁ ≈ g ∘ h₂ → A ⇒ P
    unique    : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                  p₁ ∘ i ≈ h₁ → p₂ ∘ i ≈ h₂ →
                  i ≈ universal eq

    p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                         p₁ ∘ universal eq ≈ h₁
    p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                         p₂ ∘ universal eq ≈ h₂

  unique′ : (eq eq′ : f ∘ h₁ ≈ g ∘ h₂) → universal eq ≈ universal eq′
  unique′ eq eq′ = unique p₁∘universal≈h₁ p₂∘universal≈h₂

  id-unique : id ≈ universal commute
  id-unique = unique identityʳ identityʳ

  universal-resp-≈ : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} {eq′ : f ∘ i₁ ≈ g ∘ i₂} → h₁ ≈ i₁ → h₂ ≈ i₂ → universal eq ≈ universal eq′
  universal-resp-≈ h₁≈i₁ h₂≈i₂ = unique (p₁∘universal≈h₁ ○ h₁≈i₁) (p₂∘universal≈h₂ ○ h₂≈i₂)

  unique-diagram : p₁ ∘ h ≈ p₁ ∘ i →
                   p₂ ∘ h ≈ p₂ ∘ i →
                   h ≈ i
  unique-diagram {h = h} {i = i} eq₁ eq₂ = begin
    h            ≈⟨ unique eq₁ eq₂ ⟩
    universal eq ≈˘⟨ unique refl refl ⟩
    i            ∎
    where eq = extendʳ commute

IsPullback⇒Pullback : IsPullback h₁ h₂ f g → Pullback f g
IsPullback⇒Pullback {h₁ = h₁} {h₂ = h₂} {f = f} {g = g} is-pullback = record
  { p₁ = h₁
  ; p₂ = h₂
  ; commute = is-pullback.commute
  ; universal = is-pullback.universal
  ; unique = is-pullback.unique
  ; p₁∘universal≈h₁ = is-pullback.p₁∘universal≈h₁
  ; p₂∘universal≈h₂ = is-pullback.p₂∘universal≈h₂
  }
  where
    module is-pullback = IsPullback is-pullback

Pullback⇒IsPullback : (pullback : Pullback f g)  → IsPullback (Pullback.p₁ pullback) (Pullback.p₂ pullback) f g
Pullback⇒IsPullback pullback = record
  { commute = pullback.commute
  ; universal = pullback.universal
  ; unique = pullback.unique
  ; p₁∘universal≈h₁ = pullback.p₁∘universal≈h₁
  ; p₂∘universal≈h₂ = pullback.p₂∘universal≈h₂
  }
  where
    module pullback = Pullback pullback
