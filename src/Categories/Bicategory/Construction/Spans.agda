{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Diagram.Pullback

module Categories.Bicategory.Construction.Spans {o ℓ e} (𝒞 : Category o ℓ e) (has-pullbacks : ∀ {X Y Z} (f : 𝒞 [ X , Z ]) (g : 𝒞 [ Y , Z ]) → Pullback 𝒞 f g) where

open import Level
open import Function using (_$_)

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)

open import Categories.Bicategory
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym)

open import Categories.Category.Construction.Spans 𝒞 renaming (Spans to Spans₁)

open import Categories.Morphism
open import Categories.Morphism.Reasoning 𝒞

private
  module Spans₁ X Y = Category (Spans₁ X Y)

open Category 𝒞
open HomReasoning
open Equiv

open Span
open Span⇒
open Pullback

private
  variable
    A B C D E : Obj

--------------------------------------------------------------------------------
-- Various Spans, Span Maps, and their compositions

id-span : Span A A
id-span {A} = record
  { M = A
  ; dom = id
  ; cod = id
  }

_⊚₀_ : Span B C → Span A B → Span A C
f ⊚₀ g =
  let pullback = has-pullbacks (cod g) (dom f)
  in record
      { M = P pullback
      ; dom = dom g ∘ p₁ pullback
      ; cod = cod f ∘ p₂ pullback
      }

_⊚₁_ : {f f′ : Span B C} {g g′ : Span A B} → Span⇒ f f′ → Span⇒ g g′ → Span⇒ (f ⊚₀ g) (f′ ⊚₀ g′)
_⊚₁_  {_} {_} {_} {f} {f′} {g} {g′} α β =
  let pullback = has-pullbacks (cod g) (dom f)
      pullback′ = has-pullbacks (cod g′) (dom f′)
  in record
    { arr = universal pullback′ {h₁ = arr β ∘ p₁ pullback} {h₂ = arr α ∘ p₂ pullback} $ begin
      cod g′ ∘ arr β ∘ p₁ pullback ≈⟨ pullˡ (commute-cod β) ⟩
      cod g ∘ p₁ pullback          ≈⟨ commute pullback ⟩
      dom f ∘ p₂ pullback          ≈⟨ pushˡ (⟺ (commute-dom α)) ⟩
      dom f′ ∘ arr α ∘ p₂ pullback ∎
    ; commute-dom = begin
      (dom g′ ∘ p₁ pullback′) ∘ universal pullback′ _ ≈⟨ pullʳ (p₁∘universal≈h₁ pullback′) ⟩
      dom g′ ∘ arr β ∘ p₁ pullback                    ≈⟨ pullˡ (commute-dom β) ⟩
      dom g ∘ p₁ pullback                             ∎
    ; commute-cod = begin
      (cod f′ ∘ p₂ pullback′) ∘ universal pullback′ _ ≈⟨ pullʳ (p₂∘universal≈h₂ pullback′) ⟩
      cod f′ ∘ arr α ∘ p₂ pullback                    ≈⟨ pullˡ (commute-cod α) ⟩
      cod f ∘ p₂ pullback                             ∎
    }

--------------------------------------------------------------------------------
-- Proofs about span compositions

⊚₁-homomorphism : {f f′ f″ : Span B C} {g g′ g″ : Span A B}
                  → (α : Span⇒ f f′) → (α′ : Span⇒ f′ f″)
                  → (β : Span⇒ g g′) → (β′ : Span⇒ g′ g″)
                  → Spans₁ A C [ (Spans₁ B C [ α′ ∘ α ]) ⊚₁ (Spans₁ A B [ β′ ∘ β ]) ≈ Spans₁ A C [ α′ ⊚₁ β′ ∘ α ⊚₁ β ] ]
⊚₁-homomorphism {A} {B} {C} {f} {f′} {f″} {g} {g′} {g″} α α′ β β′ =
  let pullback = has-pullbacks (cod g) (dom f)
      pullback′ = has-pullbacks (cod g′) (dom f′)
      pullback″ = has-pullbacks (cod g″) (dom f″)
      α-chase = begin
        p₂ pullback″ ∘ universal pullback″ _ ∘ universal pullback′ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback″) ⟩
        (arr α′ ∘ p₂ pullback′) ∘ universal pullback′ _ ≈⟨ extendˡ (p₂∘universal≈h₂ pullback′) ⟩
        (arr α′ ∘ arr α) ∘ p₂ pullback ∎
      β-chase = begin
        p₁ pullback″ ∘ universal pullback″ _ ∘ universal pullback′ _            ≈⟨ pullˡ (p₁∘universal≈h₁ pullback″) ⟩
        (arr β′ ∘ p₁ (has-pullbacks (cod g′) (dom f′))) ∘ universal pullback′ _ ≈⟨ extendˡ (p₁∘universal≈h₁ pullback′) ⟩
        (arr β′ ∘ arr β) ∘ p₁ pullback                                          ∎
  in ⟺ (unique (has-pullbacks (cod g″) (dom f″)) β-chase α-chase)

--------------------------------------------------------------------------------
-- Associators

module _ (f : Span C D) (g : Span B C) (h : Span A B) where
  private
    pullback-fg = has-pullbacks (cod g) (dom f)
    pullback-gh = has-pullbacks (cod h) (dom g)
    pullback-⟨fg⟩h = has-pullbacks (cod h) (dom g ∘ p₁ pullback-fg)
    pullback-f⟨gh⟩ = has-pullbacks (cod g ∘ p₂ pullback-gh) (dom f)

  ⊚-assoc : Span⇒ ((f ⊚₀ g) ⊚₀ h) (f ⊚₀ (g ⊚₀ h))
  ⊚-assoc = record
    { arr = universal pullback-f⟨gh⟩ {h₁ = universal pullback-gh (commute pullback-⟨fg⟩h ○ assoc)} $ begin
        (cod g ∘ p₂ pullback-gh) ∘ universal pullback-gh _ ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-gh) ⟩
        cod g ∘ p₁ pullback-fg ∘ p₂ pullback-⟨fg⟩h         ≈⟨ extendʳ (commute pullback-fg) ⟩
        dom f ∘ p₂ pullback-fg ∘ p₂ pullback-⟨fg⟩h         ∎
    ; commute-dom = begin
        ((dom h ∘ p₁ pullback-gh) ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
        (dom h ∘ p₁ pullback-gh) ∘ universal pullback-gh _                          ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-gh) ⟩
        dom h ∘ p₁ pullback-⟨fg⟩h                                                   ∎
    ; commute-cod = begin
        (cod f ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ≈⟨ extendˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        (cod f ∘ p₂ pullback-fg) ∘ p₂ pullback-⟨fg⟩h             ∎
    }

  ⊚-assoc⁻¹ :  Span⇒ (f ⊚₀ (g ⊚₀ h)) ((f ⊚₀ g) ⊚₀ h)
  ⊚-assoc⁻¹ = record
    { arr = universal pullback-⟨fg⟩h {h₁ = p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩} {h₂ = universal pullback-fg (⟺ assoc ○ commute pullback-f⟨gh⟩)} $ begin
        cod h ∘ p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩         ≈⟨ extendʳ (commute pullback-gh) ⟩
        dom g ∘ p₂ pullback-gh ∘ p₁ pullback-f⟨gh⟩         ≈⟨ pushʳ (⟺ (p₁∘universal≈h₁ pullback-fg)) ⟩
        (dom g ∘ p₁ pullback-fg) ∘ universal pullback-fg _ ∎
      ; commute-dom = begin
        (dom h ∘ p₁ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _ ≈⟨ extendˡ (p₁∘universal≈h₁ pullback-⟨fg⟩h) ⟩
        (dom h ∘ p₁ pullback-gh) ∘ p₁ pullback-f⟨gh⟩             ∎
    ; commute-cod = begin
        ((cod f ∘ p₂ pullback-fg) ∘ p₂ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
        (cod f ∘ p₂ pullback-fg) ∘ universal pullback-fg _                          ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-fg) ⟩
        cod f ∘ p₂ pullback-f⟨gh⟩                                                   ∎
    }

  ⊚-assoc-iso : Iso (Spans₁ A D) ⊚-assoc ⊚-assoc⁻¹
  ⊚-assoc-iso = record
    { isoˡ =
      let lemmaˡ = begin
            p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-⟨fg⟩h) ⟩
            (p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _           ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
            p₁ pullback-gh ∘ universal pullback-gh _                                    ≈⟨ p₁∘universal≈h₁ pullback-gh ⟩
            p₁ pullback-⟨fg⟩h                                                           ∎
          lemmaʳ = begin
            p₂ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
            universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _                        ≈⟨ unique-diagram pullback-fg ((pullˡ (p₁∘universal≈h₁ pullback-fg) ○ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ○ p₂∘universal≈h₂ pullback-gh)) ((pullˡ (p₂∘universal≈h₂ pullback-fg) ○ p₂∘universal≈h₂ pullback-f⟨gh⟩)) ⟩
            p₂ pullback-⟨fg⟩h                                                           ∎
      in unique pullback-⟨fg⟩h lemmaˡ lemmaʳ ○ ⟺ (Pullback.id-unique pullback-⟨fg⟩h)
    ; isoʳ =
      let lemmaˡ = begin
            p₁ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
            universal pullback-gh _ ∘ universal pullback-⟨fg⟩h _                        ≈⟨ unique-diagram pullback-gh (pullˡ (p₁∘universal≈h₁ pullback-gh) ○ p₁∘universal≈h₁ pullback-⟨fg⟩h) (pullˡ (p₂∘universal≈h₂ pullback-gh) ○ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ○ p₁∘universal≈h₁ pullback-fg) ⟩
            p₁ pullback-f⟨gh⟩                                                           ∎
          lemmaʳ = begin
            p₂ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
            (p₂ pullback-fg ∘ p₂ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _           ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
            p₂ pullback-fg ∘ universal pullback-fg _                                    ≈⟨ p₂∘universal≈h₂ pullback-fg ⟩
            p₂ pullback-f⟨gh⟩                                                           ∎
      in unique pullback-f⟨gh⟩ lemmaˡ lemmaʳ ○ ⟺ (Pullback.id-unique pullback-f⟨gh⟩)
    }

⊚-assoc-commute : ∀ {f f′ : Span C D} {g g′ : Span B C} {h h′ : Span A B} → (α : Span⇒ f f′) → (β : Span⇒ g g′) → (γ : Span⇒ h h′)
            → Spans₁ A D [ Spans₁ A D [ ⊚-assoc f′ g′ h′ ∘ (α ⊚₁ β) ⊚₁ γ ] ≈ Spans₁ A D [ α ⊚₁ (β ⊚₁ γ) ∘ ⊚-assoc f g h ] ]
⊚-assoc-commute {f = f} {f′ = f′} {g = g} {g′ = g′} {h = h} {h′ = h′} α β γ =
  let pullback-fg     = has-pullbacks (cod g) (dom f)
      pullback-fg′    = has-pullbacks (cod g′) (dom f′)
      pullback-gh     = has-pullbacks (cod h) (dom g)
      pullback-gh′    = has-pullbacks (cod h′) (dom g′)
      pullback-f⟨gh⟩  = has-pullbacks (cod g ∘ p₂ pullback-gh) (dom f)
      pullback-f⟨gh⟩′ = has-pullbacks (cod g′ ∘ p₂ pullback-gh′) (dom f′)
      pullback-⟨fg⟩h  = has-pullbacks (cod h) (dom g ∘ p₁ pullback-fg)
      pullback-⟨fg⟩h′ = has-pullbacks (cod h′) (dom g′ ∘ p₁ pullback-fg′)

      eq = begin
        cod h′ ∘ arr γ ∘ p₁ pullback-⟨fg⟩h                      ≈⟨ pullˡ (commute-cod γ) ⟩
        cod h ∘ p₁ pullback-⟨fg⟩h                               ≈⟨ commute pullback-⟨fg⟩h ⟩
        (dom g ∘ p₁ pullback-fg) ∘ p₂ pullback-⟨fg⟩h            ≈˘⟨ commute-dom β ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((dom g′ ∘ arr β) ∘ p₁ pullback-fg) ∘ p₂ pullback-⟨fg⟩h ≈⟨ assoc² ⟩
        dom g′ ∘ arr β ∘ p₁ pullback-fg ∘ p₂ pullback-⟨fg⟩h     ∎

      -- NOTE: This could probably be a standalone pullback lemma
      lemmaˡ = begin
        p₁ pullback-f⟨gh⟩′ ∘ universal pullback-f⟨gh⟩′ _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩′) ⟩
        (universal pullback-gh′ _ ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _   ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
        -- FIXME: Use unique-diagram
        universal pullback-gh′ _ ∘ universal pullback-gh _                            ≈⟨ unique pullback-gh′ (pullˡ (p₁∘universal≈h₁ pullback-gh′) ○ pullʳ (p₁∘universal≈h₁ pullback-gh)) (pullˡ (p₂∘universal≈h₂ pullback-gh′) ○ pullʳ (p₂∘universal≈h₂ pullback-gh)) ⟩
        universal pullback-gh′ eq                                                     ≈˘⟨ unique pullback-gh′ (pullˡ (p₁∘universal≈h₁ pullback-gh′) ○ p₁∘universal≈h₁ pullback-⟨fg⟩h′) (pullˡ (p₂∘universal≈h₂ pullback-gh′) ○ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h′) ○ extendʳ (p₁∘universal≈h₁ pullback-fg′)) ⟩
        universal pullback-gh′ _ ∘ universal pullback-⟨fg⟩h′ _                        ∎

      lemmaʳ = begin
        p₂ pullback-f⟨gh⟩′ ∘ universal pullback-f⟨gh⟩′ _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩′) ⟩
        (arr α ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _                      ≈⟨ extendˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        (arr α ∘ p₂ pullback-fg) ∘ p₂ pullback-⟨fg⟩h                                  ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-fg′)) ⟩
        p₂ pullback-fg′ ∘ universal pullback-fg′ _ ∘ p₂ pullback-⟨fg⟩h                ≈⟨ pushʳ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩h′)) ⟩
        (p₂ pullback-fg′ ∘ p₂ pullback-⟨fg⟩h′) ∘ universal pullback-⟨fg⟩h′ _ ∎

      eq′ = begin
        (cod g′ ∘ p₂ pullback-gh′) ∘ universal pullback-gh′ _ ∘ universal pullback-⟨fg⟩h′ _ ≈⟨ center (p₂∘universal≈h₂ pullback-gh′) ⟩
        cod g′ ∘ (p₁ pullback-fg′ ∘ p₂ pullback-⟨fg⟩h′) ∘ universal pullback-⟨fg⟩h′ _       ≈⟨ center⁻¹ (commute (pullback-fg′)) refl ⟩
        (dom f′ ∘ p₂ pullback-fg′) ∘ (p₂ pullback-⟨fg⟩h′ ∘ universal pullback-⟨fg⟩h′ _)     ≈⟨ center refl ⟩
        dom f′ ∘ (p₂ pullback-fg′ ∘ p₂ pullback-⟨fg⟩h′) ∘ universal pullback-⟨fg⟩h′ _ ∎

  in begin
    universal pullback-f⟨gh⟩′ _ ∘ universal pullback-⟨fg⟩h′ _ ≈⟨ unique pullback-f⟨gh⟩′ (pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩′)) (pullˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩′)) ⟩
    universal pullback-f⟨gh⟩′ eq′                             ≈˘⟨ unique pullback-f⟨gh⟩′ lemmaˡ lemmaʳ ⟩
    universal pullback-f⟨gh⟩′ _ ∘ universal pullback-f⟨gh⟩ _ ∎


--------------------------------------------------------------------------------
-- Unitors

module _ (f : Span A B) where
  private
    pullback-dom-f = has-pullbacks id (dom f)
    pullback-cod-f = has-pullbacks (cod f) id

  ⊚-unitˡ : Span⇒ (id-span ⊚₀ f) f
  ⊚-unitˡ = record
    { arr = p₁ pullback-cod-f
    ; commute-dom = refl
    ; commute-cod = commute pullback-cod-f
    }

  ⊚-unitˡ⁻¹ : Span⇒ f (id-span ⊚₀ f)
  ⊚-unitˡ⁻¹ = record
    { arr = universal pullback-cod-f id-comm
    ; commute-dom = cancelʳ (p₁∘universal≈h₁ pullback-cod-f)
    ; commute-cod = pullʳ (p₂∘universal≈h₂ pullback-cod-f) ○ identityˡ
    }

  ⊚-unitˡ-iso : Iso (Spans₁ A B) ⊚-unitˡ ⊚-unitˡ⁻¹
  ⊚-unitˡ-iso = record
    { isoˡ = unique-diagram pullback-cod-f (pullˡ (p₁∘universal≈h₁ pullback-cod-f) ○ id-comm-sym) (pullˡ (p₂∘universal≈h₂ pullback-cod-f) ○ commute pullback-cod-f ○ id-comm-sym)
    ; isoʳ = p₁∘universal≈h₁ pullback-cod-f
    }

  ⊚-unitʳ : Span⇒ (f ⊚₀ id-span) f
  ⊚-unitʳ = record
    { arr = p₂ pullback-dom-f
    ; commute-dom = ⟺ (commute pullback-dom-f)
    ; commute-cod = refl
    }

  ⊚-unitʳ⁻¹ : Span⇒ f (f ⊚₀ id-span)
  ⊚-unitʳ⁻¹ = record
    { arr = universal pullback-dom-f id-comm-sym
    ; commute-dom = pullʳ (p₁∘universal≈h₁ pullback-dom-f) ○ identityˡ
    ; commute-cod = pullʳ (p₂∘universal≈h₂ pullback-dom-f) ○ identityʳ
    }

  ⊚-unitʳ-iso : Iso (Spans₁ A B) ⊚-unitʳ ⊚-unitʳ⁻¹
  ⊚-unitʳ-iso = record
    { isoˡ = unique-diagram pullback-dom-f (pullˡ (p₁∘universal≈h₁ pullback-dom-f) ○ ⟺ (commute pullback-dom-f) ○ id-comm-sym) (pullˡ (p₂∘universal≈h₂ pullback-dom-f) ○ id-comm-sym)
    ; isoʳ = p₂∘universal≈h₂ pullback-dom-f
    }

⊚-unitˡ-commute : ∀ {f f′ : Span A B} → (α : Span⇒ f f′) → Spans₁ A B [ Spans₁ A B [ ⊚-unitˡ f′ ∘ Spans₁.id B B ⊚₁ α ] ≈ Spans₁ A B [ α ∘ ⊚-unitˡ f ] ]
⊚-unitˡ-commute {f′ = f′} α = p₁∘universal≈h₁ (has-pullbacks (cod f′) id)

⊚-unitʳ-commute : ∀ {f f′ : Span A B} → (α : Span⇒ f f′) → Spans₁ A B [ Spans₁ A B [ ⊚-unitʳ f′ ∘ α ⊚₁ Spans₁.id A A ] ≈ Spans₁ A B [ α ∘ ⊚-unitʳ f ] ]
⊚-unitʳ-commute {f′ = f′} α = p₂∘universal≈h₂ (has-pullbacks id (dom f′))

--------------------------------------------------------------------------------
-- Interactions between associators and unitors

triangle : (f : Span A B) → (g : Span B C) → Spans₁ A C [ Spans₁ A C [ Spans₁.id B C {g} ⊚₁ ⊚-unitˡ f ∘ ⊚-assoc g id-span f ] ≈ ⊚-unitʳ g ⊚₁ Spans₁.id A B {f} ]
triangle f g =
  let pullback-dom-g = has-pullbacks id (dom g)
      pullback-cod-f = has-pullbacks (cod f) id
      pullback-fg    = has-pullbacks (cod f) (dom g)
      pullback-id-fg = has-pullbacks (id ∘ p₂ pullback-cod-f) (dom g)
      pullback-f-id-g = has-pullbacks (cod f) (id ∘ p₁ pullback-dom-g)
  in unique pullback-fg (pullˡ (p₁∘universal≈h₁ pullback-fg) ○ pullʳ (p₁∘universal≈h₁ pullback-id-fg) ○ p₁∘universal≈h₁ pullback-cod-f ○ ⟺ identityˡ)
                        (pullˡ (p₂∘universal≈h₂ pullback-fg) ○ pullʳ (p₂∘universal≈h₂ pullback-id-fg) ○ identityˡ)


pentagon : (f : Span A B) → (g : Span B C) → (h : Span C D) → (i : Span D E)
         →  Spans₁ A E [ Spans₁ A E [ (Spans₁.id D E {i}) ⊚₁ (⊚-assoc h g f) ∘ Spans₁ A E [ ⊚-assoc i (h ⊚₀ g) f ∘ ⊚-assoc i h g ⊚₁ Spans₁.id A B {f} ] ] ≈ Spans₁ A E [ ⊚-assoc i h (g ⊚₀ f) ∘ ⊚-assoc (i ⊚₀ h) g f ] ]
pentagon {A} {B} {C} {D} {E} f g h i =
  let pullback-fg       = has-pullbacks (cod f) (dom g)
      pullback-gh       = has-pullbacks (cod g) (dom h)
      pullback-hi       = has-pullbacks (cod h) (dom i)
      pullback-f⟨gh⟩    = has-pullbacks (cod f) (dom (h ⊚₀ g))
      pullback-⟨fg⟩h    = has-pullbacks (cod (g ⊚₀ f)) (dom h)
      pullback-⟨gh⟩i    = has-pullbacks (cod (h ⊚₀ g)) (dom i)
      pullback-g⟨hi⟩    = has-pullbacks (cod g) (dom (i ⊚₀ h))
      pullback-⟨⟨fg⟩h⟩i = has-pullbacks (cod (h ⊚₀ (g ⊚₀ f))) (dom i)
      pullback-⟨f⟨gh⟩⟩i = has-pullbacks (cod ((h ⊚₀ g) ⊚₀ f)) (dom i)
      pullback-⟨fg⟩⟨hi⟩ = has-pullbacks (cod (g ⊚₀ f)) (dom (i ⊚₀ h))
      pullback-f⟨⟨gh⟩i⟩ = has-pullbacks (cod f) (dom (i ⊚₀ (h ⊚₀ g)))
      pullback-f⟨g⟨hi⟩⟩ = has-pullbacks (cod f) (dom ((i ⊚₀ h) ⊚₀ g))

      lemma-fgˡ = begin
        p₁ pullback-fg ∘ universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-fg) ⟩
        p₁ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                        ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
        p₁ pullback-f⟨⟨gh⟩i⟩ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                                                  ≈⟨ p₁∘universal≈h₁ pullback-f⟨⟨gh⟩i⟩ ⟩
        id ∘ p₁ pullback-f⟨g⟨hi⟩⟩                                                                             ≈⟨ identityˡ ⟩
        p₁ pullback-f⟨g⟨hi⟩⟩                                                                                  ≈˘⟨ p₁∘universal≈h₁ pullback-fg ⟩
        p₁ pullback-fg ∘ universal pullback-fg _                                                              ∎

      lemma-fgʳ = begin
        p₂ pullback-fg ∘ universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-fg) ⟩
        (p₁ pullback-gh ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _     ≈⟨ center (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        p₁ pullback-gh ∘ (p₁ pullback-⟨gh⟩i ∘ p₂ pullback-f⟨⟨gh⟩i⟩) ∘ universal pullback-f⟨⟨gh⟩i⟩ _           ≈⟨ center⁻¹ refl (p₂∘universal≈h₂ pullback-f⟨⟨gh⟩i⟩) ⟩
        (p₁ pullback-gh ∘ p₁ pullback-⟨gh⟩i) ∘ universal pullback-⟨gh⟩i _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩              ≈⟨ center (p₁∘universal≈h₁ pullback-⟨gh⟩i) ⟩ 
        p₁ pullback-gh ∘ universal pullback-gh _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                       ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-gh) ⟩
        p₁ pullback-g⟨hi⟩ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                              ≈˘⟨ p₂∘universal≈h₂ pullback-fg ⟩
        p₂ pullback-fg ∘ universal pullback-fg _                                                              ∎

      lemma-⟨fg⟩hˡ = begin
        p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-⟨fg⟩h) ⟩
        universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                        ≈⟨ unique-diagram pullback-fg lemma-fgˡ lemma-fgʳ ⟩
        universal pullback-fg _                                                                                     ≈˘⟨ p₁∘universal≈h₁ pullback-⟨fg⟩⟨hi⟩ ⟩
        p₁ pullback-⟨fg⟩⟨hi⟩ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                                        ≈⟨ pushˡ (⟺ (p₁∘universal≈h₁ pullback-⟨fg⟩h)) ⟩
        p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                              ∎

      lemma-⟨fg⟩hʳ = begin
        p₂ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
        (p₂ pullback-gh ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _           ≈⟨ center (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        p₂ pullback-gh ∘ (p₁ pullback-⟨gh⟩i ∘ p₂ pullback-f⟨⟨gh⟩i⟩) ∘ universal pullback-f⟨⟨gh⟩i⟩ _                 ≈⟨ center⁻¹ refl (p₂∘universal≈h₂ pullback-f⟨⟨gh⟩i⟩) ⟩
        (p₂ pullback-gh ∘ p₁ pullback-⟨gh⟩i) ∘ universal pullback-⟨gh⟩i _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                    ≈⟨ center (p₁∘universal≈h₁ pullback-⟨gh⟩i) ⟩
        p₂ pullback-gh ∘ universal pullback-gh _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                             ≈⟨ extendʳ (p₂∘universal≈h₂ pullback-gh) ⟩
        p₁ pullback-hi ∘ p₂ pullback-g⟨hi⟩ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                   ≈⟨ pushʳ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩⟨hi⟩)) ⟩
        (p₁ pullback-hi ∘ p₂ pullback-⟨fg⟩⟨hi⟩) ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                     ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩h)) ⟩
        p₂ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                              ∎

      lemmaˡ = begin
        p₁ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-⟨⟨fg⟩h⟩i) ⟩
        (universal pullback-⟨fg⟩h _ ∘ p₁ pullback-⟨f⟨gh⟩⟩i) ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _  ≈⟨ center (p₁∘universal≈h₁ pullback-⟨f⟨gh⟩⟩i) ⟩
        universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                              ≈⟨ unique-diagram pullback-⟨fg⟩h lemma-⟨fg⟩hˡ lemma-⟨fg⟩hʳ ⟩
        universal pullback-⟨fg⟩h _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                                           ≈⟨ pushˡ (⟺ (p₁∘universal≈h₁ pullback-⟨⟨fg⟩h⟩i)) ⟩
        p₁ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                 ∎

      lemmaʳ = begin
        p₂ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨⟨fg⟩h⟩i) ⟩
        (id ∘ p₂ pullback-⟨f⟨gh⟩⟩i) ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                          ≈⟨ center (p₂∘universal≈h₂ pullback-⟨f⟨gh⟩⟩i) ⟩
        id ∘ (p₂ pullback-⟨gh⟩i ∘ p₂ pullback-f⟨⟨gh⟩i⟩) ∘ universal pullback-f⟨⟨gh⟩i⟩ _                                      ≈⟨ center⁻¹ identityˡ (p₂∘universal≈h₂ pullback-f⟨⟨gh⟩i⟩) ⟩
        p₂ pullback-⟨gh⟩i ∘ universal pullback-⟨gh⟩i _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨gh⟩i) ⟩
        (p₂ pullback-hi ∘ p₂ pullback-g⟨hi⟩) ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                          ≈⟨ extendˡ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩⟨hi⟩)) ⟩
        (p₂ pullback-hi ∘ p₂ pullback-⟨fg⟩⟨hi⟩) ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                              ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-⟨⟨fg⟩h⟩i)) ⟩
        p₂ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                 ∎

  in unique-diagram pullback-⟨⟨fg⟩h⟩i lemmaˡ lemmaʳ

Spans : Bicategory (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e o
Spans = record
  { enriched = record
    { Obj = Obj
    ; hom = Spans₁
    ; id = λ {A} → record
      { F₀ = λ _ → id-span
      ; F₁ = λ _ → Spans₁.id A A
      ; identity = refl
      ; homomorphism = ⟺ identity²
      ; F-resp-≈ = λ _ → refl
      }
    ; ⊚ = record
      { F₀ = λ (f , g) → f ⊚₀ g
      ; F₁ = λ (α , β) → α ⊚₁ β
      ; identity = λ {(f , g)} → ⟺ (unique (has-pullbacks (cod g) (dom f)) id-comm id-comm)
      ; homomorphism = λ {X} {Y} {Z} {(α , α′)} {(β , β′)} → ⊚₁-homomorphism α β α′ β′
      ; F-resp-≈ = λ {(f , g)} {(f′ , g′)} {_} {_} (α-eq , β-eq) → universal-resp-≈ (has-pullbacks (cod g′) (dom f′)) (∘-resp-≈ˡ β-eq) (∘-resp-≈ˡ α-eq)
      }
    ; ⊚-assoc = niHelper record
      { η = λ ((f , g) , h) → ⊚-assoc f g h
      ; η⁻¹ = λ ((f , g) , h) → ⊚-assoc⁻¹ f g h
      ; commute = λ ((α , β) , γ) → ⊚-assoc-commute α β γ
      ; iso = λ ((f , g) , h) → ⊚-assoc-iso f g h
      }
    ; unitˡ = niHelper record
      { η = λ (_ , f) → ⊚-unitˡ f
      ; η⁻¹ = λ (_ , f) → ⊚-unitˡ⁻¹ f
      ; commute = λ (_ , α) → ⊚-unitˡ-commute α
      ; iso = λ (_ , f) → ⊚-unitˡ-iso f
      }
    ; unitʳ = niHelper record
      { η = λ (f , _) → ⊚-unitʳ f
      ; η⁻¹ = λ (f , _) → ⊚-unitʳ⁻¹ f
      ; commute = λ (α , _) → ⊚-unitʳ-commute α
      ; iso = λ (f , _) → ⊚-unitʳ-iso f
      }
    }
  ; triangle = λ {_} {_} {_} {f} {g} → triangle f g
  ; pentagon = λ {_} {_} {_} {_} {_} {f} {g} {h} {i} → pentagon f g h i
  }
