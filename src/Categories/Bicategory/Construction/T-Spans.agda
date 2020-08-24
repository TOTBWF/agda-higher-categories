{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Monad
open import Categories.Monad.Cartesian

-- The bicategory of T-Spans, defined on page 108 of https://arxiv.org/abs/math/0305049
-- Also see https://ncatlab.org/nlab/show/multicategory
module Categories.Bicategory.Construction.T-Spans {o ℓ e} {ℰ : Category o ℓ e} {T : Monad ℰ} (T-cartesian : CartesianMonad T) where

open import Level
open import Function using (_$_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)
open import Categories.Category.Product
open import Categories.Bicategory
open import Categories.Functor renaming (id to idF)
open import Categories.Diagram.Pullback ℰ as Pullback
open import Categories.Diagram.IsPullback ℰ as IsPullback

open import Categories.Category.Construction.T-Spans T renaming (T-Spans to T-Spans₁)

open import Categories.Morphism ℰ
open import Categories.Morphism.Reasoning ℰ

private
  module ℰ = Category ℰ
  module T = Monad T

open ℰ
open HomReasoning
open Equiv
open T.F renaming (F₀ to T₀; F₁ to T₁; F-resp-≈ to T-resp-≈)
open T-Span
open T-Span⇒
open CartesianMonad T-cartesian

private
  variable
    X Y Z : Obj

T-Spans : Bicategory {!!} {!!} {!!} {!!}
T-Spans = record
  { enriched = record
    { Obj = Obj
    ; hom = T-Spans₁
    ; id = record
             { F₀ = λ _ → id-span
             ; F₁ = λ _ → id-span⇒
             ; identity = refl
             ; homomorphism = sym identity²
             ; F-resp-≈ = λ _ → refl
             }
    ; ⊚ = span-∘
    ; ⊚-assoc = {!!}
    ; unitˡ = {!!}
    ; unitʳ = {!!}
    }
  ; triangle = {!!}
  ; pentagon = {!!}
  }
  where
    id-span : ∀ {X : Obj} → T-Span X X
    id-span {X} = record
      { M = X
      ; dom = T.η.η X
      ; cod = id
      }

    id-span⇒ : ∀ {X : Obj} → T-Span⇒ (id-span {X}) (id-span {X}) 
    id-span⇒ = record
      { arr = id
      ; commute-dom = identityʳ
      ; commute-cod = identityʳ
      }

    _⊚₀_ : T-Span Y Z → T-Span X Y → T-Span X Z
    _⊚₀_ {X = X} f g = 
      let pullback : Pullback (T₁ (cod g)) (dom f)
          pullback = has-pullbacks (T₁ (cod g)) (dom f)
      in record
        { M = Pullback.P pullback
        ; dom = T.μ.η X ∘ T₁ (dom g) ∘ Pullback.p₁ pullback
        ; cod = cod f ∘ Pullback.p₂ pullback
        }

    _⊚₁_ : ∀ {f f′ : T-Span Y Z} → {g g′ : T-Span X Y} → (α : T-Span⇒ f f′) → (β : T-Span⇒ g g′) → T-Span⇒ (f ⊚₀ g) (f′ ⊚₀ g′)
    _⊚₁_  {X = X} {f} {f′} {g} {g′} α β = 
      let pullback = has-pullbacks (T₁ (cod g)) (dom f)
          pullback′ = has-pullbacks (T₁ (cod g′)) (dom f′)

          chase : T₁ (cod g′) ∘ T₁ (arr β) ∘ Pullback.p₁ pullback ≈ dom f′ ∘ arr α ∘ Pullback.p₂ pullback
          chase = begin
              T₁ (cod g′) ∘ T₁ (arr β) ∘ Pullback.p₁ pullback ≈⟨ pullˡ (⟺ (T.F.homomorphism)) ⟩
              T₁ (cod g′ ∘ arr β) ∘ Pullback.p₁ pullback      ≈⟨ T-resp-≈ (commute-cod β) ⟩∘⟨refl ⟩
              T₁ (cod g) ∘ Pullback.p₁ pullback               ≈⟨ Pullback.commute pullback ⟩
              dom f ∘ Pullback.p₂ pullback                    ≈⟨ pushˡ (⟺ (commute-dom α)) ⟩
              dom f′ ∘ arr α ∘ Pullback.p₂ pullback           ∎
      in record
        { arr = Pullback.universal pullback′ chase
        ; commute-dom = begin
          (T.μ.η X ∘ T₁ (dom g′) ∘ Pullback.p₁ pullback′) ∘ Pullback.universal pullback′ chase ≈⟨ pull-last (Pullback.p₁∘universal≈h₁ pullback′) ⟩
          T.μ.η X ∘ T₁ (dom g′) ∘ T₁ (arr β) ∘ Pullback.p₁ pullback                            ≈⟨ refl⟩∘⟨ pullˡ (⟺ T.F.homomorphism) ⟩
          T.μ.η X ∘ T₁ (dom g′ ∘ arr β) ∘ Pullback.p₁ pullback                                 ≈⟨ refl⟩∘⟨ (T-resp-≈ (commute-dom β)) ⟩∘⟨refl ⟩
          T.μ.η X ∘ T₁ (dom g) ∘ Pullback.p₁ pullback                                          ∎
        ; commute-cod = begin
          (cod f′ ∘ Pullback.p₂ pullback′) ∘ Pullback.universal pullback′ chase ≈⟨ pullʳ (Pullback.p₂∘universal≈h₂ pullback′) ⟩
          cod f′ ∘ arr α ∘ Pullback.p₂ pullback                                 ≈⟨ pullˡ (commute-cod α) ⟩
          cod f ∘ Pullback.p₂ pullback                                          ∎
        }

    ⊚₁-identity : ∀ (f : T-Span Y Z) → (g : T-Span X Y) → T-Spans₁ X Z [ Category.id (T-Spans₁ Y Z) {f} ⊚₁ Category.id (T-Spans₁ X Y) {g} ≈ Category.id (T-Spans₁ X Z) ]
    ⊚₁-identity f g =
      let pullback = has-pullbacks (T₁ (cod g)) (dom f)
      in begin
        Pullback.universal pullback _ ≈˘⟨ Pullback.unique pullback (ℰ.identityʳ ○ introˡ T.F.identity) id-comm ⟩
        ℰ.id ∎

    ⊚₁-homomorphism : ∀ {f f′ f″ : T-Span Y Z} {g g′ g″ : T-Span X Y}
                      → (α : T-Span⇒ f f′) → (α′ : T-Span⇒ f′ f″) → (β : T-Span⇒ g g′) → (β′ : T-Span⇒ g′ g″)
                      → T-Spans₁ X Z [ (T-Spans₁ Y Z [ α′ ∘ α ]) ⊚₁ (T-Spans₁ X Y [ β′ ∘ β ]) ≈ T-Spans₁ X Z [ α′ ⊚₁ β′ ∘ α ⊚₁ β ] ]
    ⊚₁-homomorphism {Y = Y} {Z = Z} {X = X} {f} {f′} {f″} {g} {g′} {g″} α α′ β β′ =
      let pullback = has-pullbacks (T₁ (cod g)) (dom f)
          pullback′ = has-pullbacks (T₁ (cod g′)) (dom f′)
          pullback″ = has-pullbacks (T₁ (cod g″)) (dom f″)

          β-chase = begin
            Pullback.p₁ pullback″ ∘ Pullback.universal pullback″ _ ∘ Pullback.universal pullback′ _ ≈⟨ pullˡ (Pullback.p₁∘universal≈h₁ pullback″) ⟩
            (T₁ (arr β′) ∘ Pullback.p₁ pullback′) ∘ Pullback.universal pullback′ _                  ≈⟨ pullʳ (Pullback.p₁∘universal≈h₁ pullback′) ⟩
            T₁ (arr β′) ∘ T₁ (arr β) ∘ Pullback.p₁ pullback                                         ≈⟨ pullˡ (⟺ T.F.homomorphism) ⟩
            T₁ (arr (T-Spans₁ X Y [ β′ ∘ β ])) ∘ Pullback.p₁ pullback                               ∎

          α-chase = begin
            Pullback.p₂ pullback″ ∘ Pullback.universal pullback″ _ ∘ Pullback.universal pullback′ _ ≈⟨ pullˡ (Pullback.p₂∘universal≈h₂ pullback″) ⟩
            (arr α′ ∘ Pullback.p₂ pullback′) ∘ Pullback.universal pullback′ _                       ≈⟨ pullʳ (Pullback.p₂∘universal≈h₂ pullback′) ⟩
            arr α′ ∘ arr α ∘ Pullback.p₂ pullback                                                   ≈⟨ sym-assoc ⟩
            (arr α′ ∘ arr α) ∘ Pullback.p₂ pullback                                                 ∎

      in sym (Pullback.unique pullback″ β-chase α-chase)

    ⊚₁-resp-≈ : ∀ {f f′ : T-Span Y Z} {g g′ : T-Span X Y} (α α′ : T-Span⇒ f f′) (β β′ : T-Span⇒ g g′)
                → (α-eq : T-Spans₁ Y Z [ α ≈ α′ ]) → (β-eq : T-Spans₁ X Y [ β ≈ β′ ]) → T-Spans₁ X Z [ α ⊚₁ β ≈ α′ ⊚₁ β′ ]
    ⊚₁-resp-≈ {f = f} {f′ = f′} {g = g} {g′ = g′} α α′ β β′ α-eq β-eq =
      let pullback′ = has-pullbacks (T₁ (cod g′)) (dom f′)
      in Pullback.universal-resp-≈ pullback′ (∘-resp-≈ˡ (T-resp-≈ β-eq)) (∘-resp-≈ˡ α-eq)

    span-∘ : Functor (Product (T-Spans₁ Y Z) (T-Spans₁ X Y)) (T-Spans₁ X Z)
    span-∘ = record
      { F₀ = λ (f , g) → f ⊚₀ g
      ; F₁ = λ (α , β) → α ⊚₁ β
      ; identity = λ {(f , g)} → ⊚₁-identity f g
      ; homomorphism = λ {(f , g)} {(f′ , g′)} {(f″ , g″)} {(α , β)} {(α′ , β′)} → ⊚₁-homomorphism α α′ β β′
      ; F-resp-≈ = λ {(f , g)} {(f′ , g′)} {(α , β)} {(α′ , β′)} (α-eq , β-eq) → ⊚₁-resp-≈ α α′ β β′ α-eq β-eq
      }

    span-∘-unitˡ : ∀ {E E′ : ℰ.Obj} → (f : T-Span E E′) → T-Span⇒ (id-span ⊚₀ f) f
    span-∘-unitˡ {E} {E′} f =
      let pullback = has-pullbacks (T₁ (cod f)) (T.η.η E′)
          pullback-η = Pullback.swap (IsPullback⇒Pullback (cartesian-η (cod f)))
          pullback-iso = Pullback.up-to-iso pullback pullback-η
          open _≅_
      in record
        { arr = from pullback-iso
        ; commute-dom = ⟺ $ switch-tofromʳ pullback-iso $ begin
          (T.μ.η E ∘ T₁ (dom f) ∘ Pullback.p₁ pullback) ∘ Pullback.universal pullback _ ≈⟨ pull-last (Pullback.p₁∘universal≈h₁ pullback) ⟩
          T.μ.η E ∘ T₁ (dom f) ∘ T.η.η (M f) ≈⟨ refl⟩∘⟨ T.η.sym-commute (dom f) ⟩
          T.μ.η E ∘ T.η.η (T₀ E) ∘ dom f ≈⟨ cancelˡ T.identityʳ ⟩
          dom f ∎
        ; commute-cod = ⟺ $ switch-tofromʳ pullback-iso $ begin
          (id ∘ Pullback.p₂ pullback) ∘ Pullback.universal pullback _ ≈⟨ pullʳ (Pullback.p₂∘universal≈h₂ pullback) ⟩
          id ∘ cod f ≈⟨ identityˡ ⟩
          cod f ∎
        }
