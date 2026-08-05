{-# OPTIONS --without-K --safe #-}

open import Categories.Category
import Categories.Morphism.Reasoning

-- Lifting Properties
module Categories.Morphism.Lifts-Patched {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open Category 𝒞
open Definitions 𝒞
open Categories.Morphism.Reasoning 𝒞 using (pullˡ)

open import Categories.Morphism.Lifts 𝒞 using (Filler)

-- The diagonal in a square. The record does not require the square to commute
-- but rather deduces this from the existence of the diagonal.
-- The reason is that if the record is parametrized by a morphism equality,
-- then record types differ if there are multiple (unequal) proofs of
-- morphism equality. Then, properties like FactorizationSystem.diag-unique₂
-- would become more complicated. Thus, Diagonal does not use
-- above Filler record, which is parametric in a morphism equality.
record Diagonal {A B C D} (i : A ⇒ B) (f : A ⇒ C)
                (g : B ⇒ D) (p : C ⇒ D) : Set (ℓ ⊔ e) where
  field
    --      i
    --   A ────> B
    --   │     / │
    --   │  d ╱  │
    -- f │   ╱   │ g
    --   │  ╱    │
    --   V V     V
    --    C ───> D
    --      m
    d : B ⇒ C
    commˡ : d ∘ i ≈ f
    commʳ : p ∘ d ≈ g

  comm : CommutativeSquare i f g p
  comm = begin
    g ∘ i      ≈⟨ pullˡ commʳ ⟨
    p ∘ d ∘ i  ≈⟨ refl⟩∘⟨ commˡ ⟩
    p ∘ f      ∎
    where open HomReasoning

  toFiller : Filler comm
  toFiller = Filler.constructor d commˡ commʳ

Filler⇒Diagonal : ∀ {A B X Y} {i : A ⇒ B} {f : A ⇒ X} {g : B ⇒ Y} {p : X ⇒ Y}
                  {comm : CommutativeSquare i f g p}
                  → Filler comm
                  → Diagonal i f g p
Filler⇒Diagonal f = record { d = filler ; commˡ = fill-commˡ ; commʳ = fill-commʳ }
  where open Filler f

record UniqueDiagonal {A B X Y} (i : A ⇒ B) (f : A ⇒ X)
                      (g : B ⇒ Y) (p : X ⇒ Y) : Set (ℓ ⊔ e) where
  field
    diagonal : Diagonal i f g p
  open Diagonal diagonal public
  field
    unique : ∀ (v : Diagonal i f g p) → d ≈ Diagonal.d v

  unique₂ : ∀ (v w : Diagonal i f g p) → Diagonal.d v ≈ Diagonal.d w
  unique₂ v w = begin
    Diagonal.d v  ≈⟨ unique v ⟨
    d             ≈⟨ unique w ⟩
    Diagonal.d w  ∎
    where open HomReasoning



--------------------------------------------------------------------------------
-- Lifings of Morphism Classes

open import Categories.Morphism.Lifts 𝒞 using (MorphismClass)

_⊆_ : {p q : Level} → MorphismClass p → MorphismClass q → Set (o ⊔ ℓ ⊔ p ⊔ q)
M ⊆ N = ∀ {X Y} → {f : X ⇒ Y} → M f → N f


≈-closed : {p : Level} → (M : MorphismClass p) → Set (o ⊔ ℓ ⊔ e ⊔ p)
≈-closed M = ∀ {X Y} → {f g : X ⇒ Y} → f ≈ g → M f → M g

-- Bundled structure for members of a morphism class
record MorphismClassMember {p : Level} (M : MorphismClass p) (A B : Obj) : Set (p ⊔ ℓ) where
  field
    mor : A ⇒ B
    in-class : M mor

