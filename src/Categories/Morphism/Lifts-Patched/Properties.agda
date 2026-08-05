{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphism.Lifts-Patched.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Categories.Category.Construction.Arrow 𝒞

open import Categories.Diagram.Pullback 𝒞
open import Categories.Diagram.Pushout 𝒞

open import Categories.Morphism.Lifts 𝒞
open import Categories.Morphism.Lifts-Patched 𝒞

open import Categories.Morphism.Reasoning 𝒞
import Categories.Morphism as Mor

open Category 𝒞
open Definitions 𝒞
open HomReasoning

open Mor 𝒞 using (Mono; Epi)

--------------------------------------------------------------------------------
-- Uniqueness of Diagonals

module _ {A B X Y : Obj} {i : A ⇒ B} {f : A ⇒ X}
         {g : B ⇒ Y} {p : X ⇒ Y} where
  Mono⇒UniqueDiagonal : Mono p
                      → CommutativeSquare i f g p
                      → (d : B ⇒ X)
                      → p ∘ d ≈ g
                      → UniqueDiagonal i f g p
  Mono⇒UniqueDiagonal p-mono g∘i≈p∘f d p∘d≈g = record
    { diagonal = diag
    ; unique = λ v → p-mono d (Diagonal.d v) (diag .commʳ ○ ⟺ (v .commʳ))
    }
    where
      diag : Diagonal _ _ _ _
      diag = record
        { d = d
        ; commˡ = p-mono (d ∘ i) f (pullˡ p∘d≈g ○ g∘i≈p∘f)
        ; commʳ = p∘d≈g
        }
      open Diagonal hiding (d)

  Epi⇒UniqueDiagonal : Epi i
                     → CommutativeSquare i f g p
                     → (d : B ⇒ X)
                     → d ∘ i ≈ f
                     → UniqueDiagonal i f g p
  Epi⇒UniqueDiagonal p-epi g∘i≈p∘f d d∘i≈f = record
    { diagonal = diag
    ; unique = λ v → p-epi d (Diagonal.d v) (diag .commˡ ○ ⟺ (v .commˡ))
    }
    where
      diag : Diagonal _ _ _ _
      diag = record
        { d = d
        ; commˡ = d∘i≈f
        ; commʳ = p-epi (p ∘ d) g (pullʳ d∘i≈f ○ ⟺ g∘i≈p∘f)
        }
      open Diagonal hiding (d)

