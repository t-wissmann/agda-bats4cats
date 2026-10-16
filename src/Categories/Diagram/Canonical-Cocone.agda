{-# OPTIONS --without-K --safe #-}
open import Level

open import Data.Product
open import Categories.Category
open import Categories.Category.Slice
open import Categories.Functor
open import Categories.Category.SubCategory
open import Categories.Diagram.Cocone
open import Categories.Functor.Construction.SubCategory

module Categories.Diagram.Canonical-Cocone {o ℓ e} (𝒞 : Category o ℓ e) where

private
  module 𝒞 = Category 𝒞

-- The following functor disappeared from:
-- open import Categories.Functor.Slice (𝒞) using (Forgetful)

Forgetful : ∀{X} → Functor (Slice 𝒞 X) 𝒞
Forgetful {X} = record
                 { F₀ = λ z → SliceObj.Y z
                 ; F₁ = λ {A} {B} f → f .Slice⇒.h
                 ; identity = λ {A} → 𝒞.Equiv.refl
                 ; homomorphism = λ {X = X₁} {Y} {Z} {f} {g} → 𝒞.Equiv.refl
                 ; F-resp-≈ = λ {A} {B} {f} {g} z → z
                 }

-- For each family of fp objects and another objects, we have a slice category:
Cat[_↓_] : {ℓ-I : Level} {I : Set ℓ-I} → (𝒞-fp : I → 𝒞.Obj) → 𝒞.Obj → Category (ℓ-I ⊔ ℓ) (ℓ ⊔ e) e
Cat[_↓_]  {I = I} 𝒞-fp X = FullSubCategory (Slice 𝒞 X) objects
  where
    open Category 𝒞
    objects : Σ[ i ∈ I ] (𝒞-fp i ⇒ X) → Category.Obj (Slice 𝒞 X)
    objects (i , i⇒X) = sliceobj i⇒X

-- and an obvious forgetful functor (resp. diagram)
Functor[_↓_] : {ℓ-I : Level} {I : Set ℓ-I} → (𝒞-fp : I → 𝒞.Obj) → (X : 𝒞.Obj) → Functor (Cat[ 𝒞-fp ↓ X ]) 𝒞
Functor[_↓_]  𝒞-fp X = Forgetful ∘F (FullSub _)

-- which has a canonical Cocone: X itself
Cocone[_↓_] : {ℓ-I : Level} {I : Set ℓ-I} → (𝒞-fp : I → 𝒞.Obj) → (X : 𝒞.Obj) → Cocone (Functor[ 𝒞-fp ↓ X ])
Cocone[_↓_]  𝒞-fp X = record { coapex = record {
    ψ = λ (i , i⇒X) → i⇒X ;
    commute = Slice⇒.△
  } }
