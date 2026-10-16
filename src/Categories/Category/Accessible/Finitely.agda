{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category
open import Categories.Category.Accessible
open import Categories.Diagram.Filtered using (filtered)

module Categories.Category.Accessible.Finitely where

Finitely-Accessible : {o ℓ : Level} (𝒞 : Category o ℓ ℓ) → Set _
Finitely-Accessible 𝒞 = Accessible 𝒞 filtered λ x → x
