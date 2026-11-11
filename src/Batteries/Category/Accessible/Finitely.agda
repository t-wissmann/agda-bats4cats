{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category
open import Batteries.Category.Accessible
open import Batteries.Diagram.Filtered using (filtered)

module Batteries.Category.Accessible.Finitely where

Finitely-Accessible : {o ℓ : Level} (𝒞 : Category o ℓ ℓ) → Set _
Finitely-Accessible 𝒞 = Accessible 𝒞 filtered λ x → x
