{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Morphism.Lifts using (MorphismClass)

module Batteries.Morphism.FactorizationSystem where


private
  variable
    o ℓ e ℓℰ ℓℳ : Level
    𝒞 : Category o ℓ e

open import Batteries.Morphism.FactorizationSystem.Core

FactorizationSystem-syntax : (𝒞 : Category o ℓ e) → MorphismClass 𝒞 ℓℰ → MorphismClass 𝒞 ℓℳ → Set (o ⊔ ℓ ⊔ e ⊔ ℓℰ ⊔ ℓℳ)
FactorizationSystem-syntax 𝒞 ℰ ℳ = FactorizationSystem 𝒞 ℰ ℳ

syntax FactorizationSystem-syntax 𝒞 ℰ ℳ = [ ℰ , ℳ ]-structured 𝒞




