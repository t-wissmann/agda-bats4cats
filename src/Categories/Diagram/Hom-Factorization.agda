{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)

open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Diagram.Cocone

module Categories.Diagram.Hom-Factorization
  {o o' ℓ ℓ' e e'}
  {𝒞 : Category o ℓ e}
  {𝒟 : Category o' ℓ' e'}
  {D : Functor 𝒟 𝒞}
  (cocone : Cocone D)
  where

private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module D = Functor D
    module cocone = Cocone cocone

open Category 𝒞 using (_⇒_; _≈_; _∘_)

record Triangle {P : 𝒞.Obj} (p : P ⇒ cocone.N) : Set (o' ⊔ ℓ ⊔ e) where
  -- a factorization of a morphism through the diagram of a cocone
  constructor triangle
  field
    x : 𝒟.Obj
    p' : P ⇒ D.₀ x
    commutes : p ≈ cocone.ψ x ∘ p'

record identified-in-diagram {P : 𝒞.Obj} {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) : Set (o' ⊔ ℓ' ⊔ e) where
  -- the property whether two morphisms to a diagram object are identified
  -- within the diagram
  field
    j : 𝒟.Obj
    d : i 𝒟.⇒ j
    Dd∘f≈Dd∘g : D.₁ d ∘ f ≈ D.₁ d ∘ g

record identified-in-diagram₂ {P : 𝒞.Obj} {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) : Set (o' ⊔ ℓ' ⊔ e) where
  field
    j : 𝒟.Obj
    f' : i 𝒟.⇒ j
    g' : i 𝒟.⇒ j
    Dd∘f≈Dd∘g : D.₁ f' ∘ f ≈ D.₁ g' ∘ g

UniqueCoconeFactorization : 𝒞.Obj → Set _
UniqueCoconeFactorization P =
    ∀ {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) → cocone.ψ i ∘ f ≈ cocone.ψ i ∘ g →
      identified-in-diagram f g
