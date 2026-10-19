{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)

open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Diagram.Cocone
open import Categories.Diagram.Filtered

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
open import Categories.Morphism.Reasoning 𝒞

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


record identified-in-diagram₂ {P : 𝒞.Obj}
                              {i j : 𝒟.Obj}
                              (f : P ⇒ D.₀ i)
                              (g : P ⇒ D.₀ j) : Set (o' ⊔ ℓ' ⊔ e) where
  -- heterogenous version of identified-in-diagram:
  -- two morphisms to two different objects in the diagram
  field
    ij : 𝒟.Obj
    f' : i 𝒟.⇒ ij
    g' : j 𝒟.⇒ ij
    Dd∘f≈Dd∘g : D.₁ f' ∘ f ≈ D.₁ g' ∘ g

  -- identified₁ : MergeAllParallelMorphisms 𝒟 → identified-in-diagram f g
  -- identified₁ merge-all = record
  --   { j = tip
  --   ; d = merge 𝒟.∘ f'
  --   ; Dd∘f≈Dd∘g = begin
  --     D.₁ (merge 𝒟.∘ f') ∘ f   ≈⟨ pushˡ D.homomorphism ⟩
  --     D.₁ merge ∘ D.₁ f' ∘ f   ≈⟨ refl⟩∘⟨ Dd∘f≈Dd∘g ⟩
  --     D.₁ merge ∘ D.₁ g' ∘ g   ≈⟨ pushˡ D.homomorphism ⟨
  --     D.₁ (merge 𝒟.∘ g') ∘ g   ≈⟨ D.F-resp-≈ prop ⟩∘⟨refl ⟨
  --     D.₁ (merge 𝒟.∘ f') ∘ g   ∎
  --   }
  --   where
  --     open MergedMorphisms (MergeAllParallelMorphisms.merge-all merge-all f' g')
  --     open Category.HomReasoning 𝒞



UniqueCoconeFactorization : 𝒞.Obj → Set _
UniqueCoconeFactorization P =
    ∀ {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) → cocone.ψ i ∘ f ≈ cocone.ψ i ∘ g →
      identified-in-diagram f g


record Essentially-Unique-Cocone-Factor {P : 𝒞.Obj} (p : P ⇒ cocone.N)  : Set (o' ⊔ ℓ ⊔ ℓ' ⊔ e) where
  field
    exists : Triangle p
    essentially-unique : ∀ (i : 𝒟.Obj)
                         → (f g : P ⇒ D.₀ i)
                         → (cocone.ψ i ∘ f ≈ p)
                         → (cocone.ψ i ∘ g ≈ p)
                         → identified-in-diagram f g

  essentially-unique₂ : filtered 𝒟
                        → ∀ {i j : 𝒟.Obj}
                        → (f : P ⇒ D.₀ i)
                        → (g : P ⇒ D.₀ j)
                        → (cocone.ψ i ∘ f ≈ p)
                        → (cocone.ψ j ∘ g ≈ p)
                        → identified-in-diagram₂ f g
  essentially-unique₂ 𝒟-filtered {i} {j} f g ψ[i]∘f≈p ψ[j]∘g≈p = record
    { ij = ij
    ; f' = d 𝒟.∘ i₁ 
    ; g' = d 𝒟.∘ i₂ 
    ; Dd∘f≈Dd∘g = begin
        D.₁ (d 𝒟.∘ i₁) ∘ f ≈⟨ pushˡ D.homomorphism ⟩
        D.₁ d ∘ D.₁ i₁ ∘ f ≈⟨ Dd∘f≈Dd∘g ⟩
        D.₁ d ∘ D.₁ i₂ ∘ g ≈⟨ pushˡ D.homomorphism ⟨
        D.₁ (d 𝒟.∘ i₂) ∘ g ∎
    }
    where
      open filtered 𝒟-filtered
      open UpperBound (construct-upper-bound i j) renaming (obj to k)
      open Category.HomReasoning 𝒞
      m : identified-in-diagram (D.₁ i₁ ∘ f) (D.₁ i₂ ∘ g)
      m = essentially-unique k _ _
          (pullˡ (cocone.commute i₁) ○ ψ[i]∘f≈p)
          (pullˡ (cocone.commute i₂) ○ ψ[j]∘g≈p)
      open identified-in-diagram m renaming (j to ij)
