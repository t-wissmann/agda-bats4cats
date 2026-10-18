{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Data.Product

open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties

import Categories.Diagram.Colimit.Setoids-Choice as Setoids
import Categories.Diagram.Colimit.Setoids-Colimit as Setoids-Colimit
open import Helper-Definitions
open import Categories.Diagram.Colimit.Setoids-Colimit using (KernelPairs)
open import Categories.Diagram.Colimit.Colimit-Lemmas
open import Categories.Diagram.Filtered

import Categories.Diagram.Hom-Factorization

module Categories.Diagram.Colimit.Hom-Colimit-Choice
  {o ℓ} (𝒞 : Category o ℓ ℓ)
  where

private
    module 𝒞 = Category 𝒞

open import Categories.Morphism.Reasoning.Core 𝒞

-- We only consider 'small' diagram schemes, i.e. those whose levels are bounded
-- by the hom-level ℓ of 𝒞. Then the hom-functors Hom[ 𝒞 ][ P ,-] land in
-- Setoids ℓ ℓ, which is already cocomplete for such schemes, so no level lifting
-- (LiftSetoids) is needed.
module _
  {𝒟 : Category ℓ ℓ ℓ}
  {D : Functor 𝒟 𝒞}
  (colim : Colimit D)
  where

  open Hom 𝒞
  open Categories.Diagram.Hom-Factorization (Colimit.colimit colim)

  private
      module colim = Colimit colim
      module 𝒟 = Category 𝒟
      module D = Functor D

      open Category 𝒞

  -- record Triangle {P : 𝒞.Obj} (p : P ⇒ colim.coapex) : Set ℓ where
  --   -- a factorization of a morphism through the diagram.
  --   constructor triangle
  --   field
  --     x : 𝒟.Obj
  --     p' : P ⇒ D.₀ x
  --     commutes : p ≈ colim.proj x ∘ p'

  -- If a hom-functor 𝒞(P,-) preserves a colimit C, this gives rise to a
  -- factorization of morphisms P ⇒ C through the diagram:
  hom-colim-choice : (P : 𝒞.Obj) →
      preserves-colimit D (Hom[ 𝒞 ][ P ,-]) →
      (p : P ⇒ colim.coapex) →
      Triangle p
  hom-colim-choice P hom-preserves-colim p =
    record { x = x ; p' = p' ;
      commutes =
        begin
        p                            ≈⟨ commutes-in-𝒞 ⟩
        colim.proj x ∘ p' ∘ id   ≈⟨ refl⟩∘⟨ identityʳ ⟩
        colim.proj x ∘ p'
        ∎
      }
    where
      open Setoid renaming (_≈_ to _[[_≈_]])
      homset-colimit = Colimit-from-prop (hom-preserves-colim colim)
      module homset-colimit = Colimit homset-colimit

      x,p' = Setoids.colimit-choice {c = ℓ} {ℓ' = ℓ} homset-colimit p

      x = proj₁ x,p'
      p' = proj₂ x,p'

      commutes : homset-colimit.coapex [[ p ≈ homset-colimit.proj x ⟨$⟩ p' ]]
      commutes =
        (Setoids.colimit-choice-correct {c = ℓ} {ℓ' = ℓ} homset-colimit {p})

      -- since hom functors are defined as bi-functor, we have an ∘id on the right:
      commutes-in-𝒞 : p ≈ colim.proj x ∘ p' ∘ id
      commutes-in-𝒞 = commutes

      open HomReasoning

      

  -- The property that morphisms from a given object factorize (at most) uniquely
  -- through the diagram D:
  UniqueColimitFactorization : 𝒞.Obj → Set _
  UniqueColimitFactorization P =
      ∀ {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) → colim.proj i ∘ f ≈ colim.proj i ∘ g →
        Σ[ i' ∈ 𝒟.Obj ]
          Σ[ f' ∈ i 𝒟.⇒ i' ]
          Σ[ g' ∈ i 𝒟.⇒ i' ]
          (D.₁ f' ∘ f ≈ D.₁ g' ∘ g)

  -- The same property, but with a single identifying morphism:
  UniqueColimitFactorization₁ : 𝒞.Obj → Set _
  UniqueColimitFactorization₁ P =
      ∀ {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) → colim.proj i ∘ f ≈ colim.proj i ∘ g →
        Σ[ i' ∈ 𝒟.Obj ] Σ[ h ∈ i 𝒟.⇒ i' ] (D.₁ h ∘ f ≈ D.₁ h ∘ g)

  include-UniqueColimitFactorization₁ : (P : 𝒞.Obj) →
    UniqueColimitFactorization₁ P →
    UniqueColimitFactorization P
  include-UniqueColimitFactorization₁ P uniq1 {i} f g eq =
    let
      i' , h , eq = uniq1 {i} f g eq
    in
    i' , (h , (h , eq))

  -- If the diagram is filtered, then the above two properties are equivalent:
  coequalize-colimit-factorization : (P : 𝒞.Obj) → filtered 𝒟 →
    UniqueColimitFactorization P →
    UniqueColimitFactorization₁ P
  coequalize-colimit-factorization P fil factor2 {i} f g eq-proj
      with (factor2 {i} f g eq-proj)
      -- We take the factorization with the two injections:
  ... | (j , f' , (g' , binary-prop)) = 
    M.tip , ((k 𝒟.∘ f') , (begin
      D.₁ (k 𝒟.∘ f') ∘ f ≈⟨ D.homomorphism ⟩∘⟨refl ⟩
      (D.₁ k ∘ D.₁ f') ∘ f ≈⟨ assoc ⟩
      D.₁ k ∘ (D.₁ f' ∘ f) ≈⟨ refl⟩∘⟨ binary-prop ⟩
      D.₁ k ∘ (D.₁ g' ∘ g) ≈⟨ sym-assoc ⟩
      (D.₁ k ∘ D.₁ g') ∘ g ≈˘⟨ D.homomorphism ⟩∘⟨refl ⟩
      D.₁ (k 𝒟.∘ g') ∘ g ≈˘⟨ D.F-resp-≈ M.prop ⟩∘⟨refl ⟩
      D.₁ (k 𝒟.∘ f') ∘ g
    ∎))
    where
      -- and the merge f' and g'
      M : MergedMorphisms _ f' g'
      M = filtered.merge-all fil f' g'
      module M = MergedMorphisms M
      -- module fil = fuse-parallel-morphisms (filtered.fuse-parallel fil)
      k = M.merge
      open HomReasoning

  hom-colim-unique-factor :
      filtered 𝒟 →
      (P : 𝒞.Obj) →
      IsLimitting (F-map-Coconeˡ (Hom[ 𝒞 ][ P ,-]) (Colimit.colimit colim)) →
      UniqueColimitFactorization P
  hom-colim-unique-factor fil P is-colim {i} f g pr∘f≈pr∘g =
    I.B , I.inj₁ , (I.inj₂ , (begin
      D.₁ I.inj₁ ∘ f ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
      D.₁ I.inj₁ ∘ f ∘ id ≈⟨ I.identifies ⟩
      D.₁ I.inj₂ ∘ g ∘ id ≈⟨ refl⟩∘⟨ identityʳ ⟩
      D.₁ I.inj₂ ∘ g
      ∎))
    where
      open HomReasoning

      ident-f-g : Setoids-Colimit.identified-in-diagram {c = ℓ} {ℓ' = ℓ} (Hom[ 𝒞 ][ P ,-] ∘F D) f g
      ident-f-g =
        Setoids-Colimit.filtered-identification-colim
          {c = ℓ} {ℓ' = ℓ}
          (Hom[ 𝒞 ][ P ,-] ∘F D)
          (Colimit-from-prop is-colim)
          fil
          (begin
           colim.proj i ∘ f ∘ id  ≈⟨ refl⟩∘⟨ identityʳ ⟩
           colim.proj i ∘ f  ≈⟨ pr∘f≈pr∘g ⟩
           colim.proj i ∘ g  ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
           colim.proj i ∘ g ∘ id
           ∎)

      module I = Setoids-Colimit.identified-in-diagram ident-f-g

  -- a variant of hom-colim-unique-factor with only one
  -- connecting morphism within the diagram:
  hom-colim-unique-factor₁ :
      filtered 𝒟 →
      (P : 𝒞.Obj) →
      Hom[ 𝒞 ][ P ,-] preserves-the-colimit colim →
      UniqueColimitFactorization₁ P
  hom-colim-unique-factor₁ fil P is-colim =
    coequalize-colimit-factorization P fil
      (hom-colim-unique-factor fil P is-colim)


  -- A hom-functor 𝒞(P,-) preserves a colimit C given that
  -- 1. all morphisms P ⇒ C factor through the diagram.
  -- 2. the factorization is unique in the sense that
  --    if there are f g : P ⇒ D.₀ i which are identified in the colimit,
  --    then there is some morphism in the diagram which identifies f and g
  hom-colim-construct :
      has-upper-bounds 𝒟 →
      (P : 𝒞.Obj) →
      (∀ (f : P ⇒ colim.coapex) → Triangle f) →
      UniqueColimitFactorization P →
      IsLimitting (F-map-Coconeˡ (Hom[ 𝒞 ][ P ,-]) (Colimit.colimit colim))
  hom-colim-construct bounds P all-factor uniq-factor =
    Setoids-Colimit.bounded-colimiting
      {c = ℓ} {ℓ' = ℓ}
      (Hom[ 𝒞 ][ P ,-] ∘F D)
      (F-map-Coconeˡ (Hom[ 𝒞 ][ P ,-]) (Colimit.colimit colim))
      bounds
      part1
      part2
    where
      -- Part 1: show that every element in the colimit comes from
      -- somewhere in the diagram
      part1 :  ∀ x → Setoids-Colimit.comes-from-diagram {c = ℓ} {ℓ' = ℓ} (Hom[ 𝒞 ][ P ,-] ∘F D)
               (F-map-Coconeˡ Hom[ 𝒞 ][ P ,-] colim.colimit) x
      part1 f =
        record {
          i = T.x ;
          preimage = T.p' ;
          x-sent-to-c = (begin
            colim.proj T.x ∘ T.p' ∘ id
              ≈⟨ sym-assoc ⟩
            (colim.proj T.x ∘ T.p') ∘ id
              ≈⟨ identityʳ  ⟩
            colim.proj T.x ∘ T.p'
              ≈˘⟨ T.commutes  ⟩
            f
            ∎)
          }
        where
          module T = Triangle (all-factor f)
          open HomReasoning
      -- Part 2: if two elements from the diagram are identified
      -- in the colimit, then they are identified already
      -- somewhere in the diagram
      part2 : ∀ {i : 𝒟.Obj} (k : KernelPairs {c = ℓ} {ℓ' = ℓ} (Hom[ 𝒞 ][ P ,-] ∘F D) (Cocone.ψ (F-map-Coconeˡ Hom[ 𝒞 ][ P ,-] colim.colimit) i)) → Setoids-Colimit.identified-in-diagram {c = ℓ} {ℓ' = ℓ} (Hom[ 𝒞 ][ P ,-] ∘F D) (KernelPairs.pr₁ k) (KernelPairs.pr₂ k)
      part2 {i} kp =
        let
          module kp = KernelPairs kp
          open HomReasoning
          f = kp.pr₁
          g = kp.pr₂
          f-g-ident : colim.proj i ∘ f ≈ colim.proj i ∘ g
          f-g-ident = begin
            (colim.proj i ∘ f)           ≈˘⟨ (refl⟩∘⟨ identityʳ) ⟩
            (colim.proj i ∘ f ∘ id)      ≈⟨ kp.identified ⟩
            (colim.proj i ∘ g ∘ id)      ≈⟨ (refl⟩∘⟨ identityʳ) ⟩
            (colim.proj i ∘ g)
            ∎
          i' , f' , g' , Df'∘f≈Dg'∘g = uniq-factor f g f-g-ident
        in
        record {
          B = i' ; inj₁ = f' ; inj₂ = g' ; identifies =
            (begin
              D.₁ f' ∘ f ∘ id        ≈⟨ refl⟩∘⟨ identityʳ ⟩
              D.₁ f' ∘ f             ≈⟨ Df'∘f≈Dg'∘g ⟩
              D.₁ g' ∘ g             ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
              D.₁ g' ∘ g ∘ id
            ∎)
          }

  -- a hom functor of P preserves a given colimit 'colim' iff
  -- (a) every morphism from P to colim factors through the diagram, and
  -- (b) this factorization is essentially unique
  hom-filtered-colimit-characterization : filtered 𝒟 → (P : 𝒞.Obj) →
      Hom[ 𝒞 ][ P ,-] preserves-the-colimit colim
                    <===>
      (∀ (p : P ⇒ colim.coapex) → Triangle p) × UniqueColimitFactorization₁ P

  hom-filtered-colimit-characterization fil-𝒟 P = ===> , <===
    where
      ===> = λ is-limitting →
        hom-colim-choice P (preserves-all-colimits (Hom[ 𝒞 ][ P ,-]) colim is-limitting)
        ,
        λ {i} → hom-colim-unique-factor₁ fil-𝒟 P (is-limitting) {i = i}

      <===  =
        λ { (exist-factor , uniq-factor) →
          hom-colim-construct
            (filtered.bounds fil-𝒟) P exist-factor
            (include-UniqueColimitFactorization₁ P uniq-factor) }
