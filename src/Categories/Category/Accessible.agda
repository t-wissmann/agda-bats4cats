{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory
open import Categories.Object.Initial
open import Categories.Category.Construction.Thin
open import Categories.Category.Cocomplete
open import Categories.Category.Slice
open import Categories.Category.Instance.Setoids
open import Data.Product

open import Categories.Diagram.Colimit.Colimit-Lemmas
open import Categories.Diagram.Filtered

open import Relation.Binary using (Poset)

-- In usual L(F)P-Categories, one considers a (regular) cardinal λ and
-- then defines λ-presentable objects as those whose hom-set preserves
-- colimits of λ-filtered diagrams. The notion 'λ-filtered' entails that
-- the diagram has upper bounds for any set of elements of size smaller than λ.
-- Since this is inherently ordinal-based, we change the definition for the
-- formalization in agda: Instead of explicitly mentioning ordinals, we consider
-- a property/predicate 'Fil' on diagrams which is assumed to imply filteredness.
-- This subsumes stricter filteredness-notions such as countable-filteredness.
module Categories.Category.Accessible
                 {o ℓ prop-level} (𝒞 : Category o ℓ ℓ)
                 (Fil : Category ℓ ℓ ℓ → Set prop-level)
                 (Fil⇒filtered : ∀ {𝒟} → Fil 𝒟 → filtered 𝒟)
                 where

private
  module 𝒞 = Category 𝒞

open import Categories.Diagram.Canonical-Cocone (𝒞)
open import Categories.Functor.Hom
open import Categories.Object.Coproduct (𝒞)
open import Categories.Morphism (𝒞)
open import Categories.Morphism.Reasoning.Core 𝒞
open import Categories.Diagram.Coequalizer (𝒞)
open import Categories.Diagram.Pushout (𝒞)
open import Categories.Diagram.Pushout.Properties (𝒞)
open import Categories.Object.Presentable 𝒞 Fil
import Categories.Diagram.Colimit.Setoids-Colimit

open Hom

open import Categories.Diagram.Colimit.Hom-Colimit-Choice 𝒞


record Accessible : Set (o ⊔ suc ℓ ⊔ prop-level) where
  field
    -- a (small)family (resp. 'set') of objects, called 𝒞_p in the paper ...
    Idx : Set ℓ
    fin : Idx → 𝒞.Obj
    -- ... of which every element is presentable
    fin-presentable : ∀ (i : Idx) → presentable (fin i)
    -- All other objects are built from those fp objects:
    build-from-fin : ∀ (X : 𝒞.Obj) → IsLimitting (Cocone[ fin ↓ X ])
    -- and moreover every canonical diagram is filtered
    canonical-has-prop : ∀ (X : 𝒞.Obj) → Fil (Cat[ fin ↓ X ])

    -- also, we need finite coproducts of presentable objects:
    coproduct : ∀ (A B : 𝒞.Obj) → presentable A → presentable B → Coproduct A B

  canonical-diagram-scheme : ∀ (X : 𝒞.Obj) → Category ℓ ℓ ℓ
  canonical-diagram-scheme X = Cat[ fin ↓ X ]

  canonical-diagram : ∀ (X : 𝒞.Obj) → Functor (canonical-diagram-scheme X) 𝒞
  canonical-diagram X = Functor[ fin ↓ X ]

  canonical-colimit : ∀ (X : 𝒞.Obj) → Colimit (canonical-diagram X)
  canonical-colimit X = Colimit-from-prop (build-from-fin X)

  -- the family 'fin' forms a generator. This means that for every X,
  -- the morphisms 'fin k ⇒ X' are jointly epic
  fin-generator : ∀ (X : 𝒞.Obj) →
    jointly-epic
      {𝒞 = 𝒞}
      {codom = X}
      (Cocone.ψ Cocone[ fin ↓ X ])
  fin-generator X = colimit-is-jointly-epic (Colimit-from-prop (build-from-fin X))

  -- every presentable object is the split-quotient of some object from
  -- the generating family 𝒞_p:
  presentable-split-in-fin : ∀ (X : 𝒞.Obj) → presentable X → Σ[ i ∈ Idx ] (Retract X (fin i))
  presentable-split-in-fin X X-pres =
    (proj₁ (Triangle.x t)) ,
    (record {
      section = Triangle.p' t ;
      retract = (proj₂ (Triangle.x t)) ;
      is-retract = 𝒞.Equiv.sym (Triangle.commutes t) })
    where
      -- we let the identity on X factor through the canonical
      -- diagram for X:
      t : Triangle (canonical-colimit X) (𝒞.id{X})
      t = hom-colim-choice
            (canonical-colimit X)
            X
            (X-pres
              (canonical-diagram-scheme X)
              (canonical-has-prop X)
              (canonical-diagram X))
            (𝒞.id{X})



  -- the family of all presentable objects
  presentable-obj : Σ 𝒞.Obj presentable → 𝒞.Obj
  presentable-obj = proj₁

  -- the big canonical cocone with all presentable objects is also (co-)limitting:
  presentable-colimit : ∀ (X : 𝒞.Obj) → IsLimitting (Cocone[ presentable-obj ↓ X ])
  presentable-colimit X = record {
      ¡ = λ {K} → record {
        arr = fin-colimit.rep (pres-cocone-to-fin K) ;
        commute = λ{ {(A , A-pres), f} →
          let
            k , g = presentable-split-in-fin A A-pres
            module g = Retract g
            module K = Cocone K
            k-obj : Category.Obj (Cat[ fin ↓ X ])
            k-obj = k , (f ∘ g.retract)
            sliceident =
              begin
              (f ∘ g.retract) ∘ g.section
              ≈⟨ assoc ⟩
              f ∘ g.retract ∘ g.section
              ≈⟨ elimʳ g.is-retract ⟩
              f
              ∎
          in
          begin
          fin-colimit.rep (pres-cocone-to-fin K) ∘ f
            ≈˘⟨ refl⟩∘⟨ elimʳ g.is-retract ⟩
          fin-colimit.rep (pres-cocone-to-fin K) ∘ f ∘ g.retract ∘ g.section
            ≈˘⟨ assoc²βε ⟩
          (fin-colimit.rep (pres-cocone-to-fin K) ∘ f ∘ g.retract) ∘ g.section
            ≈⟨ fin-colimit.commute ⟩∘⟨refl ⟩
          Cocone.ψ (pres-cocone-to-fin K) k-obj ∘ g.section
            ≡⟨⟩
          K.ψ (((fin k) , (fin-presentable k)) , f ∘ g.retract) ∘ g.section
            ≈⟨ K.commute (slicearr sliceident) ⟩
          K.ψ ((A , A-pres), f)
          ∎
          }};
      ¡-unique = λ {K} f →
        begin
        fin-colimit.rep (pres-cocone-to-fin K)
            ≈⟨ fin-colimit.initial.¡-unique (transform-cocone⇒ f) ⟩
        Cocone⇒.arr f
        ∎
        }
    where
      open Category 𝒞
      open HomReasoning

      pres = presentable-obj
      fin-colimit : Colimit (Functor[ fin ↓ X ])
      fin-colimit = Colimit-from-prop (build-from-fin X)
      module fin-colimit = Colimit fin-colimit

      pres-cocone-to-fin : Cocone (Functor[ pres ↓ X ]) → Cocone (Functor[ fin ↓ X ])
      pres-cocone-to-fin K =
        record { coapex =
          record {
            ψ = λ {(k , f) → K.ψ (((fin k) , (fin-presentable k)) , f)} ;
            commute = K.commute
          } }
        where
          module K = Cocone K

      transform-cocone⇒ : ∀ {K : Cocone _} →
                          Cocone⇒ _ (Cocone[ presentable-obj ↓ X ]) K →
                          Cocone⇒ _ (fin-colimit.colimit) (pres-cocone-to-fin K)
      transform-cocone⇒ {K} mor =
        record {
          arr = Cocone⇒.arr mor ;
          commute = λ { {(k , f)} → Cocone⇒.commute mor }
        }

