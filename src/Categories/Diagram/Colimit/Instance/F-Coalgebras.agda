{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Agda.Builtin.Equality renaming (refl to ≡-refl)
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ; F-map-Cocone⇒ˡ)

module Categories.Diagram.Colimit.Instance.F-Coalgebras
       {o ℓ e}
       {𝒞 : Category o ℓ e}
       {F : Endofunctor 𝒞} where

private
  module 𝒞 = Category 𝒞
  module F = Functor F

open import Level

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial using (IsInitial)
open import Categories.Category.Construction.Cocones using (Cocones)

open import Categories.Diagram.Colimit.Colimit-Lemmas

open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone

-- The forgetful functor from coalgebras to the base category:
forget-Coalgebra : Functor (F-Coalgebras F) 𝒞
forget-Coalgebra =
    let
      -- open Category (F-Coalgebras F)
      open Category 𝒞
      open HomReasoning
      open Equiv
    in
    record
      { F₀ = F-Coalgebra.A
      ; F₁ = F-Coalgebra-Morphism.f
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = λ equal → equal
      }


open import Categories.Category.Cocomplete
open import Categories.Functor using (_∘F_)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cocone

-- For every cocone of a diagram, of coalgebras, we can apply the functor F to the cocone tip
apply-F-to-Coapex : {o' ℓ' e' : Level}
    → {D : Category o' ℓ' e'}
    → (J : Functor D (F-Coalgebras F))
    → {N : 𝒞.Obj}
    → Coapex (forget-Coalgebra ∘F J) N
    → Coapex (forget-Coalgebra ∘F J) (F.₀ N)
apply-F-to-Coapex J {N} coapex = record
  { ψ = λ X → F.₁ (coapex.ψ X) ∘ F-Coalgebra.α (J.₀ X)
  ; commute = λ {X} {Y} h →
      let module h = F-Coalgebra-Morphism (J.F₁ h) in
      begin
      (F.₁ (coapex.ψ Y) ∘ F-Coalgebra.α (J.₀ Y)) ∘ h.f   ≈⟨ assoc ⟩
      F.₁ (coapex.ψ Y) ∘ F-Coalgebra.α (J.₀ Y) ∘ h.f     ≈⟨ refl⟩∘⟨ h.commutes ⟩
      F.₁ (coapex.ψ Y) ∘ F.₁ h.f ∘ F-Coalgebra.α (J.₀ X) ≈⟨ pushˡ F.homomorphism ⟨
      F.₁ (coapex.ψ Y ∘ h.f) ∘ F-Coalgebra.α (J.₀ X)     ≈⟨ F.F-resp-≈ (coapex.commute h) ⟩∘⟨refl ⟩
      F.₁ (coapex.ψ X) ∘ F-Coalgebra.α (J.₀ X)           ∎
  }
  where
    open Category 𝒞
    open HomReasoning
    module coapex = Coapex coapex
    module J = Functor J

-- Same as apply-F-to-Coapex but now for Cocones (hiding the tip)
apply-F-to-Cocone-coapex : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
  → Cocone (forget-Coalgebra ∘F J)
  → Cocone (forget-Coalgebra ∘F J)
apply-F-to-Cocone-coapex J cocone =
  record { coapex = apply-F-to-Coapex J (Cocone.coapex cocone) }

-- Whenever a cocone in F-Coalgebras is (co)limitting on the level of the base category,
-- it is (co)limitting in F-Coalgebras, too!
F-Coalgebras-Limitting-Cocone : {o' ℓ' e' : Level} → {𝒟 : Category o' ℓ' e'}
  → (J : Functor 𝒟 (F-Coalgebras F))
  → (K : Cocone J)
  → IsInitial (Cocones (forget-Coalgebra ∘F J)) (F-map-Coconeˡ forget-Coalgebra K)
  → IsInitial (Cocones J) K
F-Coalgebras-Limitting-Cocone J K U[K]-initial = record
  { ¡ = λ {K'} → -- given a competing cocone K'
      let open for-competing-cocone K' in
      record
      { arr = record
        { f = h.arr
        ; commutes =
          -- we use the initiality in the base category
          -- to prove that α is a coalgebra morphism:
          U∘K-initial.¡-unique₂
             {apply-F-to-Cocone-coapex J (F-map-Coconeˡ U K')}
             α∘h
             F[h]∘α
        }
      ; commute = Cocone⇒.commute h
      }
  ; ¡-unique = λ {K'} β → U∘K-initial.¡-unique (F-map-Cocone⇒ˡ U β)
  }
  where
    module J = Functor J
    U = forget-Coalgebra
    U[_] = F-map-Coconeˡ forget-Coalgebra 
    module U[K] = Cocone U[ K ]
    module K = Cocone K
    module U∘K-initial = IsInitial U[K]-initial
    open Category 𝒞
    open HomReasoning
    open F-Coalgebra-Morphism

    module for-competing-cocone (K' : Cocone J) where
      -- Steps inside above ¡ field to make the let .. in smaller:

      -- Initiality gives the cocone morphism in the base category:
      h : Cocone⇒ (U ∘F J) U[ K ] U[ K' ]
      h = U∘K-initial.¡
      module h = Cocone⇒ h
      -- In order to prove that h is a coalgebra morphism,
      -- we turn each of the two paths of the respective diagram
      -- into cocone morphisms:
      F[h]∘α α∘h : Cocone⇒ (U ∘F J) U[ K ] (apply-F-to-Cocone-coapex J U[ K' ])
      α∘h = record
        { arr = F-Coalgebra.α (Cocone.N K') ∘ h.arr
        ; commute = λ {X} → begin
          (F-Coalgebra.α (Cocone.N K') ∘ h.arr) ∘ U[K].ψ X ≈⟨ assoc ⟩
          F-Coalgebra.α (Cocone.N K') ∘ h.arr ∘ U[K].ψ X   ≈⟨ refl⟩∘⟨  h.commute  ⟩
          F-Coalgebra.α (Cocone.N K') ∘ (Cocone.ψ K' X .f) ≈⟨ Cocone.ψ K' X .commutes ⟩
          F.₁ (Cocone.ψ K' X .f) ∘ F-Coalgebra.α (J.₀ X)   ≡⟨⟩
          F.₁ (Cocone.ψ U[ K' ] X) ∘ F-Coalgebra.α (J.₀ X) ∎
        }
      F[h]∘α = record
        { arr = F.₁ h.arr ∘ F-Coalgebra.α (Cocone.N K)
        ; commute = λ {X} → begin
          (F.₁ h.arr ∘ F-Coalgebra.α K.N) ∘ U[K].ψ X ≈⟨ assoc ⟩
          F.₁ h.arr ∘ F-Coalgebra.α K.N ∘ U[K].ψ X ≈⟨ refl⟩∘⟨ (K.ψ X) .commutes ⟩
          F.₁ h.arr ∘ F.₁ (U[K].ψ X) ∘ F-Coalgebra.α (J.₀ X) ≈⟨ pushˡ F.homomorphism ⟨
          F.₁ (h.arr ∘ U[K].ψ X) ∘ F-Coalgebra.α (J.₀ X) ≈⟨ F.F-resp-≈ h.commute ⟩∘⟨refl ⟩
          F.₁ (Cocone.ψ U[ K' ] X) ∘ F-Coalgebra.α (J.₀ X) ∎
        }

F-Coalgebras-Lift-Cocone : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
  → Colimit (forget-Coalgebra ∘F J) → Cocone J
F-Coalgebras-Lift-Cocone J colim = J-cocone
  where
    module J = Functor J
    module colim = Colimit colim
    -- Question: why does the following line work but not `K = colim.initial.⊥.N`?
    K = Cocone.N colim.initial.⊥
    -- for the coalgebra on K, we define a cocone with tip 'FK:'
    FK-cocone : Cocone (forget-Coalgebra ∘F J)
    FK-cocone = apply-F-to-Cocone-coapex J colim.colimit

    -- and we then use the universal property of K to define a coalgebra on K.
    -- for that, we first use the universal property:
    cocone-morph : Cocone⇒ _ colim.initial.⊥ FK-cocone
    cocone-morph = IsInitial.¡ colim.initial.⊥-is-initial
    k : F-Coalgebra-on F K
    k = Cocone⇒.arr cocone-morph

    K,k : F-Coalgebra F
    K,k = record { A = K ; α = k }

    -- the colimit injections/projections are all coalgebra morphisms:
    coalg-inj : ∀ A → F-Coalgebra-Morphism (J.F₀ A) K,k
    coalg-inj = λ A,α →
      let
        open Functor F
        open Category 𝒞
        open F-Coalgebra (J.F₀ A,α)
        open HomReasoning
      in
      record {
      -- the underlying morphism is just the ordinary colimit injection
      f = colim.proj A,α ;
      commutes =
          begin
          k ∘ colim.proj A,α   ≈⟨ Cocone⇒.commute cocone-morph ⟩
          F₁ (colim.proj A,α) ∘ α
          ∎
      }

    J-cocone : Cocone J
    J-cocone = record { coapex = record {
      ψ = coalg-inj ;
      commute = Cocone.commute colim.initial.⊥
      } }

F-Coalgebras-Colimit-Carrier-Limitting : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
        → (colim : Colimit (forget-Coalgebra ∘F J))
        → IsLimitting (F-map-Coconeˡ forget-Coalgebra (F-Coalgebras-Lift-Cocone J colim))
F-Coalgebras-Colimit-Carrier-Limitting J colim =
      record {
        ¡ = λ {K'} →
          record {
            arr = colim.rep K' ;
            commute = colim.commute } ;
        ¡-unique = λ {K'} f →
          let
            -- we need to unfold/fold the definitions a bit:
            f' : Cocone⇒ _ colim.colimit K'
            f' = record { arr = Cocone⇒.arr f ; commute = Cocone⇒.commute f }
            eq : 𝒞 [ Cocone⇒.arr (colim.initial.¡ {K'}) ≈ Cocone⇒.arr f' ]
            eq = colim.initial.¡-unique f'
          in
          eq
          }
      where
        module J = Functor J
        module colim = Colimit colim
        J-cocone : Cocone J
        J-cocone = F-Coalgebras-Lift-Cocone J colim


F-Coalgebras-Colimit : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
        → Colimit (forget-Coalgebra ∘F J) → Colimit J
F-Coalgebras-Colimit {o'} {ℓ'} {e'} {D} J colim =
  Colimit-from-prop
    (F-Coalgebras-Limitting-Cocone J J-cocone
      (F-Coalgebras-Colimit-Carrier-Limitting J colim))
  where
        J-cocone : Cocone J
        J-cocone = F-Coalgebras-Lift-Cocone J colim

F-Coalgebras-Cocomplete : (o' ℓ' e' : Level) → Cocomplete o' ℓ' e' 𝒞 → Cocomplete o' ℓ' e' (F-Coalgebras F)
F-Coalgebras-Cocomplete o' ℓ' e' C-Cocomplete {D} = λ (J : Functor D (F-Coalgebras F)) →
  F-Coalgebras-Colimit J (C-Cocomplete (forget-Coalgebra ∘F J))
