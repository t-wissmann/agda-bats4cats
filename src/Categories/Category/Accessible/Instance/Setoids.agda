{-# OPTIONS --without-K --safe #-}
open import Level
import Level as L


open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Hom
open import Categories.Diagram.Filtered
open import Data.Nat using (ℕ)
import Data.Nat
import Data.Sum.Base as Sum
open import Relation.Binary.Core using (Rel)
open import Data.Fin hiding (lift; lower)
open import Data.Fin.Instances using (Fin-≡-isDecEquivalence)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-↑ˡ; splitAt-↑ʳ; splitAt-raise)
open import Data.Product
-- open import Function.Equality hiding (setoid; _∘_; cong) renaming (id to ⟶id)
open import Function.Bundles
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality.Properties
-- open import Relation.Binary.PropositionalEquality using (→-to-⟶)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Diagram.Colimit using (Colimit)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Bundles
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)
open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)


open import Categories.Diagram.Colimit.Setoids-Colimit
open import Categories.Diagram.Colimit.Setoids-Choice
open import Categories.Diagram.Colimit.Colimit-Lemmas
open import Categories.Diagram.Colimit.Hom-Colimit-Choice
open import Categories.Diagram.Colimit.Instance.FinCoequalizer

module Categories.Category.Accessible.Instance.Setoids (ℓ : Level) where

private
  Setoids' = Setoids ℓ ℓ

id-filtered : ∀ {o ℓ e : Level} {𝒟} → filtered {o} {ℓ} {e} 𝒟 → filtered {o} {ℓ} {e} 𝒟
id-filtered f = f

open import Categories.Diagram.Canonical-Cocone Setoids'
open import Categories.Category.Accessible Setoids' filtered id-filtered
open import Categories.Object.Presentable Setoids' filtered
open import Categories.Category.Slice Setoids'

-- The presentable objects of Setoids ℓ ℓ are the finite sets. We realise them by
-- lifting the propositional setoid on (Fin n) up to level ℓ in both the carrier
-- and the equality.
≡-setoid : Set 0ℓ → Setoid ℓ ℓ
≡-setoid X = record
  { Carrier = Lift ℓ X
  ; _≈_ = λ x y → Lift ℓ (lower x ≡ lower y)
  ; isEquivalence = record
    { refl = lift refl
    ; sym = λ p → lift (≡.sym (lower p))
    ; trans = λ p q → lift (≡.trans (lower p) (lower q)) } }

Fin≈ : ℕ → Setoid ℓ ℓ
Fin≈ n = ≡-setoid (Fin n)

-- a morphism of Setoids' out of a finite set is just a function on (Fin n):
fin-func : ∀ {b e : Level} {k : ℕ} {B : Setoid b e} →
           (Fin k → Setoid.Carrier B) → Func (Fin≈ k) B
fin-func {B = B} f = record
  { to = λ x → f (lower x)
  ; cong = λ {x} {y} eq → Setoid.reflexive B (cong f (lower eq)) }

fin-const : ∀ {b e : Level} {k : ℕ} {B : Setoid b e} →
            Setoid.Carrier B → Func (Fin≈ k) B
fin-const x = fin-func (λ _ → x)

-- The index set of the generating family has to live at level ℓ (this is what
-- the 'Accessible' record demands), so we index the finite sets by a lifted ℕ.
ℕ̂ : Set ℓ
ℕ̂ = Lift ℓ ℕ

F̂ : ℕ̂ → Setoid ℓ ℓ
F̂ i = Fin≈ (lower i)

Fin≈-zero-empty : {ℓ-a : Level} {a : Set ℓ-a} → Fin 0 → a
Fin≈-zero-empty ()

Fin-is-presentable : ∀ (n : ℕ) → presentable (Fin≈ n)
Fin-is-presentable n 𝒟 𝒟-filtered J colim =
  -- see where-clause at the end
  bounded-colimiting
    {c = ℓ} {ℓ' = ℓ}
    (lift-hom-n ∘F J)
    (F-map-Coconeˡ lift-hom-n (colim.colimit))
    𝒟-filtered.bounds
    (λ f →
      let
        -- f is essentially a tuple of elements of the colimit:
        _ : Fin n → Setoid.Carrier colim.coapex
        _ = λ k → f ⟨$⟩ lift k
        -- since 'colim' is a colimit in setoids, every element
        -- of the family 'f' comes from some object in the diagram
        source-objects : Fin n → 𝒟.Obj
        source-objects k = proj₁ (colimit-choice {c = ℓ} {ℓ' = ℓ} colim (f ⟨$⟩ lift k))

        -- the diagram is filtered, so these objects have an upper bound:
        B : 𝒟.Obj
        B = 𝒟-filtered.fin-upper-bound source-objects

        -- and so f factors through it:
        g : Fin n → Setoid.Carrier (J.₀ B)
        g k =
          J.₁ (𝒟-filtered.fin-is-above source-objects k)
          ⟨$⟩ proj₂ (colimit-choice {c = ℓ} {ℓ' = ℓ} colim (f ⟨$⟩ lift k))


        open Setoid renaming (_≈_ to _[[_≈_]])
        g-correct : (k : Fin n) → colim.coapex [[ (f ⟨$⟩ lift k) ≈ colim.proj B ⟨$⟩ (g k) ]]
        g-correct k =
          let
            open SetoidR (colim.coapex)
            X , xₖ = colimit-choice {c = ℓ} {ℓ' = ℓ} colim (f ⟨$⟩ lift k)
            connecting-morph = 𝒟-filtered.fin-is-above source-objects k
          in
          begin
          (f ⟨$⟩ lift k)              ≈⟨ colimit-choice-correct {c = ℓ} {ℓ' = ℓ} colim ⟩
          colim.proj X ⟨$⟩ xₖ         ≈˘⟨ colim.colimit-commute connecting-morph ⟩
          (colim.proj B ∘ J.₁ connecting-morph) ⟨$⟩ xₖ        ≡⟨⟩
          colim.proj B ⟨$⟩ (J.₁ connecting-morph ⟨$⟩ xₖ)       ≡⟨⟩
          colim.proj B ⟨$⟩ (g k)
          ∎

        g≈ : Fin≈ n ⇒ J.₀ B
        g≈ = fin-func g
      in
      record {
        i = B ;
        preimage = g≈ ;
        x-sent-to-c = (λ {k} →
          let
            open SetoidR (colim.coapex)
          in
          begin
          (colim.proj B ∘ g≈ ∘ id) ⟨$⟩ k ≡⟨⟩
          colim.proj B ⟨$⟩ (g (lower k)) ≈˘⟨ g-correct (lower k) ⟩
          f ⟨$⟩ k
          ∎
          )
        })
    λ {i} kp →
      let
        module kp = KernelPairs kp
        F-colim = F-map-Coconeˡ (Hom[ Setoids' ][ (Fin≈ n) ,-] ) colim.colimit
        module F-colim = Cocone (F-colim)
        -- we are given two tuples:
        f : Fin≈ n ⇒ J.₀ i
        f = kp.pr₁
        g : Fin≈ n ⇒ J.₀ i
        g = kp.pr₂
        -- which are identified in the cocone
        open Setoid renaming (_≈_ to _[[_≈_]])
        F-identified : F-colim.N [[ F-colim.ψ i ⟨$⟩ kp.pr₁ ≈ F-colim.ψ i ⟨$⟩ kp.pr₂ ]]
        F-identified = kp.identified
        -- expanding the definition of F yields:
        identified : hom-setoid [[ colim.proj i ∘ f ∘ id ≈ colim.proj i ∘ g ∘ id ]]
        identified = kp.identified

        i' , ( h , eq ) = induction n i f g identified
      in
      record { B = i' ; inj₁ = h ; inj₂ = h ; identifies = eq }
  where
    open Hom (Setoids')
    hom-n = Hom[ (Fin≈ n) ,-]
    lift-hom-n = Hom[ Setoids' ][ (Fin≈ n) ,-]
    module colim = Colimit colim
    open Category (Setoids')
    module 𝒟 = Category 𝒟
    module J = Functor J
    module 𝒟-filtered = filtered 𝒟-filtered
    open Setoid renaming (_≈_ to _[[_≈_]])
    induction : ∀ (k : ℕ) (j : Category.Obj 𝒟) →
                  (s t : Fin≈ k ⇒ J.₀ j) →
                  hom-setoid [[ colim.proj j ∘ s ≈ colim.proj j ∘ t ]] →
                  Σ[ j' ∈ 𝒟.Obj ] (Σ[ h ∈ j 𝒟.⇒ j' ] ( hom-setoid [[ J.₁ h ∘ s ≈ J.₁ h ∘ t ]]))
    induction ℕ.zero j s t eq-proj = j , (𝒟.id , (λ {k} → Fin≈-zero-empty (lower k) ))
    induction (ℕ.suc k) j s t eq-proj =
      let
        -- the elements s 0 and t 0 are identified in the colimit:
        proj-identifies-0 : colim.coapex [[ colim.proj j ⟨$⟩ (s ⟨$⟩ lift Fin.zero) ≈ colim.proj j ⟨$⟩ (t ⟨$⟩ lift Fin.zero) ]]
        proj-identifies-0 = eq-proj {lift Fin.zero}

        -- and so s 0 and t 0 are identified somewhere in the diagram:
        ident-in-dia-0 : identified-in-diagram {c = ℓ} {ℓ' = ℓ} J (s ⟨$⟩ lift Fin.zero) (t ⟨$⟩ lift Fin.zero)
        ident-in-dia-0 = filtered-identification-colim {c = ℓ} {ℓ' = ℓ} J colim 𝒟-filtered proj-identifies-0
        module ident-in-dia-0 = identified-in-diagram ident-in-dia-0
        M = 𝒟-filtered.merge-all ident-in-dia-0.inj₁ ident-in-dia-0.inj₂
        module M = MergedMorphisms M
        j-0 = M.tip
        coeq = M.merge
        coeq-prop = M.prop
        h-0 : j 𝒟.⇒ j-0
        h-0 = coeq 𝒟.∘ ident-in-dia-0.inj₁

        -- we restrict s/t/eq-ref to the other components in order to apply the I.H. to them:
        s-suc : Fin≈ k ⇒ J.₀ j
        s-suc = fin-func (λ m → s ⟨$⟩ lift (Fin.suc m))
        t-suc : Fin≈ k ⇒ J.₀ j
        t-suc = fin-func (λ m → t ⟨$⟩ lift (Fin.suc m))
        eq-proj-suc : hom-setoid [[ colim.proj j ∘ s-suc ≈ colim.proj j ∘ t-suc ]]
        eq-proj-suc = λ {x} → eq-proj {lift (Fin.suc (lower x))}
        -- the induction hypothesis:
        j-suc , (h-suc , ident-in-dia-suc) = induction k j s-suc t-suc eq-proj-suc

        -- we can combine the two morphisms for 0 and the I.H.:
        closed = 𝒟-filtered.close-span h-0 h-suc
        module closed = ClosedSpan closed
        j' = closed.tip
        h-inj₁ = closed.close-fst
        h-inj₂ = closed.close-snd
        h : j 𝒟.⇒ j'
        h = h-inj₁ 𝒟.∘ h-0

        -- J-expand-0 : hom-setoid [[ J.₁ h ≈ J.₁ h-inj₁ ∘ J.₁ coeq ∘ J.₁ ident-in-dia-0.inj₁ ]]
        -- J-expand-0 = let open HomReasoning in
        --   begin
        --   J.₁ h ≈⟨ J.homomorphism ⟩
        --   J.₁ h-inj₁ ∘ J.₁ h-0 ≈⟨ (refl⟩∘⟨ J.homomorphism) ⟩
        --   J.₁ h-inj₁ ∘ J.₁ coeq ∘ J.₁ ident-in-dia-0.inj₁
        --   ∎

        open SetoidR (J.₀ j')
        refl-j = (Setoid.refl (J.₀ j))
      in
      j' , h , λ { -- case distinction: so we have either s0/t0 or s-suc/t-suc
        {lift Fin.zero} →
          begin
          (J.₁ h ∘ s) ⟨$⟩ lift Fin.zero ≡⟨⟩
          J.₁ h ⟨$⟩ (s ⟨$⟩ lift Fin.zero) ≈⟨ J.homomorphism ⟩
          J.₁ h-inj₁ ⟨$⟩  (J.₁ (coeq 𝒟.∘ ident-in-dia-0.inj₁) ⟨$⟩ (s ⟨$⟩ lift Fin.zero)) ≈⟨ Func.cong (J.₁ h-inj₁) J.homomorphism ⟩
          (J.₁ h-inj₁ ∘ J.₁ coeq) ⟨$⟩ (J.₁ ident-in-dia-0.inj₁ ⟨$⟩ (s ⟨$⟩ lift Fin.zero)) ≈⟨ Func.cong (J.₁ h-inj₁ ∘ J.₁ coeq) ident-in-dia-0.identifies ⟩
          (J.₁ h-inj₁ ∘ J.₁ coeq) ⟨$⟩ (J.₁ ident-in-dia-0.inj₂ ⟨$⟩ (t ⟨$⟩ lift Fin.zero)) ≈˘⟨ Func.cong (J.₁ h-inj₁) J.homomorphism ⟩
          (J.₁ h-inj₁ ∘ J.₁ (coeq 𝒟.∘ ident-in-dia-0.inj₂)) ⟨$⟩ (t ⟨$⟩ lift Fin.zero) ≈˘⟨ Func.cong (J.₁ h-inj₁) (J.F-resp-≈ coeq-prop) ⟩
          (J.₁ h-inj₁ ∘ J.₁ (coeq 𝒟.∘ ident-in-dia-0.inj₁)) ⟨$⟩ (t ⟨$⟩ lift Fin.zero) ≈˘⟨ J.homomorphism ⟩
          (J.₁ (h-inj₁ 𝒟.∘ coeq 𝒟.∘ ident-in-dia-0.inj₁)) ⟨$⟩ (t ⟨$⟩ lift Fin.zero) ≡⟨⟩
          (J.₁ h ∘ t) ⟨$⟩ lift Fin.zero
          ∎
      ; {lift (Fin.suc m)} →
          begin
          (J.₁ h ∘ s) ⟨$⟩ lift (Fin.suc m) ≡⟨⟩
          (J.₁ (h-inj₁ 𝒟.∘ h-0) ∘ s) ⟨$⟩ lift (Fin.suc m) ≈⟨ J.F-resp-≈ closed.commutes ⟩
          (J.₁ (h-inj₂ 𝒟.∘ h-suc) ∘ s) ⟨$⟩ lift (Fin.suc m) ≈⟨ J.homomorphism ⟩
          J.₁ h-inj₂ ⟨$⟩ (J.₁ h-suc ⟨$⟩ (s ⟨$⟩ lift (Fin.suc m))) ≈⟨ Func.cong (J.₁ h-inj₂) (ident-in-dia-suc {lift m}) ⟩
          J.₁ h-inj₂ ⟨$⟩ (J.₁ h-suc ⟨$⟩ (t ⟨$⟩ lift (Fin.suc m))) ≈˘⟨ J.homomorphism ⟩
          (J.₁ (h-inj₂ 𝒟.∘ h-suc) ∘ t) ⟨$⟩ lift (Fin.suc m) ≈˘⟨ J.F-resp-≈ closed.commutes ⟩
          (J.₁ (h-inj₁ 𝒟.∘ h-0) ∘ t) ⟨$⟩ lift (Fin.suc m) ≡⟨⟩
          (J.₁ h ∘ t) ⟨$⟩ lift (Fin.suc m)
          ∎
      }

canonical-cocone-is-limitting : ∀ (X : Setoid ℓ ℓ) → IsLimitting (Cocone[ F̂ ↓ X ])
canonical-cocone-is-limitting X =
  let
    open Setoid renaming (_≈_ to _[[_≈_]]) hiding (sym)
    CanCocone = Cocone[ F̂ ↓ X ]
    module F = Functor (Functor[ F̂ ↓ X ])
    open Category Setoids'

    t : (Setoid.Carrier X) → Category.Obj (Cat[ F̂ ↓ X ])
    t x = (lift 1 , fin-const x)

    ! : (C : Cocone (Functor[ F̂ ↓ X ])) → Cocone⇒ _ CanCocone C
    ! C =
      let
        module C = Cocone C
        underlying : (Setoid.Carrier X)  → (Setoid.Carrier C.N)
        underlying x = C.ψ (t x) ⟨$⟩ lift Fin.zero
      in
      record {
      arr = record {
        to = underlying
           ;
        cong = λ {x} {x'} x≈x' →
          let
            -- f : Slice⇒ (sliceobj (fin-const x)) (sliceobj (fin-const x'))
            f : (Cat[ F̂ ↓ X ]) [ t x , t x' ]
            f = slicearr
                  {h = id}
                  λ { {lift Fin.zero} → Setoid.sym X x≈x'}
            eq : C.ψ (t x) ≈ C.ψ (t x') ∘ F.₁ f
            eq =
              let open HomReasoning in
              begin
              C.ψ (t x) ≈˘⟨ C.commute f ⟩ C.ψ (t x') ∘ F.₁ f
              ∎
          in
          eq {lift Fin.zero} }
      ; commute = λ {s} {x} →
        let
          n , r = s
          morph : ∀ (y : Setoid.Carrier (F̂ n)) → (Cat[ F̂ ↓ X ]) [ t (r ⟨$⟩ y) , s ]
          morph y =
            slicearr
              {h = fin-const y}
              λ { {lift Fin.zero} → Setoid.refl X}
          open SetoidR (C.N)
        in
        begin
        underlying (r ⟨$⟩ x) ≡⟨⟩
        C.ψ (t (r ⟨$⟩ x)) ⟨$⟩ lift Fin.zero
          ≈˘⟨ C.commute (morph x) ⟩
        C.ψ s ⟨$⟩ ((F.₁ (morph x)) ⟨$⟩ lift Fin.zero)
          ≡⟨⟩
        C.ψ s ⟨$⟩ x
        ∎
        }
  in
  record {
    ! = λ{C} → ! C ;
    !-unique = λ {C} other {x} →
    let
      -- given an other cocone morphism to C
      module C = Cocone C
      module !C = Cocone⇒ (! C)
      module other = Cocone⇒ other
      open SetoidR (C.N)
    in
    begin
    !C.arr ⟨$⟩ x
      ≡⟨⟩
    C.ψ (t x) ⟨$⟩ lift Fin.zero
      ≈˘⟨ other.commute ⟩
    other.arr ⟨$⟩ x
    ∎
  }

concat-tuples : {a : Level} {n m : ℕ} {X : Set a} (s : Fin n → X) (t : Fin m → X) → (Fin (n  Data.Nat.+ m) → X)
concat-tuples {a} {n} {m} s t n+m = Sum.[ s , t ] (splitAt n n+m)



merge-parallel : (k n : ℕ̂) (X : Setoid ℓ ℓ)
  (s : Func (F̂ k) X)
  (t : Func (F̂ n) X)
  (g h : Cat[ F̂ ↓ X ] [ (k , s) , (n , t) ]) → MergedMorphisms (Cat[ F̂ ↓ X ]) g h
merge-parallel k n X s t (slicearr {h = g≈} g-prop) (slicearr {h = h≈} h-prop) =
  record {
    tip = n , t ;
    merge = (slicearr {h = fin-func (λ x → lift (EndoCoeq.f x)) } λ { {x} → Setoid.sym X (merge-△ (lower x)) });
    prop = λ { {x}  → lift (EndoCoeq.identify-R (g₀ (lower x)) (h₀ (lower x)) (lower x , (refl , refl))) }
  }
  where
    module t = Func t
    module g≈ = Func g≈
    module h≈ = Func h≈
    -- the underlying functions on the finite index sets:
    g₀ : Fin (lower k) → Fin (lower n)
    g₀ y = lower (g≈.to (lift y))
    h₀ : Fin (lower k) → Fin (lower n)
    h₀ y = lower (h≈.to (lift y))
    module EndoCoeq = EndoCoequalize (finite-coequalize (lower k) (Fin (lower n)) (IsDecEquivalence._≟_ Fin-≡-isDecEquivalence) g₀ h₀)

    open Setoid X using (_≈_)
    open SetoidR X
    merge-△ : (x : Fin (lower n)) → (t ⟨$⟩ lift x) ≈ (t ⟨$⟩ lift (EndoCoeq.f x))
    merge-△ x = EqClosure-ump _
      (λ y1 y2 → t ⟨$⟩ lift y1 ≈ t ⟨$⟩ lift y2) -- kernelpair
      (setoid-kernel-IsEquivalence X (λ y → t ⟨$⟩ lift y))
      (λ { {y1} {y2} (y , (gy , hy)) →
        begin
        t ⟨$⟩ lift y1          ≡˘⟨ cong (λ z → t ⟨$⟩ lift z) gy ⟩
        t ⟨$⟩ lift (g₀ y)      ≈⟨ g-prop ⟩
        s ⟨$⟩ lift y           ≈˘⟨ h-prop ⟩
        t ⟨$⟩ lift (h₀ y)      ≡⟨ cong (λ z → t ⟨$⟩ lift z) hy ⟩
        t ⟨$⟩ lift y2
        ∎
        })
      (EndoCoeq.reflect-f x)


canonical-cat-is-filtered : ∀ (X : Setoid ℓ ℓ) → filtered (Cat[ F̂ ↓ X ])
canonical-cat-is-filtered X =
  record {
    bounds = record
              { non-empty = lift 0 , (record { to = λ { (lift ()) } ; cong = λ {x} → exfalso (lower x) }) ;
              upper-bound = λ {(k , s) (n , t) →
                lift (lower k Data.Nat.+ lower n) , fin-func (concat-tuples (λ j → s ⟨$⟩ lift j) (λ j → t ⟨$⟩ lift j)) } ;
              is-above₁ = λ {(k , s) (n , t) →
                let
                  open SetoidR X
                  -- inject+ = _↑ˡ_
                in
                slicearr {h = fin-func (λ - → lift (- ↑ˡ lower n))}
                λ {i} → begin
                concat-tuples (λ j → s ⟨$⟩ lift j) (λ j → t ⟨$⟩ lift j) (lower i ↑ˡ lower n)
                  ≡⟨⟩
                Sum.[ (λ j → s ⟨$⟩ lift j) , (λ j → t ⟨$⟩ lift j) ] (splitAt (lower k) (lower i ↑ˡ lower n))
                  ≡⟨ cong Sum.[ (λ j → s ⟨$⟩ lift j) , (λ j → t ⟨$⟩ lift j) ] (splitAt-↑ˡ (lower k) (lower i) (lower n)) ⟩
                -- Sum.[ ... ] (Sum.inj₁ (lower i))
                --  ≡⟨⟩
                s ⟨$⟩ i
                ∎
                } ;
              is-above₂ = λ {(k , s) (n , t) →
                let
                  open SetoidR X
                in
                slicearr {h = fin-func (λ - → lift (lower k ↑ʳ -))}
                λ {i} →
                begin
                concat-tuples (λ j → s ⟨$⟩ lift j) (λ j → t ⟨$⟩ lift j) (lower k ↑ʳ lower i)
                  ≡⟨⟩
                Sum.[ (λ j → s ⟨$⟩ lift j) , (λ j → t ⟨$⟩ lift j) ] (splitAt (lower k) (lower k ↑ʳ lower i))
                  ≡⟨ cong Sum.[ (λ j → s ⟨$⟩ lift j) , (λ j → t ⟨$⟩ lift j) ] (splitAt-↑ʳ (lower k) (lower n) (lower i)) ⟩
                -- Sum.[ ... ] (Sum.inj₂ (lower i))
                --  ≡⟨⟩
                t ⟨$⟩ i
                ∎
              } } ;
    merge-parallel = record { merge-all = λ { {k , s} {n , t} g h →
          merge-parallel k  n X s t g h
        }
      }
    }
  where
    exfalso : ∀ {a : Level} {A : Set a} → Fin 0 → A
    exfalso ()



Setoids-Accessible : Accessible
Setoids-Accessible = record
               { Idx = ℕ̂
               ; fin = F̂
               ; fin-presentable = λ i → Fin-is-presentable (lower i)
               ; build-from-fin = canonical-cocone-is-limitting
               ; canonical-has-prop = λ X → canonical-cat-is-filtered X
               ; coproduct = λ A B _ _ →  BinaryCoproducts.coproduct (Cocartesian.coproducts (Setoids-Cocartesian {ℓ} {ℓ})) {A} {B}
               }
