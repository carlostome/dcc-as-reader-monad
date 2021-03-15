module Reader where

  open import Data.Empty                                      using (⊥-elim; ⊥)
  open import Data.List                                       using (List; []; _∷_; _++_; [_])
  open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
  open import Data.Product                                    using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
  open import Data.Unit                                       using (⊤; tt)
  open import Relation.Binary.PropositionalEquality           using (_≡_; refl; cong; sym) renaming (subst to ≡-subst)
  open import Data.Bool

  module Calculus (ℒ : Set) where

    data Ty : Set where
        bool : Ty
        _⇒_  : (a b : Ty) → Ty
        𝕓    : ℒ → Ty
    
    infixr 3 _⇒_

    -- A context Γ is a list of types
    Ctx : Set
    Ctx = List Ty

    data _∈_ (A : Ty) : Ctx → Set where
      here : ∀ {Γ} → A ∈ (A ∷ Γ)
      there : ∀ {B Γ} → A ∈ Γ → A ∈ (B ∷ Γ)

    private
      variable
        A B : Ty

    -- terms
    data _⊢_ (Γ : Ctx) : Ty → Set where

        var : A ∈ Γ
            --------
            → Γ ⊢ A 

        lam : (A ∷ Γ) ⊢ B
            ---------------
            → Γ ⊢ (A ⇒ B)

        app : Γ ⊢ (A ⇒ B) → Γ ⊢ A
            ----------------------
            →       Γ ⊢ B

        true false : --------
                     Γ ⊢ bool

        ifte : Γ ⊢ bool → Γ ⊢ A → Γ ⊢ A
             ----------------------------
             →       Γ ⊢ A

  module Standard (ℒ : Set) (⟦ℒ⟧ : ℒ → Set) where
    open import Data.Product
    open Calculus ℒ

    ⟦_⟧Ty : Ty → Set
    ⟦ bool ⟧Ty = Bool
    ⟦ A ⇒ B ⟧Ty = ⟦ A ⟧Ty → ⟦ B ⟧Ty
    ⟦ 𝕓 ℓ ⟧Ty = ⟦ℒ⟧ ℓ

    ⟦_⟧Ctx : Ctx → Set
    ⟦ [] ⟧Ctx = ⊤
    ⟦ A ∷ Γ ⟧Ctx = (⟦ A ⟧Ty) × (⟦ Γ ⟧Ctx)

    lookupCtx : ∀ {A} {Γ} → A ∈ Γ → ⟦ Γ ⟧Ctx → ⟦ A ⟧Ty
    lookupCtx here (t , _) = t
    lookupCtx (there x) (_ , Γ) = lookupCtx x Γ

    ⟦_⟧Tm : ∀ {Γ} {A} → Γ ⊢ A →  ⟦ Γ ⟧Ctx → ⟦ A ⟧Ty
    ⟦ var x ⟧Tm = lookupCtx x
    ⟦ lam t ⟧Tm = λ γ → λ x → ⟦ t ⟧Tm (x , γ)
    ⟦ app t u ⟧Tm = λ γ → ⟦ t ⟧Tm γ (⟦ u ⟧Tm γ)
    ⟦ true ⟧Tm = λ γ → true
    ⟦ false ⟧Tm = λ γ → false
    ⟦ ifte t t₁ t₂ ⟧Tm = λ γ → if ⟦ t ⟧Tm γ then ⟦ t₁ ⟧Tm γ else ⟦ t₂ ⟧Tm γ

  -- relational model
  Rel : Set → Set → Set₁
  Rel A B = A → B → Set

  -- Arrow of relations
  _→Rel_ : ∀ {A B C D : Set} → Rel A B → Rel C D → Rel (A → C) (B → D)
  _→Rel_  {A} {B} R₁ R₂ f g = ∀ (a : A) (b : B) → R₁ a b → R₂ (f a) (g b) 

  -- Product of relations
  _×Rel_ : ∀ {A B C D : Set} → Rel A B → Rel C D → Rel (A × C) (B × D)
  _×Rel_ R₁ R₂ (a , c) (b , d) = (R₁ a b) × (R₂ c d)

  -- Terminal relation
  ⊤Rel : ∀ {A B : Set} → Rel A B
  ⊤Rel _ _ = ⊤

  -- relational interpretation of the calculus
  module Relational (ℒ : Set) (⟦ℒ⟧₁ : ℒ → Set) (⟦ℒ⟧₂ : ℒ → Set) (⟦ℒ⟧Rel : ∀ b → Rel (⟦ℒ⟧₁ b) (⟦ℒ⟧₂ b)) where
    open Calculus ℒ
    open Standard ℒ ⟦ℒ⟧₁ renaming (⟦_⟧Ty to ⟦_⟧Ty₁; ⟦_⟧Ctx to ⟦_⟧Ctx₁; ⟦_⟧Tm to ⟦_⟧Tm₁; lookupCtx to lookup₁) public
    open Standard ℒ ⟦ℒ⟧₂ renaming (⟦_⟧Ty to ⟦_⟧Ty₂; ⟦_⟧Ctx to ⟦_⟧Ctx₂; ⟦_⟧Tm to ⟦_⟧Tm₂; lookupCtx to lookup₂) public

    ⟦_⟧Ty : (A : Ty) → Rel (⟦ A ⟧Ty₁) (⟦ A ⟧Ty₂)
    ⟦ bool ⟧Ty = _≡_
    ⟦ A ⇒ B ⟧Ty = (⟦ A ⟧Ty) →Rel (⟦ B ⟧Ty)
    ⟦ 𝕓 ℓ ⟧Ty = ⟦ℒ⟧Rel ℓ

    ⟦_⟧Ctx : (Γ : Ctx) → Rel (⟦ Γ ⟧Ctx₁) (⟦ Γ ⟧Ctx₂)
    ⟦ [] ⟧Ctx = ⊤Rel
    ⟦ A ∷ Γ ⟧Ctx = (⟦ A ⟧Ty) ×Rel (⟦ Γ ⟧Ctx)

    lookupCtx : ∀ {A} {Γ} → (A∈Γ : A ∈ Γ) → (γ₁ :  ⟦ Γ ⟧Ctx₁) → (γ₂ : ⟦ Γ ⟧Ctx₂)
                 → ⟦ Γ ⟧Ctx γ₁ γ₂
                 → ⟦ A ⟧Ty (lookup₁ A∈Γ γ₁) (lookup₂ A∈Γ γ₂)
    lookupCtx here (t₁ , _) (t₂ , γ₂) (p , _) = p
    lookupCtx (there x) (_ , Γ₁) (_ , Γ₂) (_ , p) = lookupCtx x Γ₁ Γ₂ p

    abstr : ∀ {Γ} {A} → (t : Γ ⊢ A)
              → ∀ (γ₁ : ⟦ Γ ⟧Ctx₁) (γ₂ : ⟦ Γ ⟧Ctx₂)
              → ⟦ Γ ⟧Ctx γ₁ γ₂ → ⟦ A ⟧Ty (⟦ t ⟧Tm₁ γ₁) (⟦ t ⟧Tm₂ γ₂)
    abstr (var x) γ₁ γ₂ γ₁Rγ₂ = lookupCtx x γ₁ γ₂ γ₁Rγ₂
    abstr (lam t) γ₁ γ₂ γ₁Rγ₂ = λ a b γ₁Rγ₂' → abstr t (a , γ₁) (b , γ₂) (γ₁Rγ₂' , γ₁Rγ₂)
    abstr (app t u) γ₁ γ₂ γ₁Rγ₂ with abstr t γ₁ γ₂ γ₁Rγ₂ | abstr u γ₁ γ₂ γ₁Rγ₂
    ... | t' | u' = t' (⟦ u ⟧Tm₁ γ₁) (⟦ u ⟧Tm₂ γ₂) u'
    abstr true γ₁ γ₂ γ₁Rγ₂ = refl
    abstr false γ₁ γ₂ γ₁Rγ₂ = refl
    abstr (ifte t t₁ t₂) γ₁ γ₂ γ₁Rγ₂ with ⟦ t ⟧Tm₁ γ₁ | ⟦ t ⟧Tm₂ γ₂ | abstr t γ₁ γ₂ γ₁Rγ₂
    ... | false | .false | refl = abstr t₂ γ₁ γ₂ γ₁Rγ₂
    ... | true | .true | refl   = abstr t₁ γ₁ γ₂ γ₁Rγ₂

  -- example of NI in the two-point lattice
  module TwoPoint where

    data LH : Set where
      L H : LH

    open Calculus LH

    Labeled : LH → Ty → Ty
    Labeled ℓ A = 𝕓 ℓ ⇒ A

    ⟦H⟧ : LH → Set
    ⟦H⟧ = λ { L → ⊤
           ; H → ⊤}

    ⟦H⟧Rel : ∀ ℓ → Rel (⟦H⟧ ℓ) (⟦H⟧ ℓ)
    ⟦H⟧Rel L = λ x y → ⊥
    ⟦H⟧Rel H = λ x y → ⊥

    upLH : Ty
    upLH = 𝕓 L ⇒ 𝕓 H

    ⟦upLH⟧ : ⟦H⟧ L → ⟦H⟧ H
    ⟦upLH⟧ = λ _ → tt

    open Relational LH ⟦H⟧ ⟦H⟧ ⟦H⟧Rel

    -- non-interference follows from the abstraction theorem
    ni : ∀ (t : (upLH ∷ Labeled H bool ∷ []) ⊢ bool)
         → ∀ (s₁ s₂ : (upLH ∷ []) ⊢ Labeled H bool)
         → (⟦ t ⟧Tm₁ (⟦upLH⟧ , ((⟦ s₁ ⟧Tm₁ (⟦upLH⟧ , tt)) , tt))) ≡ (⟦ t ⟧Tm₂ (⟦upLH⟧ , ((⟦ s₂ ⟧Tm₂ (⟦upLH⟧ , tt)) , tt)))
    ni t s₁ s₂ = abstr t (⟦upLH⟧ , ((⟦ s₁ ⟧Tm₁ (⟦upLH⟧ , tt)) , tt))
                         (⟦upLH⟧ , (⟦ s₂ ⟧Tm₂ (⟦upLH⟧ , tt) , tt))
                         (⟦upLH⟧R⟦upLH⟧ , (s₁Rs₂ , tt))
       where
         s₁Rs₂ : ⟦ Labeled H bool ⟧Ty (⟦ s₁ ⟧Tm₂ (⟦upLH⟧ , tt)) (⟦ s₂ ⟧Tm₂ (⟦upLH⟧ , tt))
         s₁Rs₂ a b ()

         ⟦upLH⟧R⟦upLH⟧ : ⟦ upLH ⟧Ty ⟦upLH⟧ ⟦upLH⟧
         ⟦upLH⟧R⟦upLH⟧ = λ a b ()
