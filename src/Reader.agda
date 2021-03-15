module Reader where

  open import Data.Empty                                      using (⊥-elim; ⊥)
  open import Data.List                                       using (List; []; _∷_; _++_; [_])
  open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
  open import Data.Product                                    using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
  open import Function
  open import Data.Unit                                       using (⊤; tt)
  open import Relation.Binary.PropositionalEquality           using (_≡_; refl; cong; sym) renaming (subst to ≡-subst; isEquivalence to ≡-isEquivalence )
  open import Data.Bool hiding (T)
  open import Relation.Binary hiding (_⇒_; Rel)
  open import Level renaming (zero to ℓzero)

  module Calculus (P : Preorder ℓzero ℓzero ℓzero) where
    open Preorder P renaming (Carrier to ℒ; _∼_ to _⊑_)

    data Ty : Set where
      bool : Ty
      _⇒_  : (a b : Ty) → Ty
      𝕓    : ℒ → Ty

    infix  4 _∈_
    infixr 3 _⇒_
    infix  2 _⊢_

    -- A context Γ is a list of types
    Ctx : Set
    Ctx = List Ty

    data _∈_ (A : Ty) : Ctx → Set where
      here : ∀ {Γ} → A ∈ (A ∷ Γ)
      there : ∀ {B Γ} → A ∈ Γ → A ∈ (B ∷ Γ)

    private
      variable
        ℓ ℓ' : ℒ
        A B C : Ty
        Γ Γ'  : Ctx

    -- terms
    data _⊢_ (Γ : Ctx) : Ty → Set where

        var : A ∈ Γ
            --------
            → Γ ⊢ A 

        lam : A ∷ Γ ⊢ B
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

        coe : ℓ ⊑ ℓ'
            -----------------
            → Γ ⊢ 𝕓 ℓ ⇒ 𝕓 ℓ'

    b0 : A ∈ A ∷ Γ
    b0 = here

    b1 : A ∈ B ∷ A ∷ Γ
    b1 = there b0

    b2 : A ∈ C ∷ B ∷ A ∷ Γ
    b2 = there b1

    v0 : A ∷ Γ ⊢ A
    v0 = var b0

    v1 : B ∷ A ∷ Γ ⊢ A
    v1 = var b1

    v2 : C ∷ B ∷ A ∷ Γ ⊢ A
    v2 = var b2

    T : ℒ → Ty → Ty
    T ℓ A = 𝕓 ℓ ⇒ A

    return : Γ ⊢ A ⇒ T ℓ A
    return = lam (lam v1)

    let* :  Γ ⊢ T ℓ A ⇒ (A ⇒ T ℓ B) ⇒ T ℓ B
    let* = lam (lam (lam (app (app v1 (app v2 v0)) v0)))

    comm : Γ ⊢ T ℓ (T ℓ' A) ⇒ T ℓ' (T ℓ A)
    comm = lam (lam (lam (app (app v2 v0) v1)))

  module Standard (P : Preorder ℓzero ℓzero ℓzero)
                  (let open Preorder P renaming (Carrier to ℒ; _∼_ to _⊑_))
                  (⟦ℒ⟧ : ℒ → Set)
                  (⟦coe⟧ : ∀ {ℓ ℓ'} → ℓ ⊑ ℓ' → ⟦ℒ⟧ ℓ → ⟦ℒ⟧ ℓ') where

    open Calculus P

    ⟦_⟧Ty : Ty → Set
    ⟦ bool ⟧Ty = Bool
    ⟦ A ⇒ B ⟧Ty = ⟦ A ⟧Ty → ⟦ B ⟧Ty
    ⟦ 𝕓 ℓ ⟧Ty = ⟦ℒ⟧ ℓ

    ⟦_⟧Ctx : Ctx → Set
    ⟦ [] ⟧Ctx = ⊤
    ⟦ A ∷ Γ ⟧Ctx = (⟦ A ⟧Ty) × (⟦ Γ ⟧Ctx)

    ⟦_⟧Var : ∀ {A} {Γ} → A ∈ Γ → ⟦ Γ ⟧Ctx → ⟦ A ⟧Ty
    ⟦ here ⟧Var = proj₁
    ⟦ there x ⟧Var = ⟦ x ⟧Var ∘ proj₂

    ⟦_⟧Tm : ∀ {Γ} {A} → Γ ⊢ A →  ⟦ Γ ⟧Ctx → ⟦ A ⟧Ty
    ⟦ var x ⟧Tm = ⟦ x ⟧Var
    ⟦ lam t ⟧Tm = λ γ → λ x → ⟦ t ⟧Tm (x , γ)
    ⟦ app t u ⟧Tm = λ γ → ⟦ t ⟧Tm γ (⟦ u ⟧Tm γ)
    ⟦ true ⟧Tm = λ γ → true
    ⟦ false ⟧Tm = λ γ → false
    ⟦ ifte t t₁ t₂ ⟧Tm = λ γ → if ⟦ t ⟧Tm γ then ⟦ t₁ ⟧Tm γ else ⟦ t₂ ⟧Tm γ
    ⟦ coe ℓ⊑ℓ' ⟧Tm = λ _ → ⟦coe⟧ ℓ⊑ℓ'

  -- relational model
  Rel : Set → Set → Set₁
  Rel A B = A → B → Set

  private
    variable
      A B C D : Set

  -- Arrow of relations
  _→Rel_ : Rel A B → Rel C D → Rel (A → C) (B → D)
  _→Rel_  {A} {B} R₁ R₂ f g = ∀ {a : A} {b : B} → R₁ a b → R₂ (f a) (g b) 

  -- Product of relations
  _×Rel_ : Rel A B → Rel C D → Rel (A × C) (B × D)
  _×Rel_ R₁ R₂ (a , c) (b , d) = (R₁ a b) × (R₂ c d)

  proj₁Rel : {R₁ : Rel A B} {R₂ : Rel C D} → ((R₁ ×Rel R₂) →Rel R₁) proj₁ proj₁
  proj₁Rel = proj₁

  proj₂Rel : {R₁ : Rel A B} {R₂ : Rel C D} → ((R₁ ×Rel R₂) →Rel R₂) proj₂ proj₂
  proj₂Rel = proj₂

  -- Terminal relation
  ⊤Rel : ∀ {A B : Set} → Rel A B
  ⊤Rel _ _ = ⊤

  BoolRel : Rel Bool Bool
  BoolRel = _≡_

  ifteRel : ∀ {R : Rel A B} {b b'} {t₁ t₂ t₁' t₂'}
              → BoolRel b b' → R t₁ t₁' → R t₂ t₂' → R (if b then t₁ else t₂) (if b' then t₁' else t₂')
  ifteRel {b = true } refl r₁ r₂ = r₁
  ifteRel {b = false} refl r₁ r₂ = r₂

  -- relational interpretation of the calculus
  module Relational (P : Preorder ℓzero ℓzero ℓzero)
                    (let open Preorder P renaming (Carrier to ℒ; _∼_ to _⊑_) hiding (refl))
                    (⟦ℒ⟧₁ : ℒ → Set) (⟦ℒ⟧₂ : ℒ → Set) (⟦ℒ⟧Rel : ∀ ℓ → Rel (⟦ℒ⟧₁ ℓ) (⟦ℒ⟧₂ ℓ))
                    (⟦coe⟧₁ : ∀ {ℓ ℓ'} → ℓ ⊑ ℓ' → ⟦ℒ⟧₁ ℓ → ⟦ℒ⟧₁ ℓ')
                    (⟦coe⟧₂ : ∀ {ℓ ℓ'} → ℓ ⊑ ℓ' → ⟦ℒ⟧₂ ℓ → ⟦ℒ⟧₂ ℓ')
                    (⟦coe⟧Rel : ∀ {ℓ ℓ'} → (ℓ⊑ℓ' : ℓ ⊑ ℓ') → _→Rel_ (⟦ℒ⟧Rel ℓ) (⟦ℒ⟧Rel ℓ') (⟦coe⟧₁ ℓ⊑ℓ') (⟦coe⟧₂ ℓ⊑ℓ'))
                    where

    open Calculus P
    open Standard P ⟦ℒ⟧₁ ⟦coe⟧₁ renaming (⟦_⟧Ty to ⟦_⟧Ty₁; ⟦_⟧Ctx to ⟦_⟧Ctx₁; ⟦_⟧Tm to ⟦_⟧Tm₁; ⟦_⟧Var to ⟦_⟧Var₁) public
    open Standard P ⟦ℒ⟧₂ ⟦coe⟧₂ renaming (⟦_⟧Ty to ⟦_⟧Ty₂; ⟦_⟧Ctx to ⟦_⟧Ctx₂; ⟦_⟧Tm to ⟦_⟧Tm₂; ⟦_⟧Var to ⟦_⟧Var₂) public

    ⟦_⟧Ty : (A : Ty) → Rel (⟦ A ⟧Ty₁) (⟦ A ⟧Ty₂)
    ⟦ bool ⟧Ty = BoolRel
    ⟦ A ⇒ B ⟧Ty = (⟦ A ⟧Ty) →Rel (⟦ B ⟧Ty)
    ⟦ 𝕓 ℓ ⟧Ty = ⟦ℒ⟧Rel ℓ

    ⟦_⟧Ctx : (Γ : Ctx) → Rel (⟦ Γ ⟧Ctx₁) (⟦ Γ ⟧Ctx₂)
    ⟦ [] ⟧Ctx = ⊤Rel
    ⟦ A ∷ Γ ⟧Ctx = (⟦ A ⟧Ty) ×Rel (⟦ Γ ⟧Ctx)

    ⟦_⟧Var : ∀ {A} {Γ} {γ₁ :  ⟦ Γ ⟧Ctx₁} {γ₂ : ⟦ Γ ⟧Ctx₂}
              → (A∈Γ : A ∈ Γ)
              → ⟦ Γ ⟧Ctx γ₁ γ₂
              → ⟦ A ⟧Ty (⟦ A∈Γ ⟧Var₁ γ₁) (⟦ A∈Γ ⟧Var₂ γ₂)
    ⟦ here ⟧Var      = proj₁
    ⟦ (there x) ⟧Var = ⟦ x  ⟧Var ∘ proj₂

    -- Reynolds abstraction theorem
    ⟦_⟧Tm : ∀ {Γ} {A} {γ₁ : ⟦ Γ ⟧Ctx₁} {γ₂ : ⟦ Γ ⟧Ctx₂}
            → (t : Γ ⊢ A)
            → ⟦ Γ ⟧Ctx γ₁ γ₂ → ⟦ A ⟧Ty (⟦ t ⟧Tm₁ γ₁) (⟦ t ⟧Tm₂ γ₂)
    ⟦_⟧Tm (var x) γ₁Rγ₂   = ⟦ x ⟧Var γ₁Rγ₂
    ⟦_⟧Tm (lam t) γ₁Rγ₂   = λ γ₁Rγ₂' → ⟦ t ⟧Tm (γ₁Rγ₂' , γ₁Rγ₂)
    ⟦_⟧Tm (app t u) γ₁Rγ₂ = ⟦ t ⟧Tm γ₁Rγ₂ (⟦ u ⟧Tm γ₁Rγ₂)
    ⟦_⟧Tm true γ₁Rγ₂      = refl
    ⟦_⟧Tm false γ₁Rγ₂     = refl
    ⟦_⟧Tm {_} {A} (ifte b t₁ t₂) γ₁Rγ₂ = ifteRel {R = ⟦ A ⟧Ty} (⟦ b ⟧Tm  γ₁Rγ₂) (⟦ t₁ ⟧Tm γ₁Rγ₂) (⟦ t₂ ⟧Tm γ₁Rγ₂)
    ⟦_⟧Tm {_} {A} (coe ℓ⊑ℓ') γ₁Rγ₂ = ⟦coe⟧Rel ℓ⊑ℓ'

  -- example of NI in the two-point lattice
  module TwoPoint where

    data LH : Set where
      L H : LH

    private
      variable
        l l' l'' : LH
    data _⊑_ : LH → LH → Set where
      L⊑H    : L ⊑ H
      ⊑-refl : l ⊑ l

  
    ⊑-trans : Transitive (_⊑_)
    ⊑-trans x   ⊑-refl = x
    ⊑-trans ⊑-refl L⊑H = L⊑H

    LH-Preorder : Preorder ℓzero ℓzero ℓzero
    LH-Preorder = record { Carrier = LH
                         ; _≈_ = _≡_
                         ; _∼_ = _⊑_
                         ; isPreorder = record { isEquivalence = ≡-isEquivalence 
                                               ; reflexive = λ {refl → ⊑-refl}
                                               ; trans = ⊑-trans } }
    open Calculus LH-Preorder

    ⟦H⟧ : LH → Set
    ⟦H⟧ = λ { L → ⊤
           ; H → ⊤}

    ⟦H⟧Rel : ∀ ℓ → Rel (⟦H⟧ ℓ) (⟦H⟧ ℓ)
    ⟦H⟧Rel L = λ x y → ⊥
    ⟦H⟧Rel H = λ x y → ⊥

    ⟦coe⟧ : l ⊑ l' → ⟦H⟧ l → ⟦H⟧ l'
    ⟦coe⟧ L⊑H = λ _ → tt
    ⟦coe⟧ ⊑-refl = λ x → x

    ⟦coe⟧Rel : (l⊑l' : l ⊑ l') →  ((⟦H⟧Rel l) →Rel (⟦H⟧Rel l')) (⟦coe⟧ l⊑l') (⟦coe⟧ l⊑l')
    ⟦coe⟧Rel {L} ⊑-refl ()
    ⟦coe⟧Rel {H} ⊑-refl ()

    open Relational LH-Preorder ⟦H⟧ ⟦H⟧ ⟦H⟧Rel  ⟦coe⟧  ⟦coe⟧ ⟦coe⟧Rel 

    -- non-interference follows from the abstraction theorem
    ni : ∀ (t : T H bool ∷ [] ⊢ bool)
         → (s₁ s₂ : [] ⊢ T H bool)
         → (⟦ t ⟧Tm₁ ((⟦ s₁ ⟧Tm₁ tt) , tt)) ≡ (⟦ t ⟧Tm₂ ((⟦ s₂ ⟧Tm₂ tt) , tt))
    ni t s₁ s₂ = ⟦ t ⟧Tm (s₁Rs₂ , tt)
       where
         s₁Rs₂ : ⟦ T H bool ⟧Ty (⟦ s₁ ⟧Tm₂ tt) (⟦ s₂ ⟧Tm₂ tt)
         s₁Rs₂  ()
