-- A proof of NI for an encoding of DCC monad using
-- uninterpreted base types and constants
-- The calculus is parametrized by an infinite set of
-- type variables and an infinite set of typed konstants
module Calculus where

  open import Data.Empty
    using (⊥)
  open import Data.List
    using (List; []; _∷_)
  open import Data.List.Membership.Propositional              
    using (_∈_)
  open import Data.List.Relation.Unary.Any
    using (here; there)
  open import Data.Product
    using (_,_; _×_; proj₁; proj₂)
  open import Function
    using (_∘_)
  open import Data.Unit
    using (⊤; tt)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)
  open import Data.Bool
    using (Bool; true; false; if_then_else_)
  open import Relation.Binary as R
    hiding (_⇒_; Rel)
  open import Level
    renaming (zero to ℓzero) hiding (suc)

  module Type (I : Set) where

    infixl 5 _;_
    infixr 6 _⇒_
    infixr 7 _∧_

    -- A type with I free variables
    data Ty : Set where
      bool : Ty
      _⇒_  : (a b : Ty) → Ty
      _∧_  : (a b : Ty) → Ty
      unit : Ty
      X    : I → Ty

    -- A context Γ is a list of types
    Ctx : Set
    Ctx = List Ty

    pattern _;_ xs x = x ∷ xs

  open Type

  -- I is the set of base types,
  -- J is the set of constants, and
  -- K is the function assigning the type K j to the constant j
  module Calculus (I : Set) (J : Set) (K : J → Ty I) where

    infix  2 _⊢_

    variable
      A B C : Ty I
      Γ Γ'  : Ctx I

    -- terms
    data _⊢_ (Γ : Ctx I) : Ty I → Set where

        var : A ∈ Γ
            -------
            → Γ ⊢ A 

        lam : Γ ; A ⊢ B
            -----------
            → Γ ⊢ A ⇒ B

        app : Γ ⊢ A ⇒ B → Γ ⊢ A
            -------------------
            →       Γ ⊢ B

        true false : --------
                     Γ ⊢ bool

        ifte : Γ ⊢ bool → Γ ⊢ A → Γ ⊢ A
             --------------------------
             →          Γ ⊢ A

        fst : Γ ⊢ A ∧ B
            -----------
            →   Γ ⊢ A
        
        snd : Γ ⊢ A ∧ B
            -----------
            →   Γ ⊢ B

        prd : Γ ⊢ A → Γ ⊢ B 
            ---------------
            →   Γ ⊢ A ∧ B

        unit :
              --------
              Γ ⊢ unit

        konst : (j : J)
              ---------
              → Γ ⊢ K j

    b0 : A ∈ Γ ; A
    b0 = here refl

    b1 : A ∈ Γ ; A ; B
    b1 = there b0

    b2 : A ∈ Γ ; A ; B ; C
    b2 = there b1

    v0 : Γ ; A ⊢ A
    v0 = var b0

    v1 : Γ ; A ; B ⊢ A
    v1 = var b1

    v2 : Γ ; A ; B ; C ⊢ A
    v2 = var b2

    -- "security monad"
    T : Ty I → Ty I → Ty I
    T ℓ A = ℓ ⇒ A
    
    private
      variable
        i : I
        ℓ ℓ' : Ty I

    return : Γ ⊢ A ⇒ T ℓ A
    return = lam (lam v1)

    let* :  Γ ⊢ T ℓ A ⇒ (A ⇒ T ℓ B) ⇒ T ℓ B
    let* = lam (lam (lam (app (app v1 (app v2 v0)) v0)))

    comm : Γ ⊢ T ℓ (T ℓ' A) ⇒ T ℓ' (T ℓ A)
    comm = lam (lam (lam (app (app v2 v0) v1)))

  -- standard interpretation
  module Standard (I : Set) (⟦_⟧TyVar : I → Set) where

    ⟦_⟧Ty : Ty I → Set
    ⟦ bool  ⟧Ty = Bool
    ⟦ A ⇒ B ⟧Ty = ⟦ A ⟧Ty → ⟦ B ⟧Ty
    ⟦ A ∧ B ⟧Ty = ⟦ A ⟧Ty × ⟦ B ⟧Ty
    ⟦ unit  ⟧Ty = ⊤
    ⟦ X x   ⟧Ty = ⟦ x ⟧TyVar

    ⟦_⟧Ctx : Ctx I → Set
    ⟦ []    ⟧Ctx = ⊤
    ⟦ Γ ; A ⟧Ctx = ⟦ Γ ⟧Ctx × ⟦ A ⟧Ty

    ⟦_⟧Var : ∀ {A} {Γ} → A ∈ Γ → ⟦ Γ ⟧Ctx → ⟦ A ⟧Ty
    ⟦ here refl ⟧Var = proj₂
    ⟦ there x   ⟧Var = ⟦ x ⟧Var ∘ proj₁

    module Term (J : Set) (K : J → Ty I) (⟦_⟧K : ∀ (j : J) → ⟦ K j ⟧Ty) where

      open Calculus I J K

      ⟦_⟧Tm : Γ ⊢ A →  ⟦ Γ ⟧Ctx → ⟦ A ⟧Ty
      ⟦ var x        ⟧Tm = ⟦ x ⟧Var
      ⟦ lam t        ⟧Tm = λ γ → λ x → ⟦ t ⟧Tm (γ , x)
      ⟦ app t u      ⟧Tm = λ γ → ⟦ t ⟧Tm γ (⟦ u ⟧Tm γ)
      ⟦ true         ⟧Tm = λ γ → true
      ⟦ false        ⟧Tm = λ γ → false
      ⟦ ifte t t₁ t₂ ⟧Tm = λ γ → if ⟦ t ⟧Tm γ then ⟦ t₁ ⟧Tm γ else ⟦ t₂ ⟧Tm γ
      ⟦ fst t        ⟧Tm = λ γ → proj₁ (⟦ t ⟧Tm γ)
      ⟦ snd t        ⟧Tm = λ γ → proj₂ (⟦ t ⟧Tm γ)
      ⟦ prd t₁ t₂    ⟧Tm = λ γ → ⟦ t₁ ⟧Tm γ , ⟦ t₂ ⟧Tm γ 
      ⟦ unit         ⟧Tm = λ γ → tt
      ⟦ konst k      ⟧Tm = λ _ → ⟦ k ⟧K

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
  module Relational (I : Set) (⟦_⟧TyVar₁ : I → Set)
                              (⟦_⟧TyVar₂ : I → Set)
                              (⟦_⟧TyVarRel : ∀ (i : I) → Rel (⟦ i ⟧TyVar₁)  (⟦ i ⟧TyVar₂))
                              where

    open Standard I ⟦_⟧TyVar₁ renaming (⟦_⟧Ty to ⟦_⟧Ty₁; ⟦_⟧Ctx to ⟦_⟧Ctx₁; ⟦_⟧Var to ⟦_⟧Var₁; module Term to Term₁)
    open Standard I ⟦_⟧TyVar₂ renaming (⟦_⟧Ty to ⟦_⟧Ty₂; ⟦_⟧Ctx to ⟦_⟧Ctx₂; ⟦_⟧Var to ⟦_⟧Var₂; module Term to Term₂)

    ⟦_⟧Ty : (A : Ty I) → Rel (⟦ A ⟧Ty₁) (⟦ A ⟧Ty₂)
    ⟦ bool  ⟧Ty = BoolRel
    ⟦ A ⇒ B ⟧Ty = ⟦ A ⟧Ty →Rel ⟦ B ⟧Ty
    ⟦ A ∧ B ⟧Ty = ⟦ A ⟧Ty ×Rel  ⟦ B ⟧Ty
    ⟦ unit  ⟧Ty = ⊤Rel
    ⟦ X x   ⟧Ty = ⟦ x ⟧TyVarRel

    ⟦_⟧Ctx : (Γ : Ctx I) → Rel (⟦ Γ ⟧Ctx₁) (⟦ Γ ⟧Ctx₂)
    ⟦ []    ⟧Ctx = ⊤Rel
    ⟦ Γ ; A ⟧Ctx = ⟦ Γ ⟧Ctx ×Rel ⟦ A ⟧Ty

    ⟦_⟧Var : ∀ {A} {Γ} {γ₁ :  ⟦ Γ ⟧Ctx₁} {γ₂ : ⟦ Γ ⟧Ctx₂}
              → (A∈Γ : A ∈ Γ)
              → ⟦ Γ ⟧Ctx γ₁ γ₂
              → ⟦ A ⟧Ty (⟦ A∈Γ ⟧Var₁ γ₁) (⟦ A∈Γ ⟧Var₂ γ₂)
    ⟦ here refl ⟧Var = proj₂
    ⟦ there x   ⟧Var = ⟦ x  ⟧Var ∘ proj₁

    module Term (J : Set) (K : J → Ty I)
                          (⟦_⟧K₁   : ∀ (j : J) → ⟦ K j ⟧Ty₁)
                          (⟦_⟧K₂   : ∀ (j : J) → ⟦ K j ⟧Ty₂)
                          (⟦_⟧KRel : ∀ (j : J) → ⟦ K j ⟧Ty ⟦ j ⟧K₁ ⟦ j ⟧K₂)
                              where

      open Calculus I J K
      open Term₁ J K ⟦_⟧K₁ renaming (⟦_⟧Tm to ⟦_⟧Tm₁) public
      open Term₂ J K ⟦_⟧K₂ renaming (⟦_⟧Tm to ⟦_⟧Tm₂) public

      -- Reynolds abstraction theorem
      ⟦_⟧Tm : ∀ {Γ} {A} {γ₁ : ⟦ Γ ⟧Ctx₁} {γ₂ : ⟦ Γ ⟧Ctx₂}
              → (t : Γ ⊢ A)
              → ⟦ Γ ⟧Ctx γ₁ γ₂ → ⟦ A ⟧Ty (⟦ t ⟧Tm₁ γ₁) (⟦ t ⟧Tm₂ γ₂)
      ⟦_⟧Tm (var x)                 γ₁Rγ₂ = ⟦ x ⟧Var γ₁Rγ₂
      ⟦_⟧Tm (lam t)                 γ₁Rγ₂ = λ γ₁Rγ₂' → ⟦ t ⟧Tm (γ₁Rγ₂ , γ₁Rγ₂')
      ⟦_⟧Tm (app t u)               γ₁Rγ₂ = ⟦ t ⟧Tm γ₁Rγ₂ (⟦ u ⟧Tm γ₁Rγ₂)
      ⟦_⟧Tm true                    γ₁Rγ₂ = refl
      ⟦_⟧Tm false                   γ₁Rγ₂ = refl
      ⟦_⟧Tm {_} {A} (ifte b t₁ t₂)  γ₁Rγ₂ = ifteRel {R = ⟦ A ⟧Ty} (⟦ b ⟧Tm  γ₁Rγ₂) (⟦ t₁ ⟧Tm γ₁Rγ₂) (⟦ t₂ ⟧Tm γ₁Rγ₂)
      ⟦_⟧Tm {_} {A} (fst {B = B} t) γ₁Rγ₂ = proj₁Rel {R₁ = ⟦ A ⟧Ty} {R₂ = ⟦ B ⟧Ty} (⟦ t ⟧Tm γ₁Rγ₂)
      ⟦_⟧Tm {_} {B} (snd {A = A} t) γ₁Rγ₂ = proj₂Rel {R₁ = ⟦ A ⟧Ty} {R₂ = ⟦ B ⟧Ty} (⟦ t ⟧Tm γ₁Rγ₂)
      ⟦_⟧Tm (prd t u)               γ₁Rγ₂ = ⟦ t ⟧Tm γ₁Rγ₂ , ⟦ u ⟧Tm γ₁Rγ₂
      ⟦_⟧Tm unit                    γ₁Rγ₂ = tt
      ⟦_⟧Tm {_} {A} (konst k)       γ₁Rγ₂ = ⟦ k ⟧KRel

  -- example of NI in the two-point lattice
  module TwoPoint where

    -- two element set
    data Two : Set where
      1' 2' : Two

    -- three element set
    data Three : Set where
      1' 2' 3' : Three

    L : Ty Two
    L = X 1'

    H : Ty Two
    H = X 2' 

    ⟦_⟧H : Two → Set
    ⟦_⟧H _ = ⊤

    ⟦_⟧HRel : ∀ (v : Two) → Rel (⟦ v ⟧H)  (⟦ v ⟧H)
    ⟦_⟧HRel _ _ _ = ⊥

    L⊑H : Ty Two
    L⊑H = L ⇒ H

    L⊑L : Ty Two
    L⊑L = L ⇒ L

    H⊑H : Ty Two
    H⊑H = H ⇒ H

    K : Three → Ty Two
    K 1' = L⊑H 
    K 2' = L⊑L
    K 3' = H⊑H 

    open Calculus Two Three K
    open Standard Two ⟦_⟧H using (⟦_⟧Ty)

    ⟦_⟧K : ∀ j → ⟦ K j ⟧Ty
    ⟦ 1' ⟧K = λ _ → tt
    ⟦ 2' ⟧K = λ _ → tt
    ⟦ 3' ⟧K = λ _ → tt

    open Relational Two ⟦_⟧H ⟦_⟧H ⟦_⟧HRel renaming (⟦_⟧Ty to ⟦_⟧TyRel)

    ⟦_⟧KRel : ∀ j → ⟦ K j ⟧TyRel ⟦ j ⟧K ⟦ j ⟧K
    ⟦ 1' ⟧KRel = λ x → x
    ⟦ 2' ⟧KRel = λ x → x
    ⟦ 3' ⟧KRel = λ x → x

    open Term Three K ⟦_⟧K ⟦_⟧K ⟦_⟧KRel

    -- non-interference follows from the abstraction theorem
    ni : ∀ (t : [] ; T H bool ⊢ bool)
         → (s₁ s₂ : [] ⊢ T H bool)
         → (⟦ t ⟧Tm₁ (tt , ⟦ s₁ ⟧Tm₁ tt) ≡ ⟦ t ⟧Tm₂ (tt , ⟦ s₂ ⟧Tm₂ tt))
    ni t s₁ s₂ = ⟦ t ⟧Tm (tt , s₁Rs₂)
       where
         s₁Rs₂ : ⟦ T H bool ⟧TyRel (⟦ s₁ ⟧Tm₂ tt) (⟦ s₂ ⟧Tm₂ tt)
         s₁Rs₂ ()
