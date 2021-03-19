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
    using (_,_; _×_; <_,_>; proj₁; proj₂)
  open import Function
    using (id; _∘_)
  open import Data.Unit
    using (⊤; tt)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)
    renaming (isEquivalence to ≡-isEquivalence)
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

  -- I is the set of base types,
  -- J is the set of constants, and
  -- K is the function assigning the type K j to the constant j
  module Calculus (P : Preorder ℓzero ℓzero ℓzero) where

    infix  2 _⊢_

    open Preorder P renaming (_∼_ to _⊑_) hiding (refl)
    open Type Carrier

    variable
      a b c : Ty
      Γ Γ'  : Ctx

    -- terms
    data _⊢_ (Γ : Ctx) : Ty → Set where

        var : a ∈ Γ
            -------
            → Γ ⊢ a

        lam : Γ ; a ⊢ b
            -----------
            → Γ ⊢ a ⇒ b

        app : Γ ⊢ a ⇒ b → Γ ⊢ a
            -------------------
            →       Γ ⊢ b

        true false : --------
                     Γ ⊢ bool

        ifte : Γ ⊢ bool → Γ ⊢ a → Γ ⊢ a
             --------------------------
             →          Γ ⊢ a

        fst : Γ ⊢ a ∧ b
            -----------
            →   Γ ⊢ a

        snd : Γ ⊢ a ∧ b
            -----------
            →   Γ ⊢ b

        prd : Γ ⊢ a → Γ ⊢ b
            ---------------
            →   Γ ⊢ a ∧ b

        unit :
              --------
              Γ ⊢ unit

        coe : ∀ {i j : Carrier} → i ⊑ j
              ------------------------
              → Γ ⊢ X i ⇒ X j

    b0 : a ∈ Γ ; a
    b0 = here refl

    b1 : a ∈ Γ ; a ; b
    b1 = there b0

    b2 : a ∈ Γ ; a ; b ; c
    b2 = there b1

    v0 : Γ ; a ⊢ a
    v0 = var b0

    v1 : Γ ; a ; b ⊢ a
    v1 = var b1

    v2 : Γ ; a ; b ; c ⊢ a
    v2 = var b2

    -- "security monad"
    T : Ty → Ty → Ty
    T ℓ a = ℓ ⇒ a
    
    private
      variable
        ℓ ℓ' : Ty

    return : Γ ⊢ a ⇒ T ℓ a
    return = lam (lam v1)

    let* :  Γ ⊢ T ℓ a ⇒ (a ⇒ T ℓ b) ⇒ T ℓ b
    let* = lam (lam (lam (app (app v1 (app v2 v0)) v0)))

    comm : Γ ⊢ T ℓ (T ℓ' a) ⇒ T ℓ' (T ℓ a)
    comm = lam (lam (lam (app (app v2 v0) v1)))

  -- standard interpretation
  module Standard (P : Preorder ℓzero ℓzero ℓzero)
                  (let open Preorder P renaming (_∼_ to _⊑_) hiding (refl))
                  (⟦_⟧TyVar : Carrier → Set) where

    open Type Carrier

    ⟦_⟧Ty : Ty → Set
    ⟦ bool  ⟧Ty = Bool
    ⟦ a ⇒ b ⟧Ty = ⟦ a ⟧Ty → ⟦ b ⟧Ty
    ⟦ a ∧ b ⟧Ty = ⟦ a ⟧Ty × ⟦ b ⟧Ty
    ⟦ unit  ⟧Ty = ⊤
    ⟦ X i   ⟧Ty = ⟦ i ⟧TyVar

    ⟦_⟧Ctx : Ctx → Set
    ⟦ []    ⟧Ctx = ⊤
    ⟦ Γ ; a ⟧Ctx = ⟦ Γ ⟧Ctx × ⟦ a ⟧Ty

    module Term (⟦_⟧Coe : ∀ {i j} → i ⊑ j → ⟦ i ⟧TyVar → ⟦ j ⟧TyVar) where

      open Calculus P

      ⟦_⟧Var : a ∈ Γ → ⟦ Γ ⟧Ctx → ⟦ a ⟧Ty
      ⟦ here refl ⟧Var = proj₂
      ⟦ there x   ⟧Var = ⟦ x ⟧Var ∘ proj₁

      ⟦_⟧Tm : Γ ⊢ a →  ⟦ Γ ⟧Ctx → ⟦ a ⟧Ty
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
      ⟦ coe i⊑j      ⟧Tm = λ γ → ⟦ i⊑j ⟧Coe

  private
    variable
      A A' B B' C D : Set

  -- relational model
  Rel : Set → Set → Set₁
  Rel A B = R.REL {a = ℓzero} {b = ℓzero} A B ℓzero

  _→-rel_ : Rel A B → Rel C D → Rel (A → C) (B → D)
  _→-rel_  {A} {B} R₁ R₂ f g = ∀ {a : A} {b : B} → R₁ a b → R₂ (f a) (g b)

  -- Dom <--- Grf ---> Cod
  record Rel₀ : Set₁ where
    constructor ⟨_⟩
    field
      {Dom} : Set
      {Cod} : Set
      Grf   : Rel Dom Cod

  -- R₀ <-- R --> R₁
  --  |     |     |
  -- dom   prs   cod
  --  |     |     |
  --  v     v     v
  -- S₀ <-- S --> S₁
  record Rel₁ (X : Rel₀) (Y : Rel₀) : Set where
    constructor ⟨_⟩
    open Rel₀ X renaming (Dom to R₀; Cod to R₁; Grf to R)
    open Rel₀ Y renaming (Dom to S₀; Cod to S₁; Grf to S)
    field
      {dom} : R₀ → S₀
      {cod} : R₁ → S₁
      prs   : _→-rel_ R S dom cod

  open Rel₀
  open Rel₁

  private
    variable
      R R' R'' S S' : Rel₀

  idRel : Rel₁ R R
  idRel .dom = id
  idRel .cod = id
  idRel .prs = id

  _∘Rel_ : Rel₁ R' R'' → Rel₁ R R' → Rel₁ R R''
  _∘Rel_ f g .dom = f .dom ∘ g .dom
  _∘Rel_ f g .cod = f .cod ∘ g .cod
  _∘Rel_ f g .prs = f .prs ∘ g .prs

  -- Product of relations
  _×-rel_ : Rel A B → Rel C D → Rel (A × C) (B × D)
  _×-rel_ R S (a , c) (b , d) = R a b × S c d

  _×Rel_ : Rel₀ → Rel₀ → Rel₀
  _×Rel_ R S .Dom = R .Dom × S .Dom
  _×Rel_ R S .Cod = R .Cod × S .Cod
  _×Rel_ R S .Grf = R .Grf ×-rel S .Grf

  prdRel : Rel₁ R S → Rel₁ R S' → Rel₁ R (S ×Rel S')
  prdRel f g .dom = < f .dom , g .dom >
  prdRel f g .cod = < f .cod , g .cod >
  prdRel f g .prs = < f .prs , g .prs >

  proj₁Rel : {R S : Rel₀} → Rel₁ (R ×Rel S) R
  proj₁Rel .dom = proj₁
  proj₁Rel .cod = proj₁
  proj₁Rel .prs = proj₁

  proj₂Rel : {R S : Rel₀} → Rel₁ (R ×Rel S) S
  proj₂Rel .dom = proj₂
  proj₂Rel .cod = proj₂
  proj₂Rel .prs = proj₂

  fstRel : Rel₁ R (S ×Rel S') → Rel₁ R S
  fstRel = proj₁Rel ∘Rel_

  sndRel : Rel₁ R (S ×Rel S') → Rel₁ R S'
  sndRel = proj₂Rel ∘Rel_

  -- Exponential of relations
  _→Rel_ : Rel₀ → Rel₀ → Rel₀
  _→Rel_ R₁ R₂ .Dom = R₁ .Dom → R₂ .Dom
  _→Rel_ R₁ R₂ .Cod = R₁ .Cod → R₂ .Cod
  _→Rel_ R₁ R₂ .Grf = R₁ .Grf →-rel R₂ .Grf

  absRel : Rel₁ (R ×Rel S') S → Rel₁ R (S' →Rel S)
  absRel f .dom = λ r s → f .dom (r , s)
  absRel f .cod = λ r s → f .cod (r , s)
  absRel f .prs = λ r s → f .prs (r , s)

  appRel : Rel₁ R (S' →Rel S) → Rel₁ R S' → Rel₁ R S
  appRel f x .dom = λ r → f .dom r (x .dom r)
  appRel f x .cod = λ r → f .cod r (x .cod r)
  appRel f x .prs = λ r → f .prs r (x .prs r)

  evalRel : Rel₁ ((S' →Rel S) ×Rel S') S
  evalRel = appRel proj₁Rel proj₂Rel

  -- Terminal relation
  ⊤Rel : Rel₀
  ⊤Rel .Dom = ⊤
  ⊤Rel .Cod = ⊤
  ⊤Rel .Grf = λ _ _ → ⊤

  ttRel : Rel₁ R ⊤Rel
  ttRel .dom _ = tt
  ttRel .cod _ = tt
  ttRel .prs _ = tt

  -- Boolean relation
  BoolRel : Rel₀
  BoolRel .Dom = Bool
  BoolRel .Cod = Bool
  BoolRel .Grf = _≡_

  trueRel : Rel₁ R BoolRel
  trueRel .dom _ = true
  trueRel .cod _ = true
  trueRel .prs _ = refl

  falseRel : Rel₁ R BoolRel
  falseRel .dom _ = false
  falseRel .cod _ = false
  falseRel .prs _ = refl

  ifteRel : Rel₁ R BoolRel → Rel₁ R S → Rel₁ R S → Rel₁ R S
  ifteRel b t e .dom r = if b .dom r then t .dom r else e .dom r
  ifteRel b t e .cod r = if b .cod r then t .cod r else e .cod r
  ifteRel b t e .prs {r₀} {r₁} r₀Rr₁ with b .dom r₀ | b .cod r₁ | b .prs r₀Rr₁
  ... | true  | .true  | refl = t .prs r₀Rr₁
  ... | false | .false | refl = e .prs r₀Rr₁

  caseRel : Rel₁ R S → Rel₁ R S → Rel₁ (R ×Rel BoolRel) S
  caseRel t e = ifteRel proj₂Rel (t ∘Rel proj₁Rel) (e ∘Rel proj₁Rel)

  -- relational interpretation of the calculus
  module Relational (P : Preorder ℓzero ℓzero ℓzero)
                    (let open Preorder P renaming (_∼_ to _⊑_) hiding (refl))
                    (⟦_⟧TyVar₁ : Carrier → Set)
                    (⟦_⟧TyVar₂ : Carrier → Set)
                    (⟦_⟧TyVarRel : ∀ (i : Carrier) → Rel (⟦ i ⟧TyVar₁)  (⟦ i ⟧TyVar₂))
                    where

    open Type Carrier
    open Standard P ⟦_⟧TyVar₁ renaming (⟦_⟧Ty to ⟦_⟧Ty₁; ⟦_⟧Ctx to ⟦_⟧Ctx₁; module Term to Term₁)
    open Standard P ⟦_⟧TyVar₂ renaming (⟦_⟧Ty to ⟦_⟧Ty₂; ⟦_⟧Ctx to ⟦_⟧Ctx₂; module Term to Term₂)

    ⟦_⟧Ty : (a : Ty) → Rel (⟦ a ⟧Ty₁) (⟦ a ⟧Ty₂)
    ⟦ bool  ⟧Ty = BoolRel .Grf
    ⟦ a ⇒ b ⟧Ty = (⟨ ⟦ a ⟧Ty ⟩ →Rel ⟨ ⟦ b ⟧Ty ⟩) .Grf
    ⟦ a ∧ b ⟧Ty = (⟨ ⟦ a ⟧Ty ⟩ ×Rel ⟨ ⟦ b ⟧Ty ⟩) .Grf
    ⟦ unit  ⟧Ty = ⊤Rel .Grf
    ⟦ X x   ⟧Ty = ⟦ x ⟧TyVarRel

    ⟦_⟧Ctx : (Γ : Ctx) → Rel (⟦ Γ ⟧Ctx₁) (⟦ Γ ⟧Ctx₂)
    ⟦ []    ⟧Ctx = ⊤Rel .Grf
    ⟦ Γ ; a ⟧Ctx = (⟨ ⟦ Γ ⟧Ctx ⟩ ×Rel ⟨ ⟦ a ⟧Ty ⟩) .Grf

    module Term  (⟦_⟧Coe₁ : ∀ {i j} → i ⊑ j → ⟦ i ⟧TyVar₁ → ⟦ j ⟧TyVar₁)
                 (⟦_⟧Coe₂ : ∀ {i j} → i ⊑ j → ⟦ i ⟧TyVar₂ → ⟦ j ⟧TyVar₂)
                 (⟦_⟧CoeRel : ∀ {i j} → (i⊑j : i ⊑ j) → (⟦ X i ⟧Ty →-rel ⟦ X j ⟧Ty) ⟦ i⊑j ⟧Coe₁ ⟦ i⊑j ⟧Coe₂)
                 where

      open Calculus P
      open Term₁ ⟦_⟧Coe₁ renaming (⟦_⟧Tm to ⟦_⟧Tm₁; ⟦_⟧Var to ⟦_⟧Var₁) public
      open Term₂ ⟦_⟧Coe₂ renaming (⟦_⟧Tm to ⟦_⟧Tm₂; ⟦_⟧Var to ⟦_⟧Var₂) public

      ⟦_⟧Var : ∀ {γ₁ : ⟦ Γ ⟧Ctx₁} {γ₂ : ⟦ Γ ⟧Ctx₂}
                → (a∈Γ : a ∈ Γ)
                → ⟦ Γ ⟧Ctx γ₁ γ₂
                → ⟦ a ⟧Ty (⟦ a∈Γ ⟧Var₁ γ₁) (⟦ a∈Γ ⟧Var₂ γ₂)
      ⟦ here refl ⟧Var = proj₂
      ⟦ there x   ⟧Var = ⟦ x  ⟧Var ∘ proj₁

      -- Reynolds abstraction theorem
      ⟦_⟧Tm : ∀ {γ₁ : ⟦ Γ ⟧Ctx₁} {γ₂ : ⟦ Γ ⟧Ctx₂}
               → (t : Γ ⊢ a)
               → ⟦ Γ ⟧Ctx γ₁ γ₂ → ⟦ a ⟧Ty (⟦ t ⟧Tm₁ γ₁) (⟦ t ⟧Tm₂ γ₂)
      ⟦_⟧Tm {_} (var x)            γ₁Rγ₂ = ⟦ x ⟧Var                                                                                       γ₁Rγ₂
      ⟦_⟧Tm {Γ} (lam {a} {b} t)    γ₁Rγ₂ = absRel    {R = ⟨ ⟦ Γ ⟧Ctx ⟩} {S' = ⟨ ⟦ a ⟧Ty ⟩} {S = ⟨ ⟦ b ⟧Ty ⟩} ⟨ ⟦ t ⟧Tm ⟩             .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} (app {a} {b} t u)  γ₁Rγ₂ = appRel    {R = ⟨ ⟦ Γ ⟧Ctx ⟩}                    {S = ⟨ ⟦ b ⟧Ty ⟩} ⟨ ⟦ t ⟧Tm ⟩ ⟨ ⟦ u ⟧Tm ⟩ .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} true               γ₁Rγ₂ = trueRel   {R = ⟨ ⟦ Γ ⟧Ctx ⟩}                                                              .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} false              γ₁Rγ₂ = falseRel  {R = ⟨ ⟦ Γ ⟧Ctx ⟩}                                                              .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} (ifte {a} b t u)   γ₁Rγ₂ = ifteRel   {R = ⟨ ⟦ Γ ⟧Ctx ⟩} {S = ⟨ ⟦ a ⟧Ty ⟩} ⟨ ⟦ b ⟧Tm ⟩ ⟨ ⟦ t ⟧Tm ⟩ ⟨ ⟦ u ⟧Tm ⟩        .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} (fst {a} {b} t)    γ₁Rγ₂ = fstRel    {R = ⟨ ⟦ Γ ⟧Ctx ⟩} {S = ⟨ ⟦ a ⟧Ty ⟩} {S' = ⟨ ⟦ b ⟧Ty ⟩} ⟨ ⟦ t ⟧Tm ⟩             .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} (snd {a} {b} t)    γ₁Rγ₂ = sndRel    {R = ⟨ ⟦ Γ ⟧Ctx ⟩} {S = ⟨ ⟦ a ⟧Ty ⟩} {S' = ⟨ ⟦ b ⟧Ty ⟩} ⟨ ⟦ t ⟧Tm ⟩             .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} (prd {a} {b} t u)  γ₁Rγ₂ = prdRel    {R = ⟨ ⟦ Γ ⟧Ctx ⟩} {S = ⟨ ⟦ a ⟧Ty ⟩} {S' = ⟨ ⟦ b ⟧Ty ⟩} ⟨ ⟦ t ⟧Tm ⟩ ⟨ ⟦ u ⟧Tm ⟩ .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} unit               γ₁Rγ₂ = ttRel     {R = ⟨ ⟦ Γ ⟧Ctx ⟩}                                                              .prs γ₁Rγ₂
      ⟦_⟧Tm {Γ} (coe i⊑j)          γ₁Rγ₂ = ⟦ i⊑j ⟧CoeRel

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
    open Type LH
    open Calculus LH-Preorder

    ⟦H⟧ : LH → Set
    ⟦H⟧ _ = ⊤

    ⟦H⟧Rel : ∀ ℓ → Rel (⟦H⟧ ℓ) (⟦H⟧ ℓ)
    ⟦H⟧Rel _ = λ x y → ⊥

    ⟦coe⟧ : l ⊑ l' → ⟦H⟧ l → ⟦H⟧ l'
    ⟦coe⟧ L⊑H = λ _ → tt
    ⟦coe⟧ ⊑-refl = λ x → x

    ⟦coe⟧Rel : (l⊑l' : l ⊑ l') →  (⟦H⟧Rel l →-rel ⟦H⟧Rel l') (⟦coe⟧ l⊑l') (⟦coe⟧ l⊑l')
    ⟦coe⟧Rel _ ()

    module Rel-LH = Relational LH-Preorder ⟦H⟧ ⟦H⟧ ⟦H⟧Rel
    open Rel-LH
    open Rel-LH.Term ⟦coe⟧ ⟦coe⟧ ⟦coe⟧Rel

    H' = X H 

    -- non-interference follows from the abstraction theorem
    ni : ∀ (t : T H' bool ∷ [] ⊢ bool)
         → (s₁ s₂ : [] ⊢ T H' bool)
         → (⟦ t ⟧Tm₁ (tt , (⟦ s₁ ⟧Tm₁ tt))) ≡ (⟦ t ⟧Tm₂ (tt , (⟦ s₂ ⟧Tm₂ tt)))
    ni t s₁ s₂ = ⟦ t ⟧Tm (tt , s₁Rs₂)
       where
         s₁Rs₂ : ⟦ T H' bool ⟧Ty (⟦ s₁ ⟧Tm₂ tt) (⟦ s₂ ⟧Tm₂ tt)
         s₁Rs₂  ()
