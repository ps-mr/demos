module stlc where

-- Syntax of Simple Types
--   (plus booleans)

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type
  bool : Type

-- Semantics of Simple Types
--   (plus booleans)

data Bool : Set where
  true false : Bool

⟦_⟧Type : Type → Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type
⟦ bool ⟧Type = Bool

-- Syntax of Typing Contexts

data Context : Set where
  ∅ : Context
  _•_ : Type → Context → Context

-- Semantics of Typing Contexts

-- this is just a unit type
data Empty : Set where
  ∅ : Empty

-- this is just a tuple type
data Bind (A B : Set) : Set where
  _•_ : A → B → Bind A B

⟦_⟧Context : Context → Set
⟦ ∅ ⟧Context = Empty
⟦ τ • Γ ⟧Context = Bind ⟦ τ ⟧Type ⟦ Γ ⟧Context

-- Syntax of (well-typed) Variables

-- (these are typed deBruijn indices)
data Var : Context → Type → Set where
  -- like zero
  this : ∀ {Γ τ} →
    Var (τ • Γ) τ

  -- like succ
  that : ∀ {Γ τ₁ τ₂} →
    Var Γ τ₂ →
    Var (τ₁ • Γ) τ₂

-- Semantics of (well-typed Variables)

-- this is lookup
⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ this ⟧Var (v • ρ) = v
⟦ that x ⟧Var (v • ρ) = ⟦ x ⟧Var ρ

-- Syntax of (well-typed) Terms

-- terms are represented as typing derivations
data Term : Context → Type → Set where
  app : ∀ {Γ τ₁ τ₂} →
    Term Γ (τ₁ ⇒ τ₂) →
    Term Γ τ₁ →
    Term Γ τ₂
  abs : ∀ {Γ τ₁ τ₂} →
    Term (τ₁ • Γ) τ₂ →
    Term Γ (τ₁ ⇒ τ₂)
  var : ∀ {Γ τ} →
    Var Γ τ →
    Term Γ τ
  true false : ∀ {Γ} →
    Term Γ bool
  if : ∀ {Γ τ} →
    Term Γ bool →
    Term Γ τ →
    Term Γ τ →
    Term Γ τ

-- Semantics of (well-typed Terms)

-- also a proof that STLC terminates

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ app t₁ t₂ ⟧Term ρ = ⟦ t₁ ⟧Term ρ (⟦ t₂ ⟧Term ρ)
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
⟦ true ⟧Term ρ = true
⟦ false ⟧Term ρ = false
⟦ if t₁ t₂ t₃ ⟧Term ρ with ⟦ t₁ ⟧Term ρ
... | true = ⟦ t₂ ⟧Term ρ
... | false = ⟦ t₃ ⟧Term ρ


-- NATURAL SEMANTICS
--   ( booleans not supported)

-- Syntax of values and environments

-- mutually recursive because we use closures
data Val : Type → Set
data Env : Context → Set

data Val where
  ⟨abs_,_⟩ : ∀ {Γ τ₁ τ₂} →
    Term (τ₁ • Γ) τ₂ → Env Γ → Val (τ₁ ⇒ τ₂)

data Env where
  ∅ : Env ∅
  _•_ : ∀ {Γ τ} → Val τ → Env Γ → Env (τ • Γ)

-- variable lookup

data _⊢_↦_ : ∀ {Γ τ} → Env Γ → Var Γ τ → Val τ → Set where
  this : ∀ {Γ τ} {v : Val τ} {ρ : Env (τ • Γ)} →
    (v • ρ) ⊢ this ↦ v
  that : ∀ {Γ τ τ′ ρ v′} {v : Val τ} {x : Var Γ τ′} → 
    ρ ⊢ x ↦ v′ →
    (v • ρ) ⊢ that x ↦ v′

-- evaluation

data _⊢_↓_ : ∀ {Γ τ} → Env Γ → Term Γ τ → Val τ → Set where
  abs : ∀ {Γ τ₁ τ₂ ρ} {t : Term (τ₁ • Γ) τ₂} →
    ρ ⊢ abs t ↓ ⟨abs t , ρ ⟩
  app : ∀ {Γ Γ′ τ₁ τ₂ ρ ρ′ v₂ v′}
    {t₁ : Term Γ (τ₁ ⇒ τ₂)} →
    {t₂ : Term Γ τ₁} →
    {t′ : Term (τ₁ • Γ′) τ₂} →
    ρ ⊢ t₁ ↓ ⟨abs t′ , ρ′ ⟩ →
    ρ ⊢ t₂ ↓ v₂ →
    (v₂ • ρ′) ⊢ t′ ↓ v′ →
    ρ ⊢ app t₁ t₂ ↓ v′
  var : ∀ {Γ τ ρ v} {x : Var Γ τ} →
    ρ ⊢ x ↦ v →
    ρ ⊢ var x ↓ v

-- Soundness of the natural semantics
-- with regard to the denotational semantics

-- basic idea:
--   if  ρ ⊢ t ↓ v  then  ⟦ t ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧

-- Meaning of Env and Val

⟦_⟧Env : ∀ {Γ} → Env Γ → ⟦ Γ ⟧Context
⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ ⟨abs t , ρ ⟩ ⟧Val = λ v → ⟦ t ⟧Term (v • ⟦ ρ ⟧Env)

-- we want Agda equivalence

open import Relation.Binary.PropositionalEquality

-- now prove soundness

↦-sound : ∀ {Γ τ ρ v} {x : Var Γ τ} →
  ρ ⊢ x ↦ v →
  ⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val
↦-sound this = refl
↦-sound (that ↦) = ↦-sound ↦

↓-sound : ∀ {Γ τ ρ v} {t : Term Γ τ} →
  ρ ⊢ t ↓ v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val
↓-sound abs = refl
↓-sound (app ↓₁ ↓₂ ↓′) =
  trans
    (cong₂ (λ x y → x y)
      (↓-sound ↓₁)
      (↓-sound ↓₂))
    (↓-sound ↓′)
↓-sound (var ↦) = ↦-sound ↦


