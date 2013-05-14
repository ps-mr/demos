-- Introduction
-- ============

-- Agda is an implementation of Martin-Löf type theory,
-- so it is both a programming language and a proof
-- assistant.

-- PART I • Programming in Agda
-- ============================

-- To program in Agda, use emacs. The agda-mode is so
-- good that you can't do without it.

-- Programming in Agda is very much like programming
-- in Haskell. We start with a module statement.

module intro where

-- After we entered some code, we can use C-c C-l to
-- load it. We either get an error or the file gets
-- colored.

-- Agda uses layout, so all top-level declarations in
-- this module have to be aligned at the same column.

-- We can import files. “import” is for bringing a
-- module from a different file into scope, and “open”
-- is for bringing the contents of that module into
-- scope.

open import Data.Nat

-- We can define datatypes. The syntax is similar to
-- generalized algebraic data types in Haskell,
-- that is, we give the type of each constructor.

data List (A : Set) : Set where
  ∅ : List A
  _,_ : (x : A) -> (xs : List A) -> List A

-- Use “\emptyset” to enter “∅”, “\to” to enter “→”, …

-- The name of the cons constructor is “_,_”. That
-- is one identifier. The underscores mark the
-- position where the arguments can occur. So we
-- can use either “_,_ a b” or “a , b”.

-- The names “x” and “xs” for the arguments of “_,_”
-- are used for automatic case splits, see below.

-- We specify the fixity of constructors, similar to
-- Haskell:

infixr 3 _,_

-- Here's some test data.

test-123 : List ℕ
test-123 = 1 , 2 , 3 , ∅

-- And a function:

map : ∀ {A B} → (A → B) → (List A → List B)
map f ∅ = ∅
map f (x , xs) = f x , map f xs

-- The braces “{” and “}” mark implicit arguments,
-- at abstraction and call sites. At call sites,
-- missing implicit arguments are inferred.
--
-- The notation “∀ {A B} →” means “{A : _} {B : _} →”
--
-- Agda can help us develop this definition.
-- Start with:
--
--   map : ∀ {A B} → (A → B) → (List A → List B)
--   map = ?
--
-- Load the file (C-c C-l). The “?” is replaced
-- by a hole. The second buffer shows the type of
-- the term required in this hole. We can keep
-- programming and fill that hole later, or work
-- on it now.
--
-- Change the part before the hole to:
--
--   map f xs =
--
-- Reload (C-c C-l) and note that the type of
-- the hole changes.
--
-- We want to implement map by pattern matching
-- on “xs”. Enter “xs” into the hole and ask for
-- a case split (C-c C-c).
--
-- Some commands for holes:
--
--   • Automatically fill hole (C-c C-a)
--     - hole can contain names of lemmas to try
--   • Refine hole (C-c C-r)
--     - if hole empty: try introduction forms
--     - if hole contains term: try that term
--   • Case split (C-c C-c)
--     - hole has to contain name of variable
--   • Give term (C-c C-space)
--     - hole has to contain exact term to use

-- PART II • Proving Stuff
-- =======================

-- Equality: The smallest binary relation that is
-- reflective.

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {a} → a ≡ a

-- This is a meta-circular definition of equality:
-- We can use “refl” to prove “a ≡ b” if and only
-- if “a” and “b” are convertible. That is,
-- β-convertible. In particular, we cannot prove
-- equality of functions by extensionality.

-- We prove a congruence lemma.

cong₂ : ∀ {A B C} {x₁ x₂ y₁ y₂} (f : A → B → C) →
  (x₁ ≡ x₂) → (y₁ ≡ y₂) → (f x₁ y₁ ≡ f x₂ y₂)
cong₂ f refl refl = refl

-- This works because pattern matching on equality
-- proofs triggers unification. This is the same
-- kind of type refinement you also see in GADT
-- pattern matching in Haskell or pattern matching
-- in Scala. In Agda, it actually works.

-- (This is also a difference between Coq and Agda:
-- In Coq, dependent pattern matching doesn't work
-- so well. Instead, one uses the “inversion” tactic)

-- Now, we can prove map fusion. We have to build
-- extensionality into the statement, because it is
-- not available for our definition of equality,
-- as mentioned above.

map-fusion : ∀ {A B C} {f : B → C} {g : A → B} →
  ∀ xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
map-fusion ∅ = refl
map-fusion (x , xs)
  = cong₂ _,_ refl (map-fusion xs)

-- In practice, you can start writing “map-fusion”,
-- and add the definitions of “_≡_” and “cong₂” later,
-- using holes.

