{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- A proof-ledger row's status is derived, not asserted: a row is only as
-- strong as the weakest step it depends on (README-EXPLAINME "Proof Ledger",
-- rule 3).  In the Evidence algebra that is sequencing: the derived status
-- of a row is its own evidence in sequence (⊓e) with the derived statuses
-- of the rows it depends on.
--
-- A ledger is a list of rows, newest first.  Row 0 is the head; row i + 1
-- is row i of the tail.  A row's dependencies are indices into the rows
-- after it, so a row can depend only on older rows and no dependency cycle
-- can be written.  An index past the end names no row, and the derivation
-- reads it as proven (𝟙).  So any reader of a ledger must refuse such a
-- dangling reference, as an unregistered row ID, before it derives a
-- status.  That is a precondition every reader must enforce, not a
-- guarantee given here: no reader exists yet, and the theorems below hold
-- for every ledger, dangling references included.
--
-- Proved:
--   eff-≼-own    the derived status is no stronger than the row's evidence;
--   eff-≼-dep    nor than any row it depends on;
--   eff-≼-reach  nor than the evidence of any row it reaches;
--   eff-respects the derived assignment respects the ledger;
--   eff-greatest every assignment that respects the ledger is below it.
-- So eff is the strongest status the ledger supports, and a recorded status
-- above it is an overstatement.
--
-- Every relation is defined by recursion on lists and ℕ, not as an indexed
-- family, so the canonical profile checks without a warning.
module ResourceAlgebra.Ledger where

open import Agda.Builtin.List public using (List; []; _∷_)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Evidence
open ResourceAlgebra Evidence using (_≼_; ≼-refl; ≼-trans)

----------------------------------------------------------------------
-- Lists
map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Membership, by recursion.
_∈_ : Nat → List Nat → Set
j ∈ []       = ⊥
j ∈ (k ∷ ks) = (j ≡ k) ⊎ (j ∈ ks)

-- The meet of a list of statuses; the empty meet is proven.
⨅ : List Status → Status
⨅ []       = proven
⨅ (s ∷ ss) = s ⊓e ⨅ ss

⨅-lower : {f : Nat → Status} (js : List Nat) {j : Nat} → j ∈ js → ⨅ (map f js) ≼ f j
⨅-lower {f} (k ∷ ks) (inj₁ refl) = ⊓e-lowerˡ (f k) (⨅ (map f ks))
⨅-lower {f} (k ∷ ks) (inj₂ p)    = ≼-trans (⊓e-lowerʳ (f k) (⨅ (map f ks))) (⨅-lower ks p)

⨅-greatest : {f : Nat → Status} {z : Status} (js : List Nat)
           → (∀ {j} → j ∈ js → z ≼ f j) → z ≼ ⨅ (map f js)
⨅-greatest {z = z} []       _ = ≼-proven z
⨅-greatest         (k ∷ ks) h = ⊓e-greatest (h (inj₁ refl)) (⨅-greatest ks (λ p → h (inj₂ p)))

----------------------------------------------------------------------
-- Ledgers
record Row : Set where
  constructor row
  field
    own  : Status      -- the §5 token of the row's own artefact
    deps : List Nat    -- the rows it depends on, as indices into the rows after it
open Row

Ledger : Set
Ledger = List Row

own-of : Ledger → Nat → Status
own-of []      _       = proven
own-of (r ∷ L) zero    = own r
own-of (r ∷ L) (suc i) = own-of L i

-- Dep L i j: row i depends directly on row j.
Dep : Ledger → Nat → Nat → Set
Dep []      _       _       = ⊥
Dep (r ∷ L) zero    zero    = ⊥
Dep (r ∷ L) zero    (suc j) = j ∈ deps r
Dep (r ∷ L) (suc i) zero    = ⊥
Dep (r ∷ L) (suc i) (suc j) = Dep L i j

-- Reach L i j: row i depends on row j through zero or more steps.
data Reach (L : Ledger) (i : Nat) : Nat → Set where
  stay : Reach L i i
  step : ∀ {k j} → Dep L i k → Reach L k j → Reach L i j

-- The derived status.
eff : Ledger → Nat → Status
eff []      _       = proven
eff (r ∷ L) zero    = own r ⊓e ⨅ (map (eff L) (deps r))
eff (r ∷ L) (suc i) = eff L i

----------------------------------------------------------------------
-- Soundness: never stronger than the evidence it rests on
eff-≼-own : ∀ L i → eff L i ≼ own-of L i
eff-≼-own []      i       = ≼-refl proven
eff-≼-own (r ∷ L) zero    = ⊓e-lowerˡ (own r) (⨅ (map (eff L) (deps r)))
eff-≼-own (r ∷ L) (suc i) = eff-≼-own L i

eff-≼-dep : ∀ L i j → Dep L i j → eff L i ≼ eff L j
eff-≼-dep []      _       _       ()
eff-≼-dep (r ∷ L) zero    zero    ()
eff-≼-dep (r ∷ L) zero    (suc j) p =
  ≼-trans (⊓e-lowerʳ (own r) (⨅ (map (eff L) (deps r)))) (⨅-lower (deps r) p)
eff-≼-dep (r ∷ L) (suc i) zero    ()
eff-≼-dep (r ∷ L) (suc i) (suc j) d = eff-≼-dep L i j d

-- A row is only as strong as the weakest step it depends on.
eff-≼-reach : ∀ L {i j} → Reach L i j → eff L i ≼ own-of L j
eff-≼-reach L {i} stay               = eff-≼-own L i
eff-≼-reach L {i} (step {k} {j} d r) = ≼-trans (eff-≼-dep L i k d) (eff-≼-reach L r)

----------------------------------------------------------------------
-- Maximality: the strongest status the ledger supports

-- An assignment respects a ledger when no row is stronger than its own
-- evidence or than a row it depends on.
record Respects (L : Ledger) (s : Nat → Status) : Set where
  field
    below-own : ∀ i → s i ≼ own-of L i
    below-dep : ∀ i j → Dep L i j → s i ≼ s j
open Respects

eff-respects : ∀ L → Respects L (eff L)
eff-respects L = record { below-own = eff-≼-own L ; below-dep = eff-≼-dep L }

-- Restricting an assignment of r ∷ L to L keeps it respectful.
restrict : ∀ {r L s} → Respects (r ∷ L) s → Respects L (λ i → s (suc i))
restrict ρ = record
  { below-own = λ i → below-own ρ (suc i)
  ; below-dep = λ i j d → below-dep ρ (suc i) (suc j) d }

eff-greatest : ∀ L s → Respects L s → ∀ i → s i ≼ eff L i
eff-greatest []      s ρ i       = ≼-proven (s i)
eff-greatest (r ∷ L) s ρ zero    =
  ⊓e-greatest (below-own ρ zero)
    (⨅-greatest (deps r)
      (λ {j} p → ≼-trans (below-dep ρ zero (suc j) p)
                         (eff-greatest L (λ k → s (suc k)) (restrict ρ) j)))
eff-greatest (r ∷ L) s ρ (suc i) = eff-greatest L (λ k → s (suc k)) (restrict ρ) i
