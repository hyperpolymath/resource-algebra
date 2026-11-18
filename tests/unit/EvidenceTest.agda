{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EvidenceTest where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Evidence
open import ResourceAlgebra.Ledger

module EV = ResourceAlgebra Evidence

-- The record's units and operations are part of the consumer contract.
zero-is-open : EV.𝟘 ≡ open-row
zero-is-open = refl

one-is-proven : EV.𝟙 ≡ proven
one-is-proven = refl

-- The owner's chain (2026-11-17): argued is above tested-only, so a step
-- that is argued and one that is tested-only together are tested-only, and
-- either one alone is the better support for a claim.
sequence-keeps-the-weaker : (argued EV.⊗ tested-only) ≡ tested-only
sequence-keeps-the-weaker = refl

alternative-keeps-the-stronger : (argued EV.⊕ tested-only) ≡ argued
alternative-keeps-the-stronger = refl

postulates-below-proven : (proven EV.⊗ proven-with-postulates) ≡ proven-with-postulates
postulates-below-proven = refl

open-annihilates : (proven EV.⊗ open-row) ≡ open-row
open-annihilates = refl

-- A worked ledger, newest first.  Rows, oldest first: 0, a theorem proved
-- about a model; 1, the argued link from the model to the code; 2, a
-- code-level claim proved against the model, resting on rows 0 and 1;
-- 3, a property checked by tests; 4, a claim proved on top of rows 2 and 3.
-- Indices count back from each row: 0 is the row just before it.
example : Ledger
example =
    row proven (0 ∷ 1 ∷ [])     -- row 4: on row 3 and row 2
  ∷ row tested-only []          -- row 3
  ∷ row proven (0 ∷ 1 ∷ [])     -- row 2: on row 1 and row 0
  ∷ row argued []               -- row 1
  ∷ row proven []               -- row 0
  ∷ []

-- Row 2 is argued: a proof about the model is only as good as the argued
-- link to the code (README-EXPLAINME rule 3).
row2-is-argued : eff example 2 ≡ argued
row2-is-argued = refl

-- Row 4 is tested-only: the weakest step it rests on.
row4-is-tested-only : eff example 0 ≡ tested-only
row4-is-tested-only = refl

-- Row 0 rests on nothing, so it keeps its own evidence.
row0-keeps-its-evidence : eff example 4 ≡ proven
row0-keeps-its-evidence = refl
