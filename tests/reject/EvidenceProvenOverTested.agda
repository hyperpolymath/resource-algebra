{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EvidenceProvenOverTested where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Evidence
open import ResourceAlgebra.Ledger

-- Must fail: a claim proved on top of a property that is only tested is not
-- proven.  Accepting this would let a ledger report a row as stronger than
-- the weakest step it rests on (README-EXPLAINME rule 3), which is the
-- overstatement Ledger.eff-greatest exists to rule out.
-- EXPECT: tested-only != proven of type Status
invalid : eff (row proven (0 ∷ []) ∷ row tested-only [] ∷ []) 0 ≡ proven
invalid = refl
