{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EvidenceArguedLinkIgnored where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Evidence
open import ResourceAlgebra.Ledger

-- Must fail: a theorem proved about a model, applied to the code through an
-- argued link, is argued, not proven.  A theorem about a model is proven for
-- the model only; the link from model to code is its own, weaker row.
-- EXPECT: argued != proven of type Status
invalid : eff (row proven (0 ∷ 1 ∷ []) ∷ row argued [] ∷ row proven [] ∷ []) 0 ≡ proven
invalid = refl
