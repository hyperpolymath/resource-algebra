{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EvidenceArguedBelowTested where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Evidence

-- Must fail: the chain puts argued above tested-only (owner ruling
-- 2026-11-17), so a claim resting on one of each is tested-only.  Accepting
-- this would reverse the two in the order every ledger is derived in.
-- EXPECT: tested-only != argued of type Status
invalid : (argued ⊓e tested-only) ≡ argued
invalid = refl
