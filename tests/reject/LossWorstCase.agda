{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module LossWorstCase where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss

-- Must fail: echo's alternatives are MIN (the less lossy branch), not MAX.
-- Reading them as worst-case would identify the loss grade with a cost
-- grade — the "informal loss number" the family map forbids.
-- EXPECT: min m n != max m n of type Nat
invalid : ∀ m n → (fin m ⊓g fin n) ≡ fin (max m n)
invalid m n = refl
