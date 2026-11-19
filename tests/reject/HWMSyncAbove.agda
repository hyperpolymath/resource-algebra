{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module HWMSyncAbove where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.HWM
open import ResourceAlgebra.Parallel

x : Grade
x = hwm 1 0 z≤n

-- Must fail: two threads of peak 1, one before the meeting and one after
-- it, hold 1 when they meet in the middle and are graded 2 running free.
-- Accepting this would give occupancy the exchange law of a time-like
-- resource (Parallel.HWM-not-sync-above).
-- EXPECT: 2 != 1 of type Nat
invalid : peak (((x ⊗h 𝟘h) ∥h (𝟘h ⊗h x)) ⊕h ((x ∥h 𝟘h) ⊗h (𝟘h ∥h x)))
        ≡ peak ((x ∥h 𝟘h) ⊗h (𝟘h ∥h x))
invalid = refl
