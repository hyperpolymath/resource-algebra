{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SHWMSyncAbove where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Drift
open import ResourceAlgebra.Instances.SignedHWM
open import ResourceAlgebra.Parallel

x : Grade
x = shwm 1 0d tt

-- Must fail: as in HWM (P-4), two threads of peak 1, one before the
-- meeting and one after it, hold 1 when they meet in the middle and are
-- graded 2 running free (Parallel.SHWM-not-sync-above).
-- EXPECT: 2 != 1 of type Nat
invalid : peak (((x ⊗s 𝟙s) ∥s (𝟙s ⊗s x)) ⊕s ((x ∥s 𝟙s) ⊗s (𝟙s ∥s x)))
        ≡ peak ((x ∥s 𝟙s) ⊗s (𝟙s ∥s x))
invalid = refl
