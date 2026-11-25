{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SpanSyncBelow where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.MaxPlus
open import ResourceAlgebra.Parallel

-- Must fail: with parallel = max, threads that meet in the middle take
-- longer than threads that run free (1 ∥ 0 then 0 ∥ 1 takes 2, not 1).
-- Accepting this would give elapsed time the exchange law of a space-like
-- resource (Parallel.MaxPlus-span-not-sync-below).
-- EXPECT: 2 != 1 of type Nat
invalid : tAdd (tMul (tPar (val 1) (val 0)) (tPar (val 0) (val 1)))
               (tPar (tMul (val 1) (val 0)) (tMul (val 0) (val 1)))
        ≡ tPar (tMul (val 1) (val 0)) (tMul (val 0) (val 1))
invalid = refl
