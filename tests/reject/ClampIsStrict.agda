{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ClampIsStrict where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.HWM using (_⊗h_)
open import ResourceAlgebra.Instances.SignedHWM

-- Must fail: reading negative drift as 0 forgets the cell that was freed,
-- so the clamped sequence peaks at 1 where the sequence peaks at 0.
-- clampG is lax, not strict (Morphism.clamp-not-strict).
-- EXPECT: 0 != 1 of type Nat
invalid : clampG (free-one ⊗s alloc-one) ≡ clampG free-one ⊗h clampG alloc-one
invalid = refl
