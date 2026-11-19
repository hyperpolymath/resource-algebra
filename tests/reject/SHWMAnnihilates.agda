{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SHWMAnnihilates where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Drift
open import ResourceAlgebra.Instances.SignedHWM

-- Must fail: a run of peak 1 followed by 𝟘 still reached peak 1, so 𝟘 does
-- not absorb on the right (SHWM-seq-𝟘, SHWM-not-annihilating).  It does
-- absorb on the left (SHWM-absorbˡ).
-- EXPECT: 1 != 0 of type Nat
invalid : peak (shwm 1 0d tt ⊗s 𝟘s) ≡ peak 𝟘s
invalid = refl
