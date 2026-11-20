{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SHWMZeroIsOne where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.SignedHWM

-- Must fail: with signed drift the unit of alternatives has drift −∞, so it
-- is not the unit of sequence (Instances.SignedHWM.SHWM-𝟘≢𝟙).  In HWM the
-- two are one grade.
-- EXPECT: Drift\.−∞ !=
invalid : 𝟘s ≡ 𝟙s
invalid = refl
