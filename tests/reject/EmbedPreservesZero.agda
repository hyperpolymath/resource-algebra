{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EmbedPreservesZero where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.HWM using (𝟘h)
open import ResourceAlgebra.Instances.SignedHWM

-- Must fail: HWM's 𝟘 is its 𝟙, and embed sends it to SHWM's 𝟙, not to its
-- 𝟘.  So embed is lax, not strict (Morphism.embed-𝟘, no-strict-HWM→SHWM).
-- EXPECT: != .*Drift\.−∞ of type
invalid : embed 𝟘h ≡ 𝟘s
invalid = refl
