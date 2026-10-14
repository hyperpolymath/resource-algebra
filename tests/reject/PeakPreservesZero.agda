{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module PeakPreservesZero where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.HWM using (HWM)
open import ResourceAlgebra.Instances.MaxPlus using (MaxPlus)
open import ResourceAlgebra.Morphism using (LaxHom; peak-lax)

-- Must fail: LaxHom only provides a bound for zero, not strict zero
-- preservation. The zero HWM grade maps to val 0, not MaxPlus's bot.
-- EXPECT: != ResourceAlgebra\.Instances\.MaxPlus\.bot of type
invalid : LaxHom.map peak-lax (ResourceAlgebra.𝟘 HWM) ≡ ResourceAlgebra.𝟘 MaxPlus
invalid = refl
