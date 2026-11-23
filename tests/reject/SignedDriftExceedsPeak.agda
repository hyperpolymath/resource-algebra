{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SignedDriftExceedsPeak where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Drift
open import ResourceAlgebra.Instances.SignedHWM

-- Must fail: signed drift may fall below zero, but a run still cannot end
-- holding more than its peak.  The bound is a field of the grade.
-- EXPECT: ⊤ !=< ⊥
invalid : Grade
invalid = shwm 0 (pk 1) tt
