{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module DriftExceedsPeak where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.HWM

-- Must fail: a run cannot end holding more live state than its peak.  The
-- invariant is a field of the grade, so no such grade can be written down.
-- EXPECT: suc .* != zero of type Nat
invalid : Grade
invalid = hwm 1 2 (s≤s (s≤s z≤n))
