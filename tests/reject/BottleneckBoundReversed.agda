{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module BottleneckBoundReversed where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss using (fin)
open import ResourceAlgebra.Instances.MinMax using (MinMax)

-- Must fail: the Loss → MinMax lax bound is 5 ≼ 3, since the induced
-- order reverses the numeric order. Reversing it would validate a bound
-- that the bottleneck map does not provide.
-- EXPECT: 3 != 5 of type Nat
invalid : ResourceAlgebra._≼_ MinMax (fin 3) (fin 5)
invalid = refl
