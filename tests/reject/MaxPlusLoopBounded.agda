{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module MaxPlusLoopBounded where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.MaxPlus

-- Must fail: no finite cost n bounds a loop whose body costs 1, because
-- one more turn costs suc n.  Accepting this would give MaxPlus a loop
-- grade it does not have (Star.MaxPlus-no-fixpoint).
-- EXPECT: suc n != n of type Nat
invalid : ∀ n → tAdd (val 0) (tMul (val 1) (val n)) ≡ val n
invalid n = refl
