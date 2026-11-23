{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SHWMPrefixKeepsPeak where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.SignedHWM

-- Must fail: freeing one cell before allocating one leaves the sequence at
-- peak 0, below the peak 1 of the allocation alone.  In HWM a prefix never
-- lowers the peak (HWM-prefix-keeps-peak); with consumption it can
-- (prefix-lowers-peak).
-- EXPECT: 0 != 1 of type Nat
invalid : peak (free-one ⊗s alloc-one) ≡ peak alloc-one
invalid = refl
