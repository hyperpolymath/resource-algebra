{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module HWMAnnihilates where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.HWM

-- Must fail: in the high-water-mark algebra the ⊕-unit is also the
-- ⊗-unit, so sequencing with it returns the other grade, not 𝟘.  Accepting
-- this would smuggle an annihilating zero into an algebra that has none.
invalid : ∀ g → (𝟘h ⊗h g) ≡ 𝟘h
invalid (hwm p n b) = refl
