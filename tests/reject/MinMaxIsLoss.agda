{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module MinMaxIsLoss where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Loss using (fin)
open import ResourceAlgebra.Instances.MinMax

-- Must fail: the bottleneck sequence keeps the worst hop; it does not add
-- the hops.  Accepting this would let a min-max bound be read as a
-- min-plus (loss) bound, which is the identification Separation S-4 and
-- the lax (not strict) loss-bottleneck morphism exist to forbid.
invalid : ∀ m n → (fin m ⊔g fin n) ≡ fin (m + n)
invalid m n = refl
