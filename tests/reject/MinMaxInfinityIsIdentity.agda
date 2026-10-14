{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module MinMaxInfinityIsIdentity where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Loss using (fin; inf)
open import ResourceAlgebra.Instances.MinMax using (_⊔g_)

-- Must fail: an unreachable sequential hop absorbs, even though infinity
-- is the identity for alternatives on the same carrier.
invalid : inf ⊔g fin 3 ≡ fin 3
invalid = refl
