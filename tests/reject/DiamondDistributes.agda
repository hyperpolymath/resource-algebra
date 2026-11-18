{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module DiamondDistributes where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Diamond

-- Must fail: the diamond lattice M3 is not distributive.  An atom met with
-- the join of the other two atoms is the atom itself (that join is the
-- top), while the join of the two meets is the bottom.  Accepting this
-- would make Diamond a dioid and leave C-4b without a witness.
-- EXPECT: a != bot of type Grade
invalid : a ⊓d (b ⊔d c) ≡ (a ⊓d b) ⊔d (a ⊓d c)
invalid = refl
