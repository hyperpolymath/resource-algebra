{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module PeakIsStrict where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.HWM
open import ResourceAlgebra.Instances.MaxPlus using (val; tMul)

-- Must fail: the peak of a sequence is max (peak a) (drift a + peak b),
-- not peak a + peak b.  Peak is only a LAX morphism HWM → MaxPlus
-- (Morphism.peak-lax: occupancy never exceeds cost); accepting this would
-- make it strict and let an occupancy bound stand in for a cost bound.
invalid : ∀ a b → val (peak (a ⊗h b)) ≡ tMul (val (peak a)) (val (peak b))
invalid (hwm p₁ n₁ b₁) (hwm p₂ n₂ b₂) = refl
