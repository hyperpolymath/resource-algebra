{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Computed witnesses that the three instances are not interchangeable.
-- Each is `refl` plus a decidable inequality on ℕ, so each is TESTED by the
-- typechecker's evaluator, not argued in prose.  They discharge, as checked
-- facts, three boundary sentences the family map currently states only in
-- words:
--   S-1  "an occupancy bound is not a cost bound"           (nextgen-typing)
--   S-2  "an informal loss number cannot stand in for the
--         structure" — echo alternatives are MIN, tropical MAX (nextgen-typing)
--   S-3  the ⊕-induced order runs opposite ways in Loss and MaxPlus
module ResourceAlgebra.Separation where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss    as L
open import ResourceAlgebra.Instances.MaxPlus as M
open import ResourceAlgebra.Instances.HWM     as H

----------------------------------------------------------------------
-- S-1  Sequencing peaks 2 and 3 (nothing held between them):
--      occupancy gives 3, cost gives 5.
two three : H.Grade
two   = hwm 2 0 z≤n
three = hwm 3 0 z≤n

hwm-seq : peak (two ⊗h three) ≡ 3
hwm-seq = refl

maxplus-seq : tMul (val 2) (val 3) ≡ val 5
maxplus-seq = refl

3≢5 : 3 ≢ 5
3≢5 ()

occupancy-is-not-cost : peak (two ⊗h three) ≢ 5
occupancy-is-not-cost = 3≢5

----------------------------------------------------------------------
-- S-2  Alternatives: echo picks the less lossy branch (min), tropical the
--      most expensive (max).  Same numbers, different grade.
loss-alt : fin 2 ⊓g fin 3 ≡ fin 2
loss-alt = refl

maxplus-alt : tAdd (val 2) (val 3) ≡ val 3
maxplus-alt = refl

2≢3 : 2 ≢ 3
2≢3 ()

alternatives-differ : (fin 2 ⊓g fin 3) ≢ fin 3
alternatives-differ p = 2≢3 (fin-inj p)
  where
  fin-inj : ∀ {m n} → fin m ≡ fin n → m ≡ n
  fin-inj refl = refl

----------------------------------------------------------------------
-- S-3  The induced order: in MaxPlus 1 is below 2; in Loss 2 is below 1
--      (the numerically smaller loss is the one that absorbs).
maxplus-order : ResourceAlgebra._≼_ MaxPlus (val 1) (val 2)
maxplus-order = refl

loss-order-reversed : ResourceAlgebra._≼_ Loss (fin 2) (fin 1)
loss-order-reversed = refl
