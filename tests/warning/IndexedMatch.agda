{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Negative control for the Agda gate's warning policy. The clause below
-- matches refl on suc m ≡ suc n, which needs injectivity of suc. Under
-- --cubical-compatible Agda warns (UnsupportedIndexedMatch) that it will
-- not compute along transports. The module is otherwise valid: it checks
-- without -W error. tests/check_agda_warning_gate_test.sh requires the
-- gate's own flags to refuse it.
module IndexedMatch where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

suc-injective : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl
