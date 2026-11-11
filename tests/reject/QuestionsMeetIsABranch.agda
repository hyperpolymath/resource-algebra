{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module QuestionsMeetIsABranch where
open import Agda.Builtin.Bool using (Bool; true; false)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Questions

-- Must fail: the grade of two alternatives is the intersection of what the
-- branches lose, and no branch need have that grade.  Accepting this would
-- let "no question is lost on some branch" be read as "one branch keeps
-- every question", which is the reading Q-4 exists to forbid.
-- EXPECT: false != true of type Bool
invalid : ResourceAlgebra._⊕_ (Questions 2) collapse shuffle ≡ collapse
invalid = refl
