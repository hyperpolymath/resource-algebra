{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Checking this module checks the whole development.
module ResourceAlgebra.All where

import ResourceAlgebra.Prelude
import ResourceAlgebra.Core
import ResourceAlgebra.Instances.Loss
import ResourceAlgebra.Instances.MaxPlus
import ResourceAlgebra.Instances.HWM
import ResourceAlgebra.Instances.MinMax
import ResourceAlgebra.Instances.Questions
import ResourceAlgebra.Instances.Evidence
import ResourceAlgebra.Ledger
import ResourceAlgebra.Instances.Diamond
import ResourceAlgebra.Separation
import ResourceAlgebra.Morphism
import ResourceAlgebra.Instances.MaxPlusTop
import ResourceAlgebra.Parallel
import ResourceAlgebra.Star
