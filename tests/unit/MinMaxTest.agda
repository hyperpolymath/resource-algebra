{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module MinMaxTest where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss using (fin; inf; _+g_)
open import ResourceAlgebra.Instances.MinMax
import ResourceAlgebra.Separation as S

module MM = ResourceAlgebra MinMax

-- Use the public record as well as the sequence operator: the record's
-- choice of units and operations is part of the consumer contract.
zero-is-unreachable : MM.𝟘 ≡ inf
zero-is-unreachable = refl

one-is-no-cost : MM.𝟙 ≡ fin 0
one-is-no-cost = refl

alternative-chooses-smaller : fin 2 MM.⊕ fin 7 ≡ fin 2
alternative-chooses-smaller = refl

alternative-chooses-smaller-reversed : fin 7 MM.⊕ fin 2 ≡ fin 2
alternative-chooses-smaller-reversed = refl

unreachable-alternative-left : ∀ n → inf MM.⊕ fin n ≡ fin n
unreachable-alternative-left n = refl

unreachable-alternative-right : ∀ n → fin n MM.⊕ inf ≡ fin n
unreachable-alternative-right n = refl

both-alternatives-unreachable : inf MM.⊕ inf ≡ inf
both-alternatives-unreachable = refl

sequence-chooses-larger : fin 2 MM.⊗ fin 7 ≡ fin 7
sequence-chooses-larger = refl

sequence-chooses-larger-reversed : fin 7 MM.⊗ fin 2 ≡ fin 7
sequence-chooses-larger-reversed = refl

repeated-hop-does-not-accumulate : fin 4 MM.⊗ fin 4 ≡ fin 4
repeated-hop-does-not-accumulate = refl

zero-hop-left : ∀ n → fin 0 ⊔g fin n ≡ fin n
zero-hop-left n = refl

zero-hop-right : ∀ n → fin n ⊔g fin 0 ≡ fin n
zero-hop-right n = cong fin (max-zeroʳ n)

unreachable-hop-left : ∀ n → inf ⊔g fin n ≡ inf
unreachable-hop-left n = refl

unreachable-hop-right : ∀ n → fin n ⊔g inf ≡ inf
unreachable-hop-right n = refl

both-hops-unreachable : inf ⊔g inf ≡ inf
both-hops-unreachable = refl

unreachable-after-no-cost : fin 0 MM.⊗ inf ≡ inf
unreachable-after-no-cost = refl

no-cost-after-unreachable : inf MM.⊗ fin 0 ≡ inf
no-cost-after-unreachable = refl

three-hop-bottleneck : (fin 2 MM.⊗ fin 7) MM.⊗ fin 3 ≡ fin 7
three-hop-bottleneck = refl

unreachable-middle-hop : (fin 2 MM.⊗ inf) MM.⊗ fin 3 ≡ inf
unreachable-middle-hop = refl

-- Exercise both distribution laws through the exported dioid layer.
distribute-left-with-unreachable :
  fin 4 MM.⊗ (inf MM.⊕ fin 2) ≡
  (fin 4 MM.⊗ inf) MM.⊕ (fin 4 MM.⊗ fin 2)
distribute-left-with-unreachable = IsDioid.distribˡ MinMax-dioid (fin 4) inf (fin 2)

distribute-right-with-unreachable :
  (fin 2 MM.⊕ inf) MM.⊗ fin 4 ≡
  (fin 2 MM.⊗ fin 4) MM.⊕ (inf MM.⊗ fin 4)
distribute-right-with-unreachable = IsDioid.distribʳ MinMax-dioid (fin 2) inf (fin 4)

choice-between-bottlenecks :
  (fin 4 MM.⊗ fin 2) MM.⊕ (fin 4 MM.⊗ fin 7) ≡ fin 4
choice-between-bottlenecks = refl

annihilate-left : inf MM.⊗ fin 0 ≡ inf
annihilate-left = IsAnnihilating.annihilˡ MinMax-annihilating (fin 0)

annihilate-right : fin 0 MM.⊗ inf ≡ inf
annihilate-right = IsAnnihilating.annihilʳ MinMax-annihilating (fin 0)

-- The induced order reverses the usual numeric order, including infinity.
smaller-bottleneck-is-above : fin 7 MM.≼ fin 2
smaller-bottleneck-is-above = refl

unreachable-is-least : inf MM.≼ fin 0
unreachable-is-least = refl

sequence-monotone-left : (fin 4 MM.⊗ fin 7) MM.≼ (fin 4 MM.⊗ fin 2)
sequence-monotone-left = IsOrdered.⊗-monoˡ MinMax-ordered (fin 4)
  {a = fin 7} {b = fin 2} refl

sequence-monotone-right : (inf MM.⊗ fin 4) MM.≼ (fin 2 MM.⊗ fin 4)
sequence-monotone-right = IsOrdered.⊗-monoʳ MinMax-ordered (fin 4)
  {a = inf} {b = fin 2} refl

-- S-4's public witnesses, and a new boundary where adding repeats a hop.
separation-loss-result : fin 2 +g fin 3 ≡ fin 5
separation-loss-result = S.loss-seq

separation-bottleneck-result : fin 2 ⊔g fin 3 ≡ fin 3
separation-bottleneck-result = S.minmax-seq

separation-witness : fin 2 ⊔g fin 3 ≢ fin 2 +g fin 3
separation-witness = S.bottleneck-is-not-sum

repeated-hop-is-not-a-sum : fin 4 ⊔g fin 4 ≢ fin 4 +g fin 4
repeated-hop-is-not-a-sum ()

numeric-order-is-not-induced-order : ¬ (fin 2 MM.≼ fin 7)
numeric-order-is-not-induced-order ()
