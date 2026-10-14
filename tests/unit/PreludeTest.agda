{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module PreludeTest where

open import ResourceAlgebra.Prelude

-- Concrete clients of the new lemmas cover zero, equal bounds, strict
-- bounds, and the recursive positive cases without a standard library.
cancel-zero-prefix : ∀ {m n} → 0 + m ≡ 0 + n → m ≡ n
cancel-zero-prefix = +-cancelˡ 0

cancel-positive-prefix : ∀ {m n} → 3 + m ≡ 3 + n → m ≡ n
cancel-positive-prefix = +-cancelˡ 3

cancel-successor : ∀ {m n} → suc m ≡ suc n → m ≡ n
cancel-successor = suc-injective

left-summand-zero : 0 ≤ 0 + 5
left-summand-zero = ≤-+ʳ 0 5

left-summand-positive : 3 ≤ 3 + 2
left-summand-positive = ≤-+ʳ 3 2

right-summand-zero : 5 ≤ 0 + 5
right-summand-zero = ≤-+ˡ 0 5

right-summand-positive : 5 ≤ 3 + 5
right-summand-positive = ≤-+ˡ 3 5

adding-preserves-strict-bound : 2 + 3 ≤ 5 + 3
adding-preserves-strict-bound = +-monoˡ-≤ {m = 2} {n = 5} 3 (s≤s (s≤s z≤n))

adding-zero-preserves-equal-bound : 3 + 0 ≤ 3 + 0
adding-zero-preserves-equal-bound = +-monoˡ-≤ {m = 3} {n = 3} 0 (≤-refl 3)

max-bound-left-zero : max 0 3 ≤ 5
max-bound-left-zero = max-lub z≤n (s≤s (s≤s (s≤s z≤n)))

max-bound-right-zero : max 3 0 ≤ 5
max-bound-right-zero = max-lub (s≤s (s≤s (s≤s z≤n))) z≤n

max-bound-positive : max 2 3 ≤ 4
max-bound-positive = max-lub (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))

max-of-zero-and-positive : max 0 5 ≡ 5
max-of-zero-and-positive = max-≤ z≤n

max-at-equal-bound : max 3 3 ≡ 3
max-at-equal-bound = max-≤ (≤-refl 3)

max-at-strict-bound : max 2 5 ≡ 5
max-at-strict-bound = max-≤ (s≤s (s≤s z≤n))

min-at-zero-bound : min 0 5 ≡ 0
min-at-zero-bound = min-≤ {m = 0} {n = 5} z≤n

min-at-strict-bound : min 2 5 ≡ 2
min-at-strict-bound = min-≤ {m = 2} {n = 5} (s≤s (s≤s z≤n))

min-at-reversed-bound : min 5 2 ≡ 2
min-at-reversed-bound = min-≥ {m = 5} {n = 2} (s≤s (s≤s z≤n))

bottleneck-bound-zero-left : max 0 5 ≤ 0 + 5
bottleneck-bound-zero-left = max-≤-+ 0 5

bottleneck-bound-zero-right : max 5 0 ≤ 5 + 0
bottleneck-bound-zero-right = max-≤-+ 5 0

bottleneck-bound-positive : max 2 3 ≤ 2 + 3
bottleneck-bound-positive = max-≤-+ 2 3

-- Each base case and the recursive case of the new distributivity lemma.
distribute-zero-sequence : max 0 (min 2 5) ≡ min (max 0 2) (max 0 5)
distribute-zero-sequence = max-distribˡ-min 0 2 5

distribute-zero-first-choice : max 3 (min 0 5) ≡ min (max 3 0) (max 3 5)
distribute-zero-first-choice = max-distribˡ-min 3 0 5

distribute-zero-second-choice : max 3 (min 5 0) ≡ min (max 3 5) (max 3 0)
distribute-zero-second-choice = max-distribˡ-min 3 5 0

distribute-positive-choices : max 3 (min 2 5) ≡ min (max 3 2) (max 3 5)
distribute-positive-choices = max-distribˡ-min 3 2 5

distribute-right-positive-choices : max (min 2 5) 3 ≡ min (max 2 3) (max 5 3)
distribute-right-positive-choices = max-distribʳ-min 2 5 3

distribute-right-zero-choice : max (min 5 0) 3 ≡ min (max 5 3) (max 0 3)
distribute-right-zero-choice = max-distribʳ-min 5 0 3
