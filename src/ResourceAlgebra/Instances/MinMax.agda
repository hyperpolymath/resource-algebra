{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The min-max (bottleneck) grade: the Loss carrier ℕ ∪ {∞} with
--   _⊓g_  = alternatives = MIN (the better path)    — the semiring "⊕", unit inf
--   _⊔g_  = sequence     = MAX (the worst hop)       — the semiring "⊗", unit fin 0
-- inf absorbs under both: an unreachable hop makes the path unreachable,
-- and an unreachable alternative is never chosen.
--
-- Consumer: typed-wasm L11's bottleneck reading (Tropical.tropMax, its
-- Level11BottleneckProof), which until now defined this sequence locally
-- and was the one allowlisted exception to its one-min-plus/one-max-plus
-- gate.  It shares Loss's carrier and alternatives on purpose: the
-- identity on the carrier is a lax morphism Loss → MinMax (Morphism.agda,
-- `loss-bottleneck`), because a bottleneck never exceeds the sum.
--
-- It is neither min-plus (sequence is max, not +) nor max-plus (max is the
-- sequence, not the alternatives, and 𝟘 is inf, not −∞): Separation.agda
-- S-4 and tests/reject/MinMaxIsLoss.agda are the checked statements.
module ResourceAlgebra.Instances.MinMax where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss
  using (Grade; fin; inf; _⊓g_; ⊓g-assoc; ⊓g-comm; ⊓g-idem)

infixl 7 _⊔g_
_⊔g_ : Grade → Grade → Grade
inf   ⊔g _     = inf
fin m ⊔g inf   = inf
fin m ⊔g fin n = fin (max m n)

----------------------------------------------------------------------
-- Sequence: (⊔g, fin 0) is a monoid
⊔g-assoc : ∀ a b c → (a ⊔g b) ⊔g c ≡ a ⊔g (b ⊔g c)
⊔g-assoc (fin a) (fin b) (fin c) = cong fin (max-assoc a b c)
⊔g-assoc (fin a) (fin b) inf     = refl
⊔g-assoc (fin a) inf     c       = refl
⊔g-assoc inf     b       c       = refl

⊔g-unitˡ : ∀ a → fin 0 ⊔g a ≡ a
⊔g-unitˡ (fin a) = refl
⊔g-unitˡ inf     = refl

⊔g-unitʳ : ∀ a → a ⊔g fin 0 ≡ a
⊔g-unitʳ (fin a) = cong fin (max-zeroʳ a)
⊔g-unitʳ inf     = refl

----------------------------------------------------------------------
-- The instance, and its layers
MinMax : ResourceAlgebra
MinMax = record
  { Grade = Grade
  ; _⊕_ = _⊓g_
  ; _⊗_ = _⊔g_
  ; 𝟘 = inf
  ; 𝟙 = fin 0
  ; alt = record { assoc = ⊓g-assoc ; comm = ⊓g-comm ; idem = ⊓g-idem ; unitˡ = λ _ → refl }
  ; seq = record { assoc = ⊔g-assoc ; unitˡ = ⊔g-unitˡ ; unitʳ = ⊔g-unitʳ }
  }

MinMax-dioid : IsDioid MinMax
MinMax-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }
  where
  distribˡ : ∀ a b c → a ⊔g (b ⊓g c) ≡ (a ⊔g b) ⊓g (a ⊔g c)
  distribˡ (fin a) (fin b) (fin c) = cong fin (max-distribˡ-min a b c)
  distribˡ (fin a) (fin b) inf     = refl
  distribˡ (fin a) inf     c       = refl
  distribˡ inf     b       c       = refl

  distribʳ : ∀ a b c → (a ⊓g b) ⊔g c ≡ (a ⊔g c) ⊓g (b ⊔g c)
  distribʳ (fin a) (fin b) (fin c) = cong fin (max-distribʳ-min a b c)
  distribʳ (fin a) (fin b) inf     = refl
  distribʳ (fin a) inf     (fin c) = refl
  distribʳ (fin a) inf     inf     = refl
  distribʳ inf     b       c       = refl

MinMax-ordered : IsOrdered MinMax
MinMax-ordered = IsDioid.ordered MinMax-dioid

MinMax-annihilating : IsAnnihilating MinMax
MinMax-annihilating = record { annihilˡ = λ _ → refl ; annihilʳ = annihilʳ }
  where
  annihilʳ : ∀ a → a ⊔g inf ≡ inf
  annihilʳ (fin _) = refl
  annihilʳ inf     = refl
