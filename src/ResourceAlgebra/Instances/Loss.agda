{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The echo-types loss grade, transcribed (not redesigned) from
-- echo-types/proofs/agda/experimental/echo-additive/Grade.agda:
--   Grade = ℕ ∪ {∞};  fin 0 = no loss (echo `keep`);  inf = total collapse.
--   _+g_  = sequence (loss accumulates, inf absorbs)   — the semiring "⊗"
--   _⊓g_  = alternatives = MIN (the less lossy option) — the semiring "⊕"
-- Provenance obligation (PROOF-STATUS, L-1): once resource-algebra is an
-- importable library, decide whether echo-types imports this module or this
-- module imports echo-types.  Until then the two definitions must stay
-- textually identical; the comparison is a review step, not a proof.
module ResourceAlgebra.Instances.Loss where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

data Grade : Set where
  fin : Nat → Grade
  inf : Grade

infixl 7 _+g_
_+g_ : Grade → Grade → Grade
fin m +g fin n = fin (m + n)
fin _ +g inf   = inf
inf   +g _     = inf

infixl 6 _⊓g_
_⊓g_ : Grade → Grade → Grade
fin m ⊓g fin n = fin (min m n)
fin m ⊓g inf   = fin m
inf   ⊓g g     = g

----------------------------------------------------------------------
-- Alternatives: (⊓g, inf) is an idempotent commutative monoid
⊓g-assoc : ∀ a b c → (a ⊓g b) ⊓g c ≡ a ⊓g (b ⊓g c)
⊓g-assoc (fin a) (fin b) (fin c) = cong fin (min-assoc a b c)
⊓g-assoc (fin a) (fin b) inf     = refl
⊓g-assoc (fin a) inf     c       = refl
⊓g-assoc inf     b       c       = refl

⊓g-comm : ∀ a b → a ⊓g b ≡ b ⊓g a
⊓g-comm (fin a) (fin b) = cong fin (min-comm a b)
⊓g-comm (fin a) inf     = refl
⊓g-comm inf     (fin b) = refl
⊓g-comm inf     inf     = refl

⊓g-idem : ∀ a → a ⊓g a ≡ a
⊓g-idem (fin a) = cong fin (min-idem a)
⊓g-idem inf     = refl

----------------------------------------------------------------------
-- Sequence: (+g, fin 0) is a monoid
+g-assoc : ∀ a b c → (a +g b) +g c ≡ a +g (b +g c)
+g-assoc (fin a) (fin b) (fin c) = cong fin (+-assoc a b c)
+g-assoc (fin a) (fin b) inf     = refl
+g-assoc (fin a) inf     c       = refl
+g-assoc inf     b       c       = refl

+g-unitˡ : ∀ a → fin 0 +g a ≡ a
+g-unitˡ (fin a) = refl
+g-unitˡ inf     = refl

+g-unitʳ : ∀ a → a +g fin 0 ≡ a
+g-unitʳ (fin a) = cong fin (+-identityʳ a)
+g-unitʳ inf     = refl

----------------------------------------------------------------------
-- The instance, and its layers
Loss : ResourceAlgebra
Loss = record
  { Grade = Grade
  ; _⊕_ = _⊓g_
  ; _⊗_ = _+g_
  ; 𝟘 = inf
  ; 𝟙 = fin 0
  ; alt = record { assoc = ⊓g-assoc ; comm = ⊓g-comm ; idem = ⊓g-idem ; unitˡ = λ _ → refl }
  ; seq = record { assoc = +g-assoc ; unitˡ = +g-unitˡ ; unitʳ = +g-unitʳ }
  }

Loss-dioid : IsDioid Loss
Loss-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }
  where
  distribˡ : ∀ a b c → a +g (b ⊓g c) ≡ (a +g b) ⊓g (a +g c)
  distribˡ (fin a) (fin b) (fin c) = cong fin (+-distribˡ-min a b c)
  distribˡ (fin a) (fin b) inf     = refl
  distribˡ (fin a) inf     c       = refl
  distribˡ inf     b       c       = refl

  distribʳ : ∀ a b c → (a ⊓g b) +g c ≡ (a +g c) ⊓g (b +g c)
  distribʳ (fin a) (fin b) (fin c) = cong fin (+-distribʳ-min a b c)
  distribʳ (fin a) (fin b) inf     = refl
  distribʳ (fin a) inf     (fin c) = refl
  distribʳ (fin a) inf     inf     = refl
  distribʳ inf     b       c       = refl

Loss-ordered : IsOrdered Loss
Loss-ordered = IsDioid.ordered Loss-dioid

Loss-annihilating : IsAnnihilating Loss
Loss-annihilating = record { annihilˡ = λ _ → refl ; annihilʳ = annihilʳ }
  where
  annihilʳ : ∀ a → a +g inf ≡ inf
  annihilʳ (fin _) = refl
  annihilʳ inf     = refl
