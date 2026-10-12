{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The tropical-types max-plus grade, transcribed (not redesigned) from
-- tropical-types/TropicalSessionTypes.lean:
--   Tropical = ℕ ∪ {bot};  bot = −∞
--   tAdd = max with bot as identity   — alternatives, the semiring "⊕"
--   tMul = + with bot absorbing       — sequence, the semiring "⊗", unit val 0
-- Cross-prover bridge obligation (PROOF-STATUS, M-1): the Lean development
-- proves `instance : CommSemiring Tropical`; this Agda transcription re-proves
-- the same laws.  Nothing mechanical links the two; the port-and-reprove
-- pattern applies and the correspondence is a named review obligation.
module ResourceAlgebra.Instances.MaxPlus where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

data Tropical : Set where
  val : Nat → Tropical
  bot : Tropical

tAdd : Tropical → Tropical → Tropical
tAdd bot     b       = b
tAdd (val m) bot     = val m
tAdd (val m) (val n) = val (max m n)

tMul : Tropical → Tropical → Tropical
tMul bot     _       = bot
tMul (val m) bot     = bot
tMul (val m) (val n) = val (m + n)

----------------------------------------------------------------------
-- Alternatives: (tAdd, bot) is an idempotent commutative monoid
tAdd-assoc : ∀ a b c → tAdd (tAdd a b) c ≡ tAdd a (tAdd b c)
tAdd-assoc (val a) (val b) (val c) = cong val (max-assoc a b c)
tAdd-assoc (val a) (val b) bot     = refl
tAdd-assoc (val a) bot     c       = refl
tAdd-assoc bot     b       c       = refl

tAdd-comm : ∀ a b → tAdd a b ≡ tAdd b a
tAdd-comm (val a) (val b) = cong val (max-comm a b)
tAdd-comm (val a) bot     = refl
tAdd-comm bot     (val b) = refl
tAdd-comm bot     bot     = refl

tAdd-idem : ∀ a → tAdd a a ≡ a
tAdd-idem (val a) = cong val (max-idem a)
tAdd-idem bot     = refl

----------------------------------------------------------------------
-- Sequence: (tMul, val 0) is a monoid
tMul-assoc : ∀ a b c → tMul (tMul a b) c ≡ tMul a (tMul b c)
tMul-assoc (val a) (val b) (val c) = cong val (+-assoc a b c)
tMul-assoc (val a) (val b) bot     = refl
tMul-assoc (val a) bot     c       = refl
tMul-assoc bot     b       c       = refl

tMul-unitˡ : ∀ a → tMul (val 0) a ≡ a
tMul-unitˡ (val a) = refl
tMul-unitˡ bot     = refl

tMul-unitʳ : ∀ a → tMul a (val 0) ≡ a
tMul-unitʳ (val a) = cong val (+-identityʳ a)
tMul-unitʳ bot     = refl

----------------------------------------------------------------------
-- The instance, and its layers
MaxPlus : ResourceAlgebra
MaxPlus = record
  { Grade = Tropical
  ; _⊕_ = tAdd
  ; _⊗_ = tMul
  ; 𝟘 = bot
  ; 𝟙 = val 0
  ; alt = record { assoc = tAdd-assoc ; comm = tAdd-comm ; idem = tAdd-idem ; unitˡ = λ _ → refl }
  ; seq = record { assoc = tMul-assoc ; unitˡ = tMul-unitˡ ; unitʳ = tMul-unitʳ }
  }

MaxPlus-dioid : IsDioid MaxPlus
MaxPlus-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }
  where
  distribˡ : ∀ a b c → tMul a (tAdd b c) ≡ tAdd (tMul a b) (tMul a c)
  distribˡ (val a) (val b) (val c) = cong val (+-distribˡ-max a b c)
  distribˡ (val a) (val b) bot     = refl
  distribˡ (val a) bot     (val c) = refl
  distribˡ (val a) bot     bot     = refl
  distribˡ bot     b       c       = refl

  distribʳ : ∀ a b c → tMul (tAdd a b) c ≡ tAdd (tMul a c) (tMul b c)
  distribʳ (val a) (val b) (val c) = cong val (+-distribʳ-max a b c)
  distribʳ (val a) (val b) bot     = refl
  distribʳ (val a) bot     (val c) = refl
  distribʳ (val a) bot     bot     = refl
  distribʳ bot     (val b) (val c) = refl
  distribʳ bot     (val b) bot     = refl
  distribʳ bot     bot     c       = refl

MaxPlus-ordered : IsOrdered MaxPlus
MaxPlus-ordered = IsDioid.ordered MaxPlus-dioid

MaxPlus-annihilating : IsAnnihilating MaxPlus
MaxPlus-annihilating = record { annihilˡ = λ _ → refl ; annihilʳ = annihilʳ }
  where
  annihilʳ : ∀ a → tMul a bot ≡ bot
  annihilʳ (val _) = refl
  annihilʳ bot     = refl
