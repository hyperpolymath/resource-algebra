{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- MaxPlus with a top: (ℕ ∪ {−∞, +∞}, max, +).
--
--   _⊕t_ = alternatives = max   (worst case);  unit bot (−∞, no path)
--   _⊗t_ = sequence     = +     (accumulate);  unit val 0
--   top  = +∞, the cost of a run with no finite bound
--
-- MaxPlus has no grade for a loop whose body costs something: the costs
-- val 1, val 2, ... have no upper bound in ℕ ∪ {−∞} (ResourceAlgebra.Star,
-- MaxPlus-no-fixpoint).  The top is that bound.  The impossible run still
-- annihilates: bot ⊗t top = bot.
module ResourceAlgebra.Instances.MaxPlusTop where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

data Grade : Set where
  bot : Grade
  val : Nat → Grade
  top : Grade

-- Injectivity through a projection (Prelude, suc-injective, says why).
val-proj : Grade → Nat
val-proj (val n) = n
val-proj bot     = zero
val-proj top     = zero

val-injective : ∀ {m n} → val m ≡ val n → m ≡ n
val-injective = cong val-proj

infixl 6 _⊕t_
_⊕t_ : Grade → Grade → Grade
bot   ⊕t y     = y
val m ⊕t bot   = val m
val m ⊕t val n = val (max m n)
val m ⊕t top   = top
top   ⊕t _     = top

infixl 7 _⊗t_
_⊗t_ : Grade → Grade → Grade
bot   ⊗t _     = bot
val m ⊗t bot   = bot
val m ⊗t val n = val (m + n)
val m ⊗t top   = top
top   ⊗t bot   = bot
top   ⊗t val _ = top
top   ⊗t top   = top

----------------------------------------------------------------------
-- Alternatives: (⊕t, bot) is an idempotent commutative monoid
⊕t-assoc : ∀ a b c → (a ⊕t b) ⊕t c ≡ a ⊕t (b ⊕t c)
⊕t-assoc bot     b       c       = refl
⊕t-assoc (val a) bot     c       = refl
⊕t-assoc (val a) (val b) bot     = refl
⊕t-assoc (val a) (val b) (val c) = cong val (max-assoc a b c)
⊕t-assoc (val a) (val b) top     = refl
⊕t-assoc (val a) top     c       = refl
⊕t-assoc top     b       c       = refl

⊕t-comm : ∀ a b → a ⊕t b ≡ b ⊕t a
⊕t-comm bot     bot     = refl
⊕t-comm bot     (val b) = refl
⊕t-comm bot     top     = refl
⊕t-comm (val a) bot     = refl
⊕t-comm (val a) (val b) = cong val (max-comm a b)
⊕t-comm (val a) top     = refl
⊕t-comm top     bot     = refl
⊕t-comm top     (val b) = refl
⊕t-comm top     top     = refl

⊕t-idem : ∀ a → a ⊕t a ≡ a
⊕t-idem bot     = refl
⊕t-idem (val a) = cong val (max-idem a)
⊕t-idem top     = refl

----------------------------------------------------------------------
-- Sequence: (⊗t, val 0) is a commutative monoid
⊗t-assoc : ∀ a b c → (a ⊗t b) ⊗t c ≡ a ⊗t (b ⊗t c)
⊗t-assoc bot     b       c       = refl
⊗t-assoc (val a) bot     c       = refl
⊗t-assoc (val a) (val b) bot     = refl
⊗t-assoc (val a) (val b) (val c) = cong val (+-assoc a b c)
⊗t-assoc (val a) (val b) top     = refl
⊗t-assoc (val a) top     bot     = refl
⊗t-assoc (val a) top     (val c) = refl
⊗t-assoc (val a) top     top     = refl
⊗t-assoc top     bot     c       = refl
⊗t-assoc top     (val b) bot     = refl
⊗t-assoc top     (val b) (val c) = refl
⊗t-assoc top     (val b) top     = refl
⊗t-assoc top     top     bot     = refl
⊗t-assoc top     top     (val c) = refl
⊗t-assoc top     top     top     = refl

⊗t-unitˡ : ∀ a → val 0 ⊗t a ≡ a
⊗t-unitˡ bot     = refl
⊗t-unitˡ (val a) = refl
⊗t-unitˡ top     = refl

⊗t-unitʳ : ∀ a → a ⊗t val 0 ≡ a
⊗t-unitʳ bot     = refl
⊗t-unitʳ (val a) = cong val (+-identityʳ a)
⊗t-unitʳ top     = refl

⊗t-comm : ∀ a b → a ⊗t b ≡ b ⊗t a
⊗t-comm bot     bot     = refl
⊗t-comm bot     (val b) = refl
⊗t-comm bot     top     = refl
⊗t-comm (val a) bot     = refl
⊗t-comm (val a) (val b) = cong val (+-comm a b)
⊗t-comm (val a) top     = refl
⊗t-comm top     bot     = refl
⊗t-comm top     (val b) = refl
⊗t-comm top     top     = refl

----------------------------------------------------------------------
-- The instance, and its layers
MaxPlusTop : ResourceAlgebra
MaxPlusTop = record
  { Grade = Grade
  ; _⊕_ = _⊕t_
  ; _⊗_ = _⊗t_
  ; 𝟘 = bot
  ; 𝟙 = val 0
  ; alt = record { assoc = ⊕t-assoc ; comm = ⊕t-comm ; idem = ⊕t-idem ; unitˡ = λ _ → refl }
  ; seq = record { assoc = ⊗t-assoc ; unitˡ = ⊗t-unitˡ ; unitʳ = ⊗t-unitʳ }
  }

MaxPlusTop-dioid : IsDioid MaxPlusTop
MaxPlusTop-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }
  where
  distribˡ : ∀ a b c → a ⊗t (b ⊕t c) ≡ (a ⊗t b) ⊕t (a ⊗t c)
  distribˡ bot     b       c       = refl
  distribˡ (val a) bot     c       = refl
  distribˡ (val a) (val b) bot     = refl
  distribˡ (val a) (val b) (val c) = cong val (+-distribˡ-max a b c)
  distribˡ (val a) (val b) top     = refl
  distribˡ (val a) top     c       = refl
  distribˡ top     bot     c       = refl
  distribˡ top     (val b) bot     = refl
  distribˡ top     (val b) (val c) = refl
  distribˡ top     (val b) top     = refl
  distribˡ top     top     c       = refl

  distribʳ : ∀ a b c → (a ⊕t b) ⊗t c ≡ (a ⊗t c) ⊕t (b ⊗t c)
  distribʳ a b c =
    trans (⊗t-comm (a ⊕t b) c)
    (trans (distribˡ c a b) (cong₂ _⊕t_ (⊗t-comm c a) (⊗t-comm c b)))

MaxPlusTop-ordered : IsOrdered MaxPlusTop
MaxPlusTop-ordered = IsDioid.ordered MaxPlusTop-dioid

MaxPlusTop-annihilating : IsAnnihilating MaxPlusTop
MaxPlusTop-annihilating = record { annihilˡ = λ _ → refl ; annihilʳ = annihilʳ }
  where
  annihilʳ : ∀ a → a ⊗t bot ≡ bot
  annihilʳ bot     = refl
  annihilʳ (val _) = refl
  annihilʳ top     = refl
