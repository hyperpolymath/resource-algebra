{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- A "which", not a "how much", grade.  Ledger: rows Q-1 to Q-4 of
-- docs/status/PROOF-STATUS.adoc; rechecked in verification/proofs/.
--
-- Fix n downstream questions.  A grade is the set of questions a step may
-- make unanswerable, as n booleans (true = this question is lost).
--   _⊗_ = sequence     = UNION        (a pipeline loses what any step loses), unit: none lost
--   _⊕_ = alternatives = INTERSECTION (lost on every branch),                 unit: all lost
-- This mirrors Loss (⊕ = min, 𝟘 = inf; ⊗ = +, 𝟙 = fin 0), question by question.
--
-- A step is safe for question i when bit i of its grade is false.
--
-- Not claimed: that a set of merged PAIRS composes by union.  It does not
-- (merging x~y then y~z also merges x~z).  Grade questions, not pairs.
--
-- Two limits of _⊕_ = intersection:
--   1. It is sound for each question alone, not for questions together.
--      In Loss one branch achieves the min.  Here no branch need achieve
--      the meet: `no-branch-achieves-meet` below has grade "none lost"
--      while neither branch keeps both questions.  Sound for "is question
--      i kept on some branch?".  Not sound for "does one branch keep all
--      the questions that I need?".
--   2. "May lose" holds for a single step and for _⊗_ only.  For
--      alternatives, intersection means "lost on every branch", so the
--      reader of the grade must own the choice.  If another party
--      chooses, the "may lose" grade is the union, not this _⊕_.
module ResourceAlgebra.Instances.Questions where

open import Agda.Builtin.Bool using (Bool; true; false)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

----------------------------------------------------------------------
-- One question: Bool with ∨ (lost on either) and ∧ (lost on both)
_∨_ _∧_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b
true  ∧ b = b
false ∧ _ = false

∨-assoc : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
∨-assoc true  _ _ = refl
∨-assoc false _ _ = refl

∨-unitʳ : ∀ a → a ∨ false ≡ a
∨-unitʳ true  = refl
∨-unitʳ false = refl

∨-zeroʳ : ∀ a → a ∨ true ≡ true
∨-zeroʳ true  = refl
∨-zeroʳ false = refl

∧-assoc : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc true  _ _ = refl
∧-assoc false _ _ = refl

∧-comm : ∀ a b → a ∧ b ≡ b ∧ a
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl

∧-idem : ∀ a → a ∧ a ≡ a
∧-idem true  = refl
∧-idem false = refl

∨-distribˡ-∧ : ∀ a b c → a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
∨-distribˡ-∧ true  _ _ = refl
∨-distribˡ-∧ false _ _ = refl

∨-distribʳ-∧ : ∀ a b c → (a ∧ b) ∨ c ≡ (a ∨ c) ∧ (b ∨ c)
∨-distribʳ-∧ true  true  true  = refl
∨-distribʳ-∧ true  true  false = refl
∨-distribʳ-∧ true  false true  = refl
∨-distribʳ-∧ true  false false = refl
∨-distribʳ-∧ false true  true  = refl
∨-distribʳ-∧ false true  false = refl
∨-distribʳ-∧ false false true  = refl
∨-distribʳ-∧ false false false = refl

----------------------------------------------------------------------
-- n questions: n booleans, by recursion on n (no indexed family, see
-- Prelude's note on _≤_), with every law lifted from the one-question law.
Q : Nat → Set
Q zero    = ⊤
Q (suc n) = Σ Bool (λ _ → Q n)

cons : ∀ n → Bool → Q n → Q (suc n)
cons n b q = b , q

rep : Bool → ∀ n → Q n
rep b zero    = tt
rep b (suc n) = b , rep b n

zip : (Bool → Bool → Bool) → ∀ n → Q n → Q n → Q n
zip f zero    _        _        = tt
zip f (suc n) (a , as) (b , bs) = f a b , zip f n as bs

module Lift (f : Bool → Bool → Bool) where
  assoc : (∀ a b c → f (f a b) c ≡ f a (f b c))
        → ∀ n x y z → zip f n (zip f n x y) z ≡ zip f n x (zip f n y z)
  assoc p zero    _ _ _ = refl
  assoc p (suc n) (a , as) (b , bs) (c , cs) =
    cong₂ (cons n) (p a b c) (assoc p n as bs cs)

  comm : (∀ a b → f a b ≡ f b a) → ∀ n x y → zip f n x y ≡ zip f n y x
  comm p zero    _ _ = refl
  comm p (suc n) (a , as) (b , bs) = cong₂ (cons n) (p a b) (comm p n as bs)

  idem : (∀ a → f a a ≡ a) → ∀ n x → zip f n x x ≡ x
  idem p zero    _ = refl
  idem p (suc n) (a , as) = cong₂ (cons n) (p a) (idem p n as)

  unitˡ : ∀ e → (∀ a → f e a ≡ a) → ∀ n x → zip f n (rep e n) x ≡ x
  unitˡ e p zero    _ = refl
  unitˡ e p (suc n) (a , as) = cong₂ (cons n) (p a) (unitˡ e p n as)

  unitʳ : ∀ e → (∀ a → f a e ≡ a) → ∀ n x → zip f n x (rep e n) ≡ x
  unitʳ e p zero    _ = refl
  unitʳ e p (suc n) (a , as) = cong₂ (cons n) (p a) (unitʳ e p n as)

  zeroˡ : ∀ z → (∀ a → f z a ≡ z) → ∀ n x → zip f n (rep z n) x ≡ rep z n
  zeroˡ z p zero    _ = refl
  zeroˡ z p (suc n) (a , as) = cong₂ (cons n) (p a) (zeroˡ z p n as)

  zeroʳ : ∀ z → (∀ a → f a z ≡ z) → ∀ n x → zip f n x (rep z n) ≡ rep z n
  zeroʳ z p zero    _ = refl
  zeroʳ z p (suc n) (a , as) = cong₂ (cons n) (p a) (zeroʳ z p n as)

----------------------------------------------------------------------
-- The instance, and its layers
module _ (n : Nat) where
  private
    _∪_ _∩_ : Q n → Q n → Q n
    _∪_ = zip _∨_ n
    _∩_ = zip _∧_ n

  Questions : ResourceAlgebra
  Questions = record
    { Grade = Q n
    ; _⊕_ = _∩_
    ; _⊗_ = _∪_
    ; 𝟘 = rep true n     -- every question lost
    ; 𝟙 = rep false n    -- no question lost
    ; alt = record
        { assoc = Lift.assoc _∧_ ∧-assoc n
        ; comm  = Lift.comm  _∧_ ∧-comm n
        ; idem  = Lift.idem  _∧_ ∧-idem n
        ; unitˡ = Lift.unitˡ _∧_ true (λ _ → refl) n
        }
    ; seq = record
        { assoc = Lift.assoc _∨_ ∨-assoc n
        ; unitˡ = Lift.unitˡ _∨_ false (λ _ → refl) n
        ; unitʳ = Lift.unitʳ _∨_ false ∨-unitʳ n
        }
    }

  Questions-dioid : IsDioid Questions
  Questions-dioid = record { distribˡ = dl n ; distribʳ = dr n }
    where
    dl : ∀ m (a b c : Q m)
       → zip _∨_ m a (zip _∧_ m b c) ≡ zip _∧_ m (zip _∨_ m a b) (zip _∨_ m a c)
    dl zero    _ _ _ = refl
    dl (suc m) (a , as) (b , bs) (c , cs) =
      cong₂ (cons m) (∨-distribˡ-∧ a b c) (dl m as bs cs)

    dr : ∀ m (a b c : Q m)
       → zip _∨_ m (zip _∧_ m a b) c ≡ zip _∧_ m (zip _∨_ m a c) (zip _∨_ m b c)
    dr zero    _ _ _ = refl
    dr (suc m) (a , as) (b , bs) (c , cs) =
      cong₂ (cons m) (∨-distribʳ-∧ a b c) (dr m as bs cs)

  Questions-ordered : IsOrdered Questions
  Questions-ordered = IsDioid.ordered Questions-dioid

  Questions-annihilating : IsAnnihilating Questions
  Questions-annihilating = record
    { annihilˡ = Lift.zeroˡ _∨_ true (λ _ → refl) n
    ; annihilʳ = Lift.zeroʳ _∨_ true ∨-zeroʳ n
    }

----------------------------------------------------------------------
-- The assembly-then-calling join, with 2 questions:
--   question 0: what is the order of the pieces?     (assembly's question)
--   question 1: do the two copies differ here?        (variant calling's question)
-- Collapsing the two copies into one consensus keeps 0 and loses 1.
-- Dropping read order (a bag of pieces) loses 0 and keeps 1.
-- Both steps lose exactly one question, so a "how much" grade cannot tell
-- them apart; this grade can.
collapse shuffle : Q 2
collapse = false , true  , tt
shuffle  = true  , false , tt

same-amount-different-loss : collapse ≢ shuffle
same-amount-different-loss p = false≢true (cong fst p)
  where
  false≢true : false ≢ true
  false≢true q = subst (λ { false → ⊤ ; true → ⊥ }) q tt

-- In sequence the losses add up: after both steps, neither question survives.
both-lost : ResourceAlgebra._⊗_ (Questions 2) collapse shuffle ≡ rep true 2
both-lost = refl

-- Limit 1 of the header, visible: the alternatives grade says no question
-- is lost, but each branch loses one (same-amount-different-loss above
-- shows the branches differ; neither is 𝟙).
no-branch-achieves-meet : ResourceAlgebra._⊕_ (Questions 2) collapse shuffle ≡ rep false 2
no-branch-achieves-meet = refl
