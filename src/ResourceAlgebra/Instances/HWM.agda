{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- STATUS: DESIGNED.  A proposed high-water-mark (occupancy) grade algebra.
--
-- occupancy-types states (docs/OPERATIONAL-MODEL.md) that live memory is
-- *counted* in v0 ("peak live bytes: high-water mark of allocated-minus-
-- dropped buffers") and that the HWM grade algebra is an R2–R3 deliverable,
-- "deliberately not a second semiring" in that repo.  Nothing there defines
-- it yet, so this module is a proposal, not a transcription.  When
-- occupancy-types publishes its own definition, that definition supersedes
-- this one and the separation witnesses in Separation.agda must be re-run.
--
-- The model: a grade records the peak live state reached during a run and
-- the drift (live state still held at the end).  Sequencing b after a
-- starts b from a's drift, so the peak of a;b is  max (peak a) (drift a +
-- peak b)  — this is exactly where an occupancy bound stops being a cost
-- bound (a cost would add the peaks).  Drift is non-negative here: the
-- model is for terms that do not consume more than they allocate; a signed
-- drift is a recorded extension (PROOF-STATUS, H-2).
module ResourceAlgebra.Instances.HWM where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

record Grade : Set where
  constructor hwm
  field
    peak    : Nat
    drift   : Nat
    bounded : drift ≤ peak

open Grade public using (peak; drift)

-- Proofs of m ≤ n are unique, so a grade is determined by peak and drift.
≤-irrelevant : ∀ {m n} (p q : m ≤ n) → p ≡ q
≤-irrelevant z≤n     z≤n     = refl
≤-irrelevant (s≤s p) (s≤s q) = cong s≤s (≤-irrelevant p q)

hwm-≡ : ∀ {p p' n n'} {b : n ≤ p} {b' : n' ≤ p'}
      → p ≡ p' → n ≡ n' → hwm p n b ≡ hwm p' n' b'
hwm-≡ {b = b} {b' = b'} refl refl = cong (hwm _ _) (≤-irrelevant b b')

max-absorb-≤ : ∀ {n p} → n ≤ p → max p n ≡ p
max-absorb-≤ {p = p} z≤n = max-zeroʳ p
max-absorb-≤ (s≤s q)     = cong suc (max-absorb-≤ q)

----------------------------------------------------------------------
-- Operations
infixl 7 _⊗h_
_⊗h_ : Grade → Grade → Grade
hwm p₁ n₁ b₁ ⊗h hwm p₂ n₂ b₂ =
  hwm (max p₁ (n₁ + p₂)) (n₁ + n₂)
      (≤-trans (+-monoʳ-≤ n₁ b₂) (≤-max-right p₁ (n₁ + p₂)))

infixl 6 _⊕h_
_⊕h_ : Grade → Grade → Grade
hwm p₁ n₁ b₁ ⊕h hwm p₂ n₂ b₂ = hwm (max p₁ p₂) (max n₁ n₂) (max-mono-≤ b₁ b₂)

-- One element is both units: nothing allocated, nothing held.
𝟘h : Grade
𝟘h = hwm 0 0 z≤n

----------------------------------------------------------------------
-- Alternatives: componentwise max
⊕h-assoc : ∀ a b c → (a ⊕h b) ⊕h c ≡ a ⊕h (b ⊕h c)
⊕h-assoc (hwm p n _) (hwm p' n' _) (hwm p'' n'' _) =
  hwm-≡ (max-assoc p p' p'') (max-assoc n n' n'')

⊕h-comm : ∀ a b → a ⊕h b ≡ b ⊕h a
⊕h-comm (hwm p n _) (hwm p' n' _) = hwm-≡ (max-comm p p') (max-comm n n')

⊕h-idem : ∀ a → a ⊕h a ≡ a
⊕h-idem (hwm p n _) = hwm-≡ (max-idem p) (max-idem n)

⊕h-unitˡ : ∀ a → 𝟘h ⊕h a ≡ a
⊕h-unitˡ (hwm p n _) = hwm-≡ refl refl

----------------------------------------------------------------------
-- Sequence
⊗h-assoc : ∀ a b c → (a ⊗h b) ⊗h c ≡ a ⊗h (b ⊗h c)
⊗h-assoc (hwm p₁ n₁ _) (hwm p₂ n₂ _) (hwm p₃ n₃ _) =
  hwm-≡
    (trans (cong (max (max p₁ (n₁ + p₂))) (+-assoc n₁ n₂ p₃))
    (trans (max-assoc p₁ (n₁ + p₂) (n₁ + (n₂ + p₃)))
           (cong (max p₁) (sym (+-distribˡ-max n₁ p₂ (n₂ + p₃))))))
    (+-assoc n₁ n₂ n₃)

⊗h-unitˡ : ∀ a → 𝟘h ⊗h a ≡ a
⊗h-unitˡ (hwm p n _) = hwm-≡ refl refl

⊗h-unitʳ : ∀ a → a ⊗h 𝟘h ≡ a
⊗h-unitʳ (hwm p n b) =
  hwm-≡ (trans (cong (max p) (+-identityʳ n)) (max-absorb-≤ b)) (+-identityʳ n)

----------------------------------------------------------------------
-- The instance, and its layers
HWM : ResourceAlgebra
HWM = record
  { Grade = Grade
  ; _⊕_ = _⊕h_
  ; _⊗_ = _⊗h_
  ; 𝟘 = 𝟘h
  ; 𝟙 = 𝟘h
  ; alt = record { assoc = ⊕h-assoc ; comm = ⊕h-comm ; idem = ⊕h-idem ; unitˡ = ⊕h-unitˡ }
  ; seq = record { assoc = ⊗h-assoc ; unitˡ = ⊗h-unitˡ ; unitʳ = ⊗h-unitʳ }
  }

HWM-dioid : IsDioid HWM
HWM-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }
  where
  distribˡ : ∀ a b c → a ⊗h (b ⊕h c) ≡ (a ⊗h b) ⊕h (a ⊗h c)
  distribˡ (hwm p n _) (hwm p₂ n₂ _) (hwm p₃ n₃ _) =
    hwm-≡ (trans (cong (max p) (+-distribˡ-max n p₂ p₃))
                 (sym (max-dup p (n + p₂) (n + p₃))))
          (+-distribˡ-max n n₂ n₃)

  distribʳ : ∀ a b c → (a ⊕h b) ⊗h c ≡ (a ⊗h c) ⊕h (b ⊗h c)
  distribʳ (hwm p₂ n₂ _) (hwm p₃ n₃ _) (hwm p n _) =
    hwm-≡ (trans (cong (max (max p₂ p₃)) (+-distribʳ-max n₂ n₃ p))
                 (max-interchange p₂ p₃ (n₂ + p) (n₃ + p)))
          (+-distribʳ-max n₂ n₃ n)

HWM-ordered : IsOrdered HWM
HWM-ordered = IsDioid.ordered HWM-dioid

-- There is no IsAnnihilating HWM: 𝟘h is also the sequence unit, so
-- 𝟘h ⊗h a ≡ a, not 𝟘h.  A grade with peak 1 refutes it (H-3);
-- tests/reject/HWMAnnihilates.agda is the control.
HWM-not-annihilating : ¬ IsAnnihilating HWM
HWM-not-annihilating z = one≢zero (cong peak (IsAnnihilating.annihilˡ z (hwm 1 0 z≤n)))
  where
  one≢zero : 1 ≢ 0
  one≢zero ()
