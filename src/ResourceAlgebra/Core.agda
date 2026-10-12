{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The parametric resource algebra shared by the type family.
--
-- Layering, from weakest to strongest:
--   ResourceAlgebra  — alternatives form an idempotent commutative monoid
--                      (⊕, 𝟘); sequence forms a monoid (⊗, 𝟙).  This is all
--                      K-CUT-LOSS (an equality) is expected to need.
--   IsOrdered        — ⊗ is monotone for the ⊕-induced order ≼; what a
--                      *bound* statement such as K-CUT-WARRANT needs.
--   IsDioid          — ⊗ distributes over ⊕ on both sides.  Every dioid is
--                      ordered (proved below), so instances prove
--                      distributivity once and get monotonicity for free.
--   IsAnnihilating   — 𝟘 absorbs under ⊗.  Deliberately separate: the
--                      high-water-mark instance is a dioid with 𝟘 ≡ 𝟙, so it
--                      cannot be annihilating, yet it is a perfectly good
--                      resource algebra.
module ResourceAlgebra.Core where

open import ResourceAlgebra.Prelude

record IsAltMonoid {G : Set} (_⊕_ : G → G → G) (𝟘 : G) : Set where
  field
    assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    comm  : ∀ a b → a ⊕ b ≡ b ⊕ a
    idem  : ∀ a → a ⊕ a ≡ a
    unitˡ : ∀ a → 𝟘 ⊕ a ≡ a

  unitʳ : ∀ a → a ⊕ 𝟘 ≡ a
  unitʳ a = trans (comm a 𝟘) (unitˡ a)

record IsSeqMonoid {G : Set} (_⊗_ : G → G → G) (𝟙 : G) : Set where
  field
    assoc : ∀ a b c → (a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c)
    unitˡ : ∀ a → 𝟙 ⊗ a ≡ a
    unitʳ : ∀ a → a ⊗ 𝟙 ≡ a

record ResourceAlgebra : Set₁ where
  infixl 6 _⊕_
  infixl 7 _⊗_
  infix  4 _≼_
  field
    Grade : Set
    _⊕_   : Grade → Grade → Grade   -- alternatives
    _⊗_   : Grade → Grade → Grade   -- sequence
    𝟘     : Grade                   -- unit of ⊕
    𝟙     : Grade                   -- unit of ⊗
    alt   : IsAltMonoid _⊕_ 𝟘
    seq   : IsSeqMonoid _⊗_ 𝟙

  -- The order every resource algebra induces: a ≼ b when b absorbs a.
  -- Which way it runs numerically is instance-specific (see
  -- Separation.agda): in a max-plus instance 𝟙 ≼ val 1 ≼ val 2, in a
  -- min-plus (loss) instance the numerically smaller grade is ABOVE.
  _≼_ : Grade → Grade → Set
  a ≼ b = (a ⊕ b) ≡ b

  ≼-refl : ∀ a → a ≼ a
  ≼-refl a = IsAltMonoid.idem alt a

  ≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
  ≼-trans {a} {b} {c} p q =
    trans (cong (a ⊕_) (sym q))
    (trans (sym (IsAltMonoid.assoc alt a b c))
    (trans (cong (_⊕ c) p) q))

  ≼-antisym : ∀ {a b} → a ≼ b → b ≼ a → a ≡ b
  ≼-antisym {a} {b} p q = trans (sym q) (trans (IsAltMonoid.comm alt b a) p)

  𝟘-least : ∀ a → 𝟘 ≼ a
  𝟘-least = IsAltMonoid.unitˡ alt

  ⊕-upperˡ : ∀ a b → a ≼ (a ⊕ b)
  ⊕-upperˡ a b =
    trans (sym (IsAltMonoid.assoc alt a a b))
          (cong (_⊕ b) (IsAltMonoid.idem alt a))

  ⊕-upperʳ : ∀ a b → b ≼ (a ⊕ b)
  ⊕-upperʳ a b =
    trans (cong (b ⊕_) (IsAltMonoid.comm alt a b))
    (trans (sym (IsAltMonoid.assoc alt b b a))
    (trans (cong (_⊕ a) (IsAltMonoid.idem alt b))
           (IsAltMonoid.comm alt b a)))

  -- (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
  ⊕-interchange : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
  ⊕-interchange a b c d =
    trans (IsAltMonoid.assoc alt a b (c ⊕ d))
    (trans (cong (a ⊕_)
      (trans (sym (IsAltMonoid.assoc alt b c d))
      (trans (cong (_⊕ d) (IsAltMonoid.comm alt b c))
             (IsAltMonoid.assoc alt c b d))))
    (sym (IsAltMonoid.assoc alt a c (b ⊕ d))))

  -- Alternatives are monotone in every resource algebra.
  ⊕-mono : ∀ {a a' b b'} → a ≼ a' → b ≼ b' → (a ⊕ b) ≼ (a' ⊕ b')
  ⊕-mono {a} {a'} {b} {b'} p q =
    trans (⊕-interchange a b a' b') (cong₂ _⊕_ p q)

record IsOrdered (R : ResourceAlgebra) : Set where
  open ResourceAlgebra R
  field
    ⊗-monoˡ : ∀ c {a b} → a ≼ b → (c ⊗ a) ≼ (c ⊗ b)
    ⊗-monoʳ : ∀ c {a b} → a ≼ b → (a ⊗ c) ≼ (b ⊗ c)

  ⊗-mono : ∀ {a a' b b'} → a ≼ a' → b ≼ b' → (a ⊗ b) ≼ (a' ⊗ b')
  ⊗-mono {a} {a'} {b} {b'} p q = ≼-trans (⊗-monoʳ b p) (⊗-monoˡ a' q)

record IsDioid (R : ResourceAlgebra) : Set where
  open ResourceAlgebra R
  field
    distribˡ : ∀ a b c → a ⊗ (b ⊕ c) ≡ (a ⊗ b) ⊕ (a ⊗ c)
    distribʳ : ∀ a b c → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊗ c)

  -- Distributivity gives monotonicity of sequencing outright.
  ordered : IsOrdered R
  ordered = record
    { ⊗-monoˡ = λ c {a} {b} p → trans (sym (distribˡ c a b)) (cong (c ⊗_) p)
    ; ⊗-monoʳ = λ c {a} {b} p → trans (sym (distribʳ a b c)) (cong (_⊗ c) p)
    }

record IsAnnihilating (R : ResourceAlgebra) : Set where
  open ResourceAlgebra R
  field
    annihilˡ : ∀ a → 𝟘 ⊗ a ≡ 𝟘
    annihilʳ : ∀ a → a ⊗ 𝟘 ≡ 𝟘
