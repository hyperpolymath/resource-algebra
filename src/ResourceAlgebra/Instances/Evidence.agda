{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The evidence grade: how strongly a proof-ledger row is supported.  The
-- carrier is the closed status vocabulary of standards PROOF-POLICY §5 (the
-- README-EXPLAINME proof ledger), as a chain, weakest first (owner ruling
-- 2026-11-17):
--
--   open < tested-only < argued < proven-with-postulates < proven
--
--   _⊔e_ = alternatives = the STRONGER (join): of two independent supports
--          for one claim, the better one counts;            unit open
--   _⊓e_ = sequence     = the WEAKER (meet): a claim that rests on steps is
--          only as strong as the weakest of them;          unit proven
--
-- So Core's order a ≼ b (a ⊕ b ≡ b) reads "a is no stronger than b", and
-- sequencing is the meet of that order (⊓e-lowerˡ, ⊓e-lowerʳ, ⊓e-greatest).
-- ResourceAlgebra.Ledger uses exactly that to derive a ledger row's status.
--
-- The statuses are coded by their rank (0 to 4) and the operations are min
-- and max on ranks, so every law below is a law of min and max on ℕ.  Every
-- case split is on a status or a ℕ, never on an indexed family, so the
-- canonical profile checks without a warning (see Prelude, _≤_).
module ResourceAlgebra.Instances.Evidence where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

-- The closed vocabulary, weakest first.
data Status : Set where
  open-row tested-only argued proven-with-postulates proven : Status

rank : Status → Nat
rank open-row               = 0
rank tested-only            = 1
rank argued                 = 2
rank proven-with-postulates = 3
rank proven                 = 4

-- Every rank from 4 up names proven.
from-rank : Nat → Status
from-rank 0                           = open-row
from-rank 1                           = tested-only
from-rank 2                           = argued
from-rank 3                           = proven-with-postulates
from-rank (suc (suc (suc (suc _))))   = proven

from-rank-rank : ∀ s → from-rank (rank s) ≡ s
from-rank-rank open-row               = refl
from-rank-rank tested-only            = refl
from-rank-rank argued                 = refl
from-rank-rank proven-with-postulates = refl
from-rank-rank proven                 = refl

rank-≤-4 : ∀ s → rank s ≤ 4
rank-≤-4 open-row               = z≤n
rank-≤-4 tested-only            = s≤s z≤n
rank-≤-4 argued                 = s≤s (s≤s z≤n)
rank-≤-4 proven-with-postulates = s≤s (s≤s (s≤s z≤n))
rank-≤-4 proven                 = ≤-refl 4

rank-from-rank : ∀ {n} → n ≤ 4 → rank (from-rank n) ≡ n
rank-from-rank {0}                                 _       = refl
rank-from-rank {1}                                 _       = refl
rank-from-rank {2}                                 _       = refl
rank-from-rank {3}                                 _       = refl
rank-from-rank {4}                                 _       = refl
rank-from-rank {suc (suc (suc (suc (suc _))))}    (le ())

-- Two statuses with one rank are one status (through from-rank, so no match
-- on an equation between numerals is needed).
rank-injective : ∀ {s t} → rank s ≡ rank t → s ≡ t
rank-injective {s} {t} p =
  trans (sym (from-rank-rank s)) (trans (cong from-rank p) (from-rank-rank t))

----------------------------------------------------------------------
-- The two operations
infixl 6 _⊔e_
infixl 7 _⊓e_
_⊔e_ : Status → Status → Status
s ⊔e t = from-rank (max (rank s) (rank t))

_⊓e_ : Status → Status → Status
s ⊓e t = from-rank (min (rank s) (rank t))

rank-⊔e : ∀ s t → rank (s ⊔e t) ≡ max (rank s) (rank t)
rank-⊔e s t = rank-from-rank (max-lub (rank-≤-4 s) (rank-≤-4 t))

rank-⊓e : ∀ s t → rank (s ⊓e t) ≡ min (rank s) (rank t)
rank-⊓e s t = rank-from-rank (≤-trans (min-≤-left (rank s) (rank t)) (rank-≤-4 s))

----------------------------------------------------------------------
-- Alternatives: (⊔e, open-row) is an idempotent commutative monoid
⊔e-assoc : ∀ a b c → (a ⊔e b) ⊔e c ≡ a ⊔e (b ⊔e c)
⊔e-assoc a b c = rank-injective
  (trans (rank-⊔e (a ⊔e b) c)
  (trans (cong (λ x → max x (rank c)) (rank-⊔e a b))
  (trans (max-assoc (rank a) (rank b) (rank c))
  (trans (cong (max (rank a)) (sym (rank-⊔e b c)))
         (sym (rank-⊔e a (b ⊔e c)))))))

⊔e-comm : ∀ a b → a ⊔e b ≡ b ⊔e a
⊔e-comm a b = cong from-rank (max-comm (rank a) (rank b))

⊔e-idem : ∀ a → a ⊔e a ≡ a
⊔e-idem a = trans (cong from-rank (max-idem (rank a))) (from-rank-rank a)

⊔e-unitˡ : ∀ a → open-row ⊔e a ≡ a
⊔e-unitˡ a = from-rank-rank a

----------------------------------------------------------------------
-- Sequence: (⊓e, proven) is a monoid
⊓e-assoc : ∀ a b c → (a ⊓e b) ⊓e c ≡ a ⊓e (b ⊓e c)
⊓e-assoc a b c = rank-injective
  (trans (rank-⊓e (a ⊓e b) c)
  (trans (cong (λ x → min x (rank c)) (rank-⊓e a b))
  (trans (min-assoc (rank a) (rank b) (rank c))
  (trans (cong (min (rank a)) (sym (rank-⊓e b c)))
         (sym (rank-⊓e a (b ⊓e c)))))))

⊓e-comm : ∀ a b → a ⊓e b ≡ b ⊓e a
⊓e-comm a b = cong from-rank (min-comm (rank a) (rank b))

⊓e-unitˡ : ∀ a → proven ⊓e a ≡ a
⊓e-unitˡ a = trans (cong from-rank (min-≥ (rank-≤-4 a))) (from-rank-rank a)

⊓e-unitʳ : ∀ a → a ⊓e proven ≡ a
⊓e-unitʳ a = trans (⊓e-comm a proven) (⊓e-unitˡ a)

Evidence : ResourceAlgebra
Evidence = record
  { Grade = Status
  ; _⊕_   = _⊔e_
  ; _⊗_   = _⊓e_
  ; 𝟘     = open-row
  ; 𝟙     = proven
  ; alt   = record { assoc = ⊔e-assoc ; comm = ⊔e-comm ; idem = ⊔e-idem ; unitˡ = ⊔e-unitˡ }
  ; seq   = record { assoc = ⊓e-assoc ; unitˡ = ⊓e-unitˡ ; unitʳ = ⊓e-unitʳ }
  }

open ResourceAlgebra Evidence using (_≼_)

----------------------------------------------------------------------
-- Dioid, ordered, annihilating
⊓e-distribˡ : ∀ a b c → a ⊓e (b ⊔e c) ≡ (a ⊓e b) ⊔e (a ⊓e c)
⊓e-distribˡ a b c = rank-injective
  (trans (rank-⊓e a (b ⊔e c))
  (trans (cong (min (rank a)) (rank-⊔e b c))
  (trans (min-distribˡ-max (rank a) (rank b) (rank c))
  (trans (cong₂ max (sym (rank-⊓e a b)) (sym (rank-⊓e a c)))
         (sym (rank-⊔e (a ⊓e b) (a ⊓e c)))))))

⊓e-distribʳ : ∀ a b c → (a ⊔e b) ⊓e c ≡ (a ⊓e c) ⊔e (b ⊓e c)
⊓e-distribʳ a b c =
  trans (⊓e-comm (a ⊔e b) c)
  (trans (⊓e-distribˡ c a b)
         (cong₂ _⊔e_ (⊓e-comm c a) (⊓e-comm c b)))

Evidence-dioid : IsDioid Evidence
Evidence-dioid = record { distribˡ = ⊓e-distribˡ ; distribʳ = ⊓e-distribʳ }

Evidence-ordered : IsOrdered Evidence
Evidence-ordered = IsDioid.ordered Evidence-dioid

Evidence-annihilating : IsAnnihilating Evidence
Evidence-annihilating = record
  { annihilˡ = λ _ → refl
  ; annihilʳ = λ a → cong from-rank (min-zeroʳ (rank a)) }

----------------------------------------------------------------------
-- The order is the rank order, and sequencing is its meet
≼→≤ : ∀ {a b} → a ≼ b → rank a ≤ rank b
≼→≤ {a} {b} p = max-≡→≤ (trans (sym (rank-⊔e a b)) (cong rank p))

≤→≼ : ∀ {a b} → rank a ≤ rank b → a ≼ b
≤→≼ {a} {b} p = trans (cong from-rank (max-≤ p)) (from-rank-rank b)

≼-proven : ∀ a → a ≼ proven
≼-proven a = ≤→≼ (rank-≤-4 a)

⊓e-lowerˡ : ∀ a b → (a ⊓e b) ≼ a
⊓e-lowerˡ a b = ≤→≼ (subst (λ x → x ≤ rank a) (sym (rank-⊓e a b)) (min-≤-left (rank a) (rank b)))

⊓e-lowerʳ : ∀ a b → (a ⊓e b) ≼ b
⊓e-lowerʳ a b = ≤→≼ (subst (λ x → x ≤ rank b) (sym (rank-⊓e a b)) (min-≤-right (rank a) (rank b)))

⊓e-greatest : ∀ {a b c} → c ≼ a → c ≼ b → c ≼ (a ⊓e b)
⊓e-greatest {a} {b} {c} p q =
  ≤→≼ (subst (λ x → rank c ≤ x) (sym (rank-⊓e a b)) (min-glb (≼→≤ p) (≼→≤ q)))
