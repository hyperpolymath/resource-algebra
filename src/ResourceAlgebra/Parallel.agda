{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Parallel composition, as a layer over a resource algebra.
--
--   IsParallel R _∥_   _∥_ is a commutative monoid on R's 𝟙 and distributes
--                      over ⊕ (hence is monotone).  Nothing relates it to ⊗.
--   SyncBelow R _∥_    (a ∥ b) ⊗ (c ∥ d) ≼ (a ⊗ c) ∥ (b ⊗ d): two threads
--                      that meet in the middle are graded at most as two
--                      threads that run free.  The exchange law of a
--                      concurrent semiring.  Space-like resources have it.
--   SyncAbove R _∥_    the reverse bound: meeting in the middle is graded at
--                      least as running free.  Time-like resources have it.
--
-- The direction is a property of the resource, not a convention, so the
-- two laws are stated apart and no layer asks for one of them:
--
--   seq-parallel       any dioid with a commutative ⊗ is parallel with
--                      _∥_ = _⊗_, and has both laws, as an equality.  This
--                      is "work": Loss and MaxPlus under +.
--   MaxPlus-span       ∥ = max on finite costs (elapsed time on unbounded
--                      processors).  SyncAbove holds, SyncBelow does not.
--   HWM-parallel       ∥ = sum of peaks and of drifts (two threads may hold
--                      their peaks together).  SyncBelow holds, SyncAbove
--                      does not.
module ResourceAlgebra.Parallel where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss    as L using (Loss; Loss-dioid; fin; inf; _+g_)
open import ResourceAlgebra.Instances.MaxPlus as M using (MaxPlus; MaxPlus-dioid; Tropical; val; bot; tAdd; tMul)
open import ResourceAlgebra.Instances.HWM     as H using (HWM; hwm; hwm-≡; _⊕h_; _⊗h_; 𝟘h; peak)

----------------------------------------------------------------------
-- The layer and the two exchange laws
module _ (R : ResourceAlgebra) where
  open ResourceAlgebra R
  private
    module S = IsSeqMonoid seq

  record IsParallel (_∥_ : Grade → Grade → Grade) : Set where
    field
      assoc    : ∀ a b c → (a ∥ b) ∥ c ≡ a ∥ (b ∥ c)
      comm     : ∀ a b → a ∥ b ≡ b ∥ a
      unitˡ    : ∀ a → 𝟙 ∥ a ≡ a
      distribˡ : ∀ a b c → a ∥ (b ⊕ c) ≡ (a ∥ b) ⊕ (a ∥ c)

    unitʳ : ∀ a → a ∥ 𝟙 ≡ a
    unitʳ a = trans (comm a 𝟙) (unitˡ a)

    distribʳ : ∀ a b c → (a ⊕ b) ∥ c ≡ (a ∥ c) ⊕ (b ∥ c)
    distribʳ a b c =
      trans (comm (a ⊕ b) c)
      (trans (distribˡ c a b) (cong₂ _⊕_ (comm c a) (comm c b)))

    -- Distributing over alternatives is already monotonicity.
    monoˡ : ∀ c {a b} → a ≼ b → (c ∥ a) ≼ (c ∥ b)
    monoˡ c {a} {b} p = trans (sym (distribˡ c a b)) (cong (λ z → c ∥ z) p)

    monoʳ : ∀ c {a b} → a ≼ b → (a ∥ c) ≼ (b ∥ c)
    monoʳ c {a} {b} p = trans (sym (distribʳ a b c)) (cong (λ z → z ∥ c) p)

  SyncBelow SyncAbove : (Grade → Grade → Grade) → Set
  SyncBelow _∥_ = ∀ a b c d → ((a ∥ b) ⊗ (c ∥ d)) ≼ ((a ⊗ c) ∥ (b ⊗ d))
  SyncAbove _∥_ = ∀ a b c d → ((a ⊗ c) ∥ (b ⊗ d)) ≼ ((a ∥ b) ⊗ (c ∥ d))

  -- Work: a commutative sequence is its own parallel composition.
  module _ (D : IsDioid R) (⊗-comm : ∀ a b → a ⊗ b ≡ b ⊗ a) where
    seq-parallel : IsParallel _⊗_
    seq-parallel = record
      { assoc = S.assoc ; comm = ⊗-comm ; unitˡ = S.unitˡ
      ; distribˡ = IsDioid.distribˡ D }

    ⊗-interchange : ∀ a b c d → (a ⊗ b) ⊗ (c ⊗ d) ≡ (a ⊗ c) ⊗ (b ⊗ d)
    ⊗-interchange a b c d =
      trans (S.assoc a b (c ⊗ d))
      (trans (cong (λ z → a ⊗ z)
        (trans (sym (S.assoc b c d))
        (trans (cong (λ z → z ⊗ d) (⊗-comm b c))
               (S.assoc c b d))))
      (sym (S.assoc a c (b ⊗ d))))

    seq-sync-below : SyncBelow _⊗_
    seq-sync-below a b c d =
      subst (λ x → ((a ⊗ b) ⊗ (c ⊗ d)) ≼ x) (⊗-interchange a b c d)
            (≼-refl ((a ⊗ b) ⊗ (c ⊗ d)))

    seq-sync-above : SyncAbove _⊗_
    seq-sync-above a b c d =
      subst (λ x → x ≼ ((a ⊗ b) ⊗ (c ⊗ d))) (⊗-interchange a b c d)
            (≼-refl ((a ⊗ b) ⊗ (c ⊗ d)))

----------------------------------------------------------------------
-- ℕ lemmas used below
+-mono-≤ : ∀ {m m' n n'} → m ≤ m' → n ≤ n' → m + n ≤ m' + n'
+-mono-≤ {m' = m'} {n = n} p q = ≤-trans (+-monoˡ-≤ n p) (+-monoʳ-≤ m' q)

+-interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d =
  trans (+-assoc a b (c + d))
  (trans (cong (a +_)
    (trans (sym (+-assoc b c d))
    (trans (cong (_+ d) (+-comm b c))
           (+-assoc c b d))))
  (sym (+-assoc a c (b + d))))

----------------------------------------------------------------------
-- Work: Loss and MaxPlus, parallel = sequence
+g-comm : ∀ a b → a +g b ≡ b +g a
+g-comm (fin a) (fin b) = cong fin (+-comm a b)
+g-comm (fin a) inf     = refl
+g-comm inf     (fin b) = refl
+g-comm inf     inf     = refl

Loss-parallel : IsParallel Loss _+g_
Loss-parallel = seq-parallel Loss Loss-dioid +g-comm

Loss-sync-below : SyncBelow Loss _+g_
Loss-sync-below = seq-sync-below Loss Loss-dioid +g-comm

Loss-sync-above : SyncAbove Loss _+g_
Loss-sync-above = seq-sync-above Loss Loss-dioid +g-comm

tMul-comm : ∀ a b → tMul a b ≡ tMul b a
tMul-comm (val a) (val b) = cong val (+-comm a b)
tMul-comm (val a) bot     = refl
tMul-comm bot     (val b) = refl
tMul-comm bot     bot     = refl

MaxPlus-work : IsParallel MaxPlus tMul
MaxPlus-work = seq-parallel MaxPlus MaxPlus-dioid tMul-comm

MaxPlus-work-sync-below : SyncBelow MaxPlus tMul
MaxPlus-work-sync-below = seq-sync-below MaxPlus MaxPlus-dioid tMul-comm

MaxPlus-work-sync-above : SyncAbove MaxPlus tMul
MaxPlus-work-sync-above = seq-sync-above MaxPlus MaxPlus-dioid tMul-comm

----------------------------------------------------------------------
-- Span: MaxPlus, parallel = max on finite costs
tPar : Tropical → Tropical → Tropical
tPar bot     _       = bot
tPar (val m) bot     = bot
tPar (val m) (val n) = val (max m n)

MaxPlus-span : IsParallel MaxPlus tPar
MaxPlus-span = record
  { assoc = assoc ; comm = comm ; unitˡ = unitˡ ; distribˡ = distribˡ }
  where
  assoc : ∀ a b c → tPar (tPar a b) c ≡ tPar a (tPar b c)
  assoc (val a) (val b) (val c) = cong val (max-assoc a b c)
  assoc (val a) (val b) bot     = refl
  assoc (val a) bot     c       = refl
  assoc bot     b       c       = refl

  comm : ∀ a b → tPar a b ≡ tPar b a
  comm (val a) (val b) = cong val (max-comm a b)
  comm (val a) bot     = refl
  comm bot     (val b) = refl
  comm bot     bot     = refl

  unitˡ : ∀ a → tPar (val 0) a ≡ a
  unitˡ (val a) = refl
  unitˡ bot     = refl

  distribˡ : ∀ a b c → tPar a (tAdd b c) ≡ tAdd (tPar a b) (tPar a c)
  distribˡ (val a) (val b) (val c) = cong val (sym (max-dup a b c))
  distribˡ (val a) (val b) bot     = refl
  distribˡ (val a) bot     (val c) = refl
  distribˡ (val a) bot     bot     = refl
  distribˡ bot     b       c       = refl

-- max (a + c) (b + d) ≤ max a b + max c d: threads that meet in the
-- middle wait for the slower half twice.
MaxPlus-span-sync-above : SyncAbove MaxPlus tPar
MaxPlus-span-sync-above (val a) (val b) (val c) (val d) =
  cong val (max-≤ (max-lub
    (+-mono-≤ (≤-max-left a b)  (≤-max-left c d))
    (+-mono-≤ (≤-max-right a b) (≤-max-right c d))))
MaxPlus-span-sync-above (val a) (val b) (val c) bot     = refl
MaxPlus-span-sync-above (val a) (val b) bot     d       = refl
MaxPlus-span-sync-above (val a) bot     (val c) d       = refl
MaxPlus-span-sync-above (val a) bot     bot     d       = refl
MaxPlus-span-sync-above bot     b       c       d       = refl

-- The other direction fails: costs 1 ∥ 0 then 0 ∥ 1 take 2 when the
-- threads meet in the middle and 1 when they run free.  The control is
-- tests/reject/SpanSyncBelow.agda.
MaxPlus-span-not-sync-below : ¬ SyncBelow MaxPlus tPar
MaxPlus-span-not-sync-below f with f (val 1) (val 0) (val 0) (val 1)
... | ()

----------------------------------------------------------------------
-- Occupancy: HWM, parallel = sum of peaks and sum of drifts
infixl 7 _∥h_
_∥h_ : H.Grade → H.Grade → H.Grade
hwm p₁ n₁ b₁ ∥h hwm p₂ n₂ b₂ = hwm (p₁ + p₂) (n₁ + n₂) (+-mono-≤ b₁ b₂)

HWM-parallel : IsParallel HWM _∥h_
HWM-parallel = record
  { assoc = assoc ; comm = comm ; unitˡ = unitˡ ; distribˡ = distribˡ }
  where
  assoc : ∀ a b c → (a ∥h b) ∥h c ≡ a ∥h (b ∥h c)
  assoc (hwm p n _) (hwm p' n' _) (hwm p'' n'' _) =
    hwm-≡ (+-assoc p p' p'') (+-assoc n n' n'')

  comm : ∀ a b → a ∥h b ≡ b ∥h a
  comm (hwm p n _) (hwm p' n' _) = hwm-≡ (+-comm p p') (+-comm n n')

  unitˡ : ∀ a → 𝟘h ∥h a ≡ a
  unitˡ (hwm p n _) = hwm-≡ refl refl

  distribˡ : ∀ a b c → a ∥h (b ⊕h c) ≡ (a ∥h b) ⊕h (a ∥h c)
  distribˡ (hwm p n _) (hwm p₂ n₂ _) (hwm p₃ n₃ _) =
    hwm-≡ (+-distribˡ-max p p₂ p₃) (+-distribˡ-max n n₂ n₃)

-- max (pa + pb) ((na + nb) + (pc + pd)) ≤ max pa (na + pc) + max pb (nb + pd),
-- and the drifts agree: threads that meet in the middle never hold more
-- than the sum of what each holds running free.
HWM-sync-below : SyncBelow HWM _∥h_
HWM-sync-below (hwm pa na _) (hwm pb nb _) (hwm pc nc _) (hwm pd nd _) =
  hwm-≡
    (max-≤ (max-lub
      (+-mono-≤ (≤-max-left pa (na + pc)) (≤-max-left pb (nb + pd)))
      (subst (λ z → z ≤ max pa (na + pc) + max pb (nb + pd))
             (sym (+-interchange na nb pc pd))
             (+-mono-≤ (≤-max-right pa (na + pc)) (≤-max-right pb (nb + pd))))))
    (max-≤ (subst (λ z → (na + nb) + (nc + nd) ≤ z)
                  (+-interchange na nb nc nd)
                  (≤-refl ((na + nb) + (nc + nd)))))

-- The other direction fails: two threads of peak 1, one before the
-- meeting and one after it, hold 1 when they meet in the middle and are
-- graded 2 running free.  The control is tests/reject/HWMSyncAbove.agda.
HWM-not-sync-above : ¬ SyncAbove HWM _∥h_
HWM-not-sync-above f =
  two≢one (cong peak (f (hwm 1 0 z≤n) 𝟘h 𝟘h (hwm 1 0 z≤n)))
  where
  two≢one : 2 ≢ 1
  two≢one ()
