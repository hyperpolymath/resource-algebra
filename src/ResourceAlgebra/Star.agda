{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The loop grade, as a layer over a resource algebra.
--
--   IsStar R star   star a is the grade of "a, any number of times": it is
--                   a fixed point of x ↦ 𝟙 ⊕ (a ⊗ x) and the least one, on
--                   both sides (Kozen's axioms for a Kleene algebra).
--
-- Which algebras have one:
--
--   unit-top-star   if 𝟙 is the greatest grade, star a = 𝟙 for every a:
--                   a loop grades as doing nothing.  Loss is the case here
--                   (the best run of a loop takes no turn).
--   no-star         a grade a with no fixed point at all rules a star out.
--                   MaxPlus (val 1) and HWM (hwm 1 1) have one: the costs
--                   of 1, 2, 3, ... turns have no bound in the carrier.
--   MaxPlusTop      MaxPlus with a top (+∞) has a star: bot and val 0 loop
--                   for nothing, every dearer body loops to top.  MaxPlus
--                   embeds in it by a strict, injective morphism (lift-hom).
module ResourceAlgebra.Star where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Morphism using (Hom)
open import ResourceAlgebra.Instances.Loss       as L using (Loss; fin; inf; _⊓g_)
open import ResourceAlgebra.Instances.MaxPlus    as M using (MaxPlus; Tropical; tAdd; tMul)
open import ResourceAlgebra.Instances.HWM        as H using (HWM; hwm; _⊕h_; _⊗h_; 𝟘h; drift)
open import ResourceAlgebra.Instances.MaxPlusTop as T
  using (MaxPlusTop; bot; val; top; _⊕t_; _⊗t_; ⊗t-unitˡ; ⊗t-comm)

----------------------------------------------------------------------
-- The layer
module _ (R : ResourceAlgebra) where
  open ResourceAlgebra R
  private
    module A = IsAltMonoid alt
    module S = IsSeqMonoid seq

  record IsStar (star : Grade → Grade) : Set where
    field
      unfold : ∀ a → 𝟙 ⊕ (a ⊗ star a) ≡ star a
      leastˡ : ∀ a b x → (b ⊕ (a ⊗ x)) ≼ x → (star a ⊗ b) ≼ x
      leastʳ : ∀ a b x → (b ⊕ (x ⊗ a)) ≼ x → (b ⊗ star a) ≼ x

    -- The loop grade bounds no turn and one more turn.
    star-𝟙 : ∀ a → 𝟙 ≼ star a
    star-𝟙 a = subst (λ z → 𝟙 ≼ z) (unfold a) (⊕-upperˡ 𝟙 (a ⊗ star a))

    star-step : ∀ a → (a ⊗ star a) ≼ star a
    star-step a =
      subst (λ z → (a ⊗ star a) ≼ z) (unfold a) (⊕-upperʳ 𝟙 (a ⊗ star a))

  -- If 𝟙 is the greatest grade, every loop grades as 𝟙.
  unit-top-star : (∀ a → a ≼ 𝟙) → IsStar (λ _ → 𝟙)
  unit-top-star greatest = record
    { unfold = λ a → trans (A.comm 𝟙 (a ⊗ 𝟙)) (greatest (a ⊗ 𝟙))
    ; leastˡ = λ a b x h →
        subst (λ z → z ≼ x) (sym (S.unitˡ b)) (≼-trans (⊕-upperˡ b (a ⊗ x)) h)
    ; leastʳ = λ a b x h →
        subst (λ z → z ≼ x) (sym (S.unitʳ b)) (≼-trans (⊕-upperˡ b (x ⊗ a)) h)
    }

  -- A grade whose loop equation has no solution rules a star out.
  NoFixpoint : Grade → Set
  NoFixpoint a = ∀ s → (𝟙 ⊕ (a ⊗ s)) ≢ s

  no-star : ∀ a → NoFixpoint a → (star : Grade → Grade) → ¬ IsStar star
  no-star a nf star st = nf (star a) (IsStar.unfold st a)

----------------------------------------------------------------------
-- ℕ lemmas used below
suc≢ : ∀ n → suc n ≢ n
suc≢ zero    ()
suc≢ (suc n) e = suc≢ n (suc-injective e)

suc≰ : ∀ m → ¬ (suc m ≤ m)
suc≰ zero    (le ())
suc≰ (suc m) p = suc≰ m (≤-pred p)

-- max (suc n + k) k is never k.
max-suc-+ : ∀ n k → max (suc (n + k)) k ≢ k
max-suc-+ n k e = suc≰ (n + k) (≤-trans (max-≡→≤ e) (≤-+ˡ n k))

----------------------------------------------------------------------
-- Loss: 𝟙 = fin 0 is the greatest grade
Loss-unit-top : ∀ a → a ⊓g fin 0 ≡ fin 0
Loss-unit-top (fin a) = cong fin (min-zeroʳ a)
Loss-unit-top inf     = refl

Loss-star : IsStar Loss (λ _ → fin 0)
Loss-star = unit-top-star Loss Loss-unit-top

----------------------------------------------------------------------
-- MaxPlus and HWM: no star
-- A body of cost 1: s would have to equal max 0 (1 + s).  The control is
-- tests/reject/MaxPlusLoopBounded.agda.
MaxPlus-no-fixpoint : NoFixpoint MaxPlus (M.val 1)
MaxPlus-no-fixpoint (M.val n) e = suc≢ n (M.val-injective e)
MaxPlus-no-fixpoint M.bot     ()

MaxPlus-no-star : (star : Tropical → Tropical) → ¬ IsStar MaxPlus star
MaxPlus-no-star = no-star MaxPlus (M.val 1) MaxPlus-no-fixpoint

-- A body that allocates 1 and keeps it: every turn adds 1 to the drift.
HWM-no-fixpoint : NoFixpoint HWM (hwm 1 1 (le tt))
HWM-no-fixpoint (hwm p n _) e = suc≢ n (cong drift e)

HWM-no-star : (star : H.Grade → H.Grade) → ¬ IsStar HWM star
HWM-no-star = no-star HWM (hwm 1 1 (le tt)) HWM-no-fixpoint

----------------------------------------------------------------------
-- MaxPlusTop: the star
star-t : T.Grade → T.Grade
star-t bot           = val 0
star-t (val zero)    = val 0
star-t (val (suc _)) = top
star-t top           = top

MaxPlusTop-star : IsStar MaxPlusTop star-t
MaxPlusTop-star = record { unfold = unfold ; leastˡ = leastˡ ; leastʳ = leastʳ }
  where
  open ResourceAlgebra MaxPlusTop using (_≼_; ≼-trans; ⊕-upperˡ; ⊕-upperʳ)

  unfold : ∀ a → val 0 ⊕t (a ⊗t star-t a) ≡ star-t a
  unfold bot           = refl
  unfold (val zero)    = refl
  unfold (val (suc _)) = refl
  unfold top           = refl

  -- From b ≼ x and a ⊗t x ≼ x.  A body that costs something, sequenced
  -- before a possible x, forces x to be top.
  go : ∀ a b x → b ≼ x → (a ⊗t x) ≼ x → (star-t a ⊗t b) ≼ x
  go bot           b       x       hb _  = subst (λ z → z ≼ x) (sym (⊗t-unitˡ b)) hb
  go (val zero)    b       x       hb _  = subst (λ z → z ≼ x) (sym (⊗t-unitˡ b)) hb
  go (val (suc n)) bot     x       _  _  = refl
  go (val (suc n)) (val m) bot     () _
  go (val (suc n)) (val m) (val k) _  ha with max-suc-+ n k (T.val-injective ha)
  ... | ()
  go (val (suc n)) (val m) top     _  _  = refl
  go (val (suc n)) top     bot     () _
  go (val (suc n)) top     (val k) () _
  go (val (suc n)) top     top     _  _  = refl
  go top           bot     x       _  _  = refl
  go top           (val m) bot     () _
  go top           (val m) (val k) _  ()
  go top           (val m) top     _  _  = refl
  go top           top     bot     () _
  go top           top     (val k) () _
  go top           top     top     _  _  = refl

  leastˡ : ∀ a b x → (b ⊕t (a ⊗t x)) ≼ x → (star-t a ⊗t b) ≼ x
  leastˡ a b x h =
    go a b x (≼-trans (⊕-upperˡ b (a ⊗t x)) h) (≼-trans (⊕-upperʳ b (a ⊗t x)) h)

  -- Sequence commutes here, so the right law is the left one.
  leastʳ : ∀ a b x → (b ⊕t (x ⊗t a)) ≼ x → (b ⊗t star-t a) ≼ x
  leastʳ a b x h =
    subst (λ z → z ≼ x) (⊗t-comm (star-t a) b)
      (leastˡ a b x (subst (λ z → (b ⊕t z) ≼ x) (⊗t-comm x a) h))

----------------------------------------------------------------------
-- MaxPlus embeds in MaxPlusTop
lift : Tropical → T.Grade
lift (M.val n) = val n
lift M.bot     = bot

lift-hom : Hom MaxPlus MaxPlusTop
lift-hom = record
  { map = lift ; map-𝟘 = refl ; map-𝟙 = refl ; map-⊕ = ⊕-case ; map-⊗ = ⊗-case }
  where
  ⊕-case : ∀ a b → lift (tAdd a b) ≡ lift a ⊕t lift b
  ⊕-case (M.val a) (M.val b) = refl
  ⊕-case (M.val a) M.bot     = refl
  ⊕-case M.bot     b         = refl

  ⊗-case : ∀ a b → lift (tMul a b) ≡ lift a ⊗t lift b
  ⊗-case (M.val a) (M.val b) = refl
  ⊗-case (M.val a) M.bot     = refl
  ⊗-case M.bot     b         = refl

lift-injective : ∀ a b → lift a ≡ lift b → a ≡ b
lift-injective (M.val a) (M.val b) e = cong M.val (T.val-injective e)
lift-injective (M.val a) M.bot     ()
lift-injective M.bot     (M.val b) ()
lift-injective M.bot     M.bot     _ = refl
