{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Morphisms between resource algebras (resource-algebra#3).
--
--   Hom A B     strict: preserves 𝟘, 𝟙, ⊕ and ⊗.  What transport of a grade
--               *equality* (K-CUT-LOSS) across instances needs.
--   LaxHom A B  preserves 𝟙 and ⊕ (hence is monotone) and maps ⊗ to at most
--               ⊗: h (a ⊗ b) ≼ h a ⊗ h b.  What transport of a *bound*
--               needs.  𝟘 is not asked for: B's 𝟘 is least, so B.𝟘 ≼ h A.𝟘
--               holds for free (`LaxHom.map-𝟘`).
--
-- Both compose and have identities.  The instances below are the maps the
-- typed-wasm levels actually use, and the classifications show which maps
-- cannot exist:
--
--   peak-lax          HWM → MaxPlus is lax (occupancy never exceeds cost;
--                     occupancy-types R-3); it does not preserve ⊗
--                     (peak-not-strict), and there is no strict map out
--                     of HWM into any algebra with 𝟘 ≢ 𝟙 (no-strict-from-HWM).
--   Loss→MaxPlus      exactly two strict maps, zero-test and support; neither
--                     tells fin 1 from fin 2.
--   MaxPlus→Loss      exactly one strict map, support′.
--   loss-bottleneck   the identity on the carrier is lax Loss → MinMax
--                     (a bottleneck never exceeds the sum); it is not strict
--                     (Separation S-4).
module ResourceAlgebra.Morphism where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss    as L using (Loss; fin; inf; _⊓g_; _+g_)
open import ResourceAlgebra.Instances.MaxPlus as M using (MaxPlus; Tropical; val; bot; tAdd; tMul)
open import ResourceAlgebra.Instances.HWM     as H using (HWM; hwm; peak; _⊕h_; _⊗h_)
open import ResourceAlgebra.Instances.MinMax  as N using (MinMax; _⊔g_)

----------------------------------------------------------------------
-- The two notions
module _ (A B : ResourceAlgebra) where
  private
    module A = ResourceAlgebra A
    module B = ResourceAlgebra B

  record Hom : Set where
    field
      map   : A.Grade → B.Grade
      map-𝟘 : map A.𝟘 ≡ B.𝟘
      map-𝟙 : map A.𝟙 ≡ B.𝟙
      map-⊕ : ∀ a b → map (a A.⊕ b) ≡ map a B.⊕ map b
      map-⊗ : ∀ a b → map (a A.⊗ b) ≡ map a B.⊗ map b

  record LaxHom : Set where
    field
      map   : A.Grade → B.Grade
      map-𝟙 : map A.𝟙 ≡ B.𝟙
      map-⊕ : ∀ a b → map (a A.⊕ b) ≡ map a B.⊕ map b
      map-⊗ : ∀ a b → map (a A.⊗ b) B.≼ (map a B.⊗ map b)

    -- Preserving ⊕ is already monotonicity for the induced order.
    mono : ∀ {a b} → a A.≼ b → map a B.≼ map b
    mono {a} {b} p = trans (sym (map-⊕ a b)) (cong map p)

    map-𝟘 : B.𝟘 B.≼ map A.𝟘
    map-𝟘 = B.𝟘-least (map A.𝟘)

  -- Every strict morphism is lax.
  lax : Hom → LaxHom
  lax h = record
    { map   = Hom.map h
    ; map-𝟙 = Hom.map-𝟙 h
    ; map-⊕ = Hom.map-⊕ h
    ; map-⊗ = λ a b →
        subst (λ x → x B.≼ (Hom.map h a B.⊗ Hom.map h b))
              (sym (Hom.map-⊗ h a b))
              (B.≼-refl (Hom.map h a B.⊗ Hom.map h b))
    }

----------------------------------------------------------------------
-- Identities and composition
id-hom : (A : ResourceAlgebra) → Hom A A
id-hom A = record
  { map = λ a → a ; map-𝟘 = refl ; map-𝟙 = refl
  ; map-⊕ = λ _ _ → refl ; map-⊗ = λ _ _ → refl }

infixr 9 _∘h_
_∘h_ : {A B C : ResourceAlgebra} → Hom B C → Hom A B → Hom A C
g ∘h f = record
  { map   = λ a → Hom.map g (Hom.map f a)
  ; map-𝟘 = trans (cong (Hom.map g) (Hom.map-𝟘 f)) (Hom.map-𝟘 g)
  ; map-𝟙 = trans (cong (Hom.map g) (Hom.map-𝟙 f)) (Hom.map-𝟙 g)
  ; map-⊕ = λ a b → trans (cong (Hom.map g) (Hom.map-⊕ f a b))
                          (Hom.map-⊕ g (Hom.map f a) (Hom.map f b))
  ; map-⊗ = λ a b → trans (cong (Hom.map g) (Hom.map-⊗ f a b))
                          (Hom.map-⊗ g (Hom.map f a) (Hom.map f b))
  }

id-lax : (A : ResourceAlgebra) → LaxHom A A
id-lax A = lax A A (id-hom A)

infixr 9 _∘l_
_∘l_ : {A B C : ResourceAlgebra} → LaxHom B C → LaxHom A B → LaxHom A C
_∘l_ {C = C} g f = record
  { map   = λ a → LaxHom.map g (LaxHom.map f a)
  ; map-𝟙 = trans (cong (LaxHom.map g) (LaxHom.map-𝟙 f)) (LaxHom.map-𝟙 g)
  ; map-⊕ = λ a b → trans (cong (LaxHom.map g) (LaxHom.map-⊕ f a b))
                          (LaxHom.map-⊕ g (LaxHom.map f a) (LaxHom.map f b))
  ; map-⊗ = λ a b → ResourceAlgebra.≼-trans C
                      (LaxHom.mono g (LaxHom.map-⊗ f a b))
                      (LaxHom.map-⊗ g (LaxHom.map f a) (LaxHom.map f b))
  }

----------------------------------------------------------------------
-- HWM → MaxPlus: the peak is a lax morphism, never a strict one
peak-lax : LaxHom HWM MaxPlus
peak-lax = record
  { map   = λ g → val (peak g)
  ; map-𝟙 = refl
  ; map-⊕ = ⊕-case
  ; map-⊗ = ⊗-case
  }
  where
  ⊕-case : ∀ a b → val (peak (a ⊕h b)) ≡ tAdd (val (peak a)) (val (peak b))
  ⊕-case (hwm p n _) (hwm p' n' _) = refl

  -- max p₁ (n₁ + p₂) ≤ p₁ + p₂, because the drift n₁ is at most the peak p₁.
  ⊗-case : ∀ a b → tAdd (val (peak (a ⊗h b))) (tMul (val (peak a)) (val (peak b)))
                 ≡ tMul (val (peak a)) (val (peak b))
  ⊗-case (hwm p₁ n₁ b₁) (hwm p₂ n₂ b₂) =
    cong val (max-≤ (max-lub (≤-+ʳ p₁ p₂) (+-monoˡ-≤ p₂ b₁)))

-- The peak does not preserve ⊗ (F-3): peaks 2 and 3 with no drift sequence
-- to peak 3, while the peaks sum to 5.  This holds whatever the units do;
-- tests/reject/PeakIsStrict.agda is the control.
peak-not-strict : ¬ (∀ a b → val (peak (a ⊗h b)) ≡ tMul (val (peak a)) (val (peak b)))
peak-not-strict f with f (hwm 2 0 z≤n) (hwm 3 0 z≤n)
... | ()

-- HWM's 𝟘 is its 𝟙, so a strict map out of HWM would identify B's 𝟘 and 𝟙.
no-strict-from-HWM : (B : ResourceAlgebra)
                   → ResourceAlgebra.𝟘 B ≢ ResourceAlgebra.𝟙 B
                   → Hom HWM B → ⊥
no-strict-from-HWM B 𝟘≢𝟙 h = 𝟘≢𝟙 (trans (sym (Hom.map-𝟘 h)) (Hom.map-𝟙 h))

no-strict-HWM→MaxPlus : Hom HWM MaxPlus → ⊥
no-strict-HWM→MaxPlus = no-strict-from-HWM MaxPlus (λ ())

no-strict-HWM→Loss : Hom HWM Loss → ⊥
no-strict-HWM→Loss = no-strict-from-HWM Loss (λ ())

----------------------------------------------------------------------
-- Loss → MaxPlus: exactly two strict morphisms
zero-test : L.Grade → Tropical
zero-test (fin zero)    = val 0
zero-test (fin (suc _)) = bot
zero-test inf           = bot

support : L.Grade → Tropical
support (fin _) = val 0
support inf     = bot

zero-test-hom : Hom Loss MaxPlus
zero-test-hom = record
  { map = zero-test ; map-𝟘 = refl ; map-𝟙 = refl ; map-⊕ = ⊕-case ; map-⊗ = ⊗-case }
  where
  ⊕-case : ∀ a b → zero-test (a ⊓g b) ≡ tAdd (zero-test a) (zero-test b)
  ⊕-case (fin zero)    (fin zero)    = refl
  ⊕-case (fin zero)    (fin (suc n)) = refl
  ⊕-case (fin (suc m)) (fin zero)    = refl
  ⊕-case (fin (suc m)) (fin (suc n)) = refl
  ⊕-case (fin zero)    inf           = refl
  ⊕-case (fin (suc m)) inf           = refl
  ⊕-case inf           b             = refl

  ⊗-case : ∀ a b → zero-test (a +g b) ≡ tMul (zero-test a) (zero-test b)
  ⊗-case (fin zero)    (fin zero)    = refl
  ⊗-case (fin zero)    (fin (suc n)) = refl
  ⊗-case (fin (suc m)) (fin n)       = refl
  ⊗-case (fin zero)    inf           = refl
  ⊗-case (fin (suc m)) inf           = refl
  ⊗-case inf           b             = refl

support-hom : Hom Loss MaxPlus
support-hom = record
  { map = support ; map-𝟘 = refl ; map-𝟙 = refl ; map-⊕ = ⊕-case ; map-⊗ = ⊗-case }
  where
  ⊕-case : ∀ a b → support (a ⊓g b) ≡ tAdd (support a) (support b)
  ⊕-case (fin m) (fin n) = refl
  ⊕-case (fin m) inf     = refl
  ⊕-case inf     b       = refl

  ⊗-case : ∀ a b → support (a +g b) ≡ tMul (support a) (support b)
  ⊗-case (fin m) (fin n) = refl
  ⊗-case (fin m) inf     = refl
  ⊗-case inf     b       = refl

val-injective : ∀ {m n} → val m ≡ val n → m ≡ n
val-injective refl = refl

-- Every strict morphism Loss → MaxPlus is zero-test or support, pointwise.
-- fin 0 ⊓g fin 1 = fin 0 forces h (fin 1) ∈ {bot, val 0}; every fin n is
-- fin 1 sequenced n times, so h (fin 1) decides the rest.
Loss→MaxPlus : (h : Hom Loss MaxPlus)
             → (∀ a → Hom.map h a ≡ zero-test a) ⊎ (∀ a → Hom.map h a ≡ support a)
Loss→MaxPlus h = go (Hom.map h (fin 1)) refl
  where
  f = Hom.map h

  step : ∀ n → f (fin (suc n)) ≡ tMul (f (fin 1)) (f (fin n))
  step n = Hom.map-⊗ h (fin 1) (fin n)

  -- val 0 ≡ tAdd (val 0) (f (fin 1))
  pin : val 0 ≡ tAdd (val 0) (f (fin 1))
  pin = trans (sym (Hom.map-𝟙 h))
        (trans (Hom.map-⊕ h (fin 0) (fin 1))
               (cong (λ z → tAdd z (f (fin 1))) (Hom.map-𝟙 h)))

  go : (x : Tropical) → f (fin 1) ≡ x
     → (∀ a → f a ≡ zero-test a) ⊎ (∀ a → f a ≡ support a)
  go bot     e = inj₁ pointwise
    where
    pointwise : ∀ a → f a ≡ zero-test a
    pointwise (fin zero)    = Hom.map-𝟙 h
    pointwise (fin (suc n)) = trans (step n) (cong (λ z → tMul z (f (fin n))) e)
    pointwise inf           = Hom.map-𝟘 h
  go (val c) e = inj₂ pointwise
    where
    c≡0 : c ≡ 0
    c≡0 = sym (val-injective (trans pin (cong (tAdd (val 0)) e)))

    fin-val0 : ∀ n → f (fin n) ≡ val 0
    fin-val0 zero    = Hom.map-𝟙 h
    fin-val0 (suc n) =
      trans (step n)
      (trans (cong (λ z → tMul z (f (fin n))) (trans e (cong val c≡0)))
             (cong (tMul (val 0)) (fin-val0 n)))

    pointwise : ∀ a → f a ≡ support a
    pointwise (fin n) = fin-val0 n
    pointwise inf     = Hom.map-𝟘 h

-- So no strict morphism Loss → MaxPlus tells fin 1 from fin 2: the
-- separation witnesses, stated for every morphism rather than for one.
Loss→MaxPlus-collapses : (h : Hom Loss MaxPlus) → Hom.map h (fin 1) ≡ Hom.map h (fin 2)
Loss→MaxPlus-collapses h with Loss→MaxPlus h
... | inj₁ z = trans (z (fin 1)) (sym (z (fin 2)))
... | inj₂ s = trans (s (fin 1)) (sym (s (fin 2)))

no-injective-Loss→MaxPlus : (h : Hom Loss MaxPlus)
                          → (∀ a b → Hom.map h a ≡ Hom.map h b → a ≡ b) → ⊥
no-injective-Loss→MaxPlus h inj with inj (fin 1) (fin 2) (Loss→MaxPlus-collapses h)
... | ()

----------------------------------------------------------------------
-- MaxPlus → Loss: exactly one strict morphism
support′ : Tropical → L.Grade
support′ (val _) = fin 0
support′ bot     = inf

support′-hom : Hom MaxPlus Loss
support′-hom = record
  { map = support′ ; map-𝟘 = refl ; map-𝟙 = refl ; map-⊕ = ⊕-case ; map-⊗ = ⊗-case }
  where
  ⊕-case : ∀ a b → support′ (tAdd a b) ≡ support′ a ⊓g support′ b
  ⊕-case (val m) (val n) = refl
  ⊕-case (val m) bot     = refl
  ⊕-case bot     b       = refl

  ⊗-case : ∀ a b → support′ (tMul a b) ≡ support′ a +g support′ b
  ⊗-case (val m) (val n) = refl
  ⊗-case (val m) bot     = refl
  ⊗-case bot     b       = refl

fin-injective : ∀ {m n} → fin m ≡ fin n → m ≡ n
fin-injective refl = refl

-- val 0 ⊕ val 1 = val 1 forces h (val 1) = fin 0 ⊓g h (val 1), which rules
-- out inf and pins every finite value to fin 0.
MaxPlus→Loss : (h : Hom MaxPlus Loss) → ∀ a → Hom.map h a ≡ support′ a
MaxPlus→Loss h = pointwise
  where
  f = Hom.map h

  absorb : f (val 1) ≡ fin 0 ⊓g f (val 1)
  absorb = trans (Hom.map-⊕ h (val 0) (val 1))
                 (cong (λ z → z ⊓g f (val 1)) (Hom.map-𝟙 h))

  one : (x : L.Grade) → f (val 1) ≡ x → f (val 1) ≡ fin 0
  one (fin c) e = trans absorb (cong (λ z → fin 0 ⊓g z) e)
  one inf     e with trans (sym e) (trans absorb (cong (λ z → fin 0 ⊓g z) e))
  ... | ()

  val-fin0 : ∀ n → f (val n) ≡ fin 0
  val-fin0 zero    = Hom.map-𝟙 h
  val-fin0 (suc n) =
    trans (Hom.map-⊗ h (val 1) (val n))
    (trans (cong (λ z → z +g f (val n)) (one (f (val 1)) refl))
           (cong (fin 0 +g_) (val-fin0 n)))

  pointwise : ∀ a → f a ≡ support′ a
  pointwise (val n) = val-fin0 n
  pointwise bot     = Hom.map-𝟘 h

----------------------------------------------------------------------
-- Loss → MinMax: the identity on the carrier is lax
loss-bottleneck : LaxHom Loss MinMax
loss-bottleneck = record
  { map = λ a → a ; map-𝟙 = refl ; map-⊕ = λ _ _ → refl ; map-⊗ = ⊗-case }
  where
  -- (a +g b) ≼ (a ⊔g b) in MinMax: the bottleneck is at most the sum.
  ⊗-case : ∀ a b → (a +g b) ⊓g (a ⊔g b) ≡ a ⊔g b
  ⊗-case (fin m) (fin n) = cong fin (min-≥ (max-≤-+ m n))
  ⊗-case (fin m) inf     = refl
  ⊗-case inf     b       = refl
