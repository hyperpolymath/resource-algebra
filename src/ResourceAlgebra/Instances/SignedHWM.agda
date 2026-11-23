{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- STATUS: DESIGNED.  The high-water-mark grade with signed drift: terms
-- may consume live state, so a run may end below where it started.
--
-- Instances.HWM is unchanged; occupancy-types adopts it as is (H-2).  This
-- module is a separate instance, and HWM sits inside it (embed, in
-- Morphism.agda as a lax map, with clamp as a lax retraction).
--
-- A grade records the peak live state above the entry level (a natural:
-- the entry level itself is reached) and the drift at the end (an integer,
-- or −∞), with drift ≤ peak.  Sequencing is HWM's formula read in the
-- integers: peak of a;b is max (peak a) (drift a + peak b), drift adds.
--
-- What changes with consumption:
--   * Componentwise max has no unit on integer drift.  The alternative
--     unit is drift −∞, so 𝟘 ≢ 𝟙 here (in HWM 𝟘 ≡ 𝟙).
--   * 𝟘 absorbs on the left and not on the right: a ; 𝟘 keeps a's peak.
--   * A prefix can lower the peak of what follows it (prefix-lowers-peak);
--     in HWM it never does (HWM-prefix-keeps-peak).
--
-- What does not change: it is a dioid, ordered, and on finite drift its
-- sequence is the bicyclic monoid, with HWM the part where drift ≥ 0
-- (bic, below).
--
-- Not modelled: the trough (the lowest level a run reaches).  A consuming
-- term needs live state on entry; this grade does not record how much.
-- See PROOF-STATUS, "Signed drift".
module ResourceAlgebra.Instances.SignedHWM where

open import Agda.Builtin.Nat using (_-_)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Drift
open import ResourceAlgebra.Instances.HWM as H using (hwm)

private
  module D  = ResourceAlgebra Drift-RA
  module DA = IsAltMonoid (ResourceAlgebra.alt Drift-RA)
  module DS = IsSeqMonoid (ResourceAlgebra.seq Drift-RA)
  module DD = IsDioid Drift-dioid
  module DO = IsOrdered (IsDioid.ordered Drift-dioid)

record Grade : Set where
  constructor shwm
  field
    peak    : Nat
    drift   : Drift
    bounded : drift ≤ᵈ peak

open Grade public using (peak; drift)

shwm-≡ : ∀ {p p' n n'} {b : n ≤ᵈ p} {b' : n' ≤ᵈ p'}
       → p ≡ p' → n ≡ n' → shwm p n b ≡ shwm p' n' b'
shwm-≡ {p} {n = n} {b = b} {b'} refl refl = cong (shwm p n) (≤ᵈ-irrelevant n p b b')

-- Peaks are compared through Drift: clamp is a left inverse of pk.
peak-≡ : ∀ {p q} → pk p ≡ pk q → p ≡ q
peak-≡ = pk-injective

private
  -- max (pk p) y, read as a natural, is a natural again.
  ⌈_,_⌉ : Nat → Drift → Nat
  ⌈ p , y ⌉ = clamp (maxd (pk p) y)

  ⌈⌉-≼ : ∀ p y q → maxd (pk p) y ≼d pk q → ⌈ p , y ⌉ ≤ q
  ⌈⌉-≼ p y q h = pk-≼→≤ (subst (λ z → z ≼d pk q) (sym (pk-clamp p y)) h)

  maxd-dup : ∀ p x y → maxd (maxd p x) (maxd p y) ≡ maxd p (maxd x y)
  maxd-dup p x y =
    trans (D.⊕-interchange p x p y) (cong (λ z → maxd z (maxd x y)) (DA.idem p))

----------------------------------------------------------------------
-- Operations
infixl 7 _⊗s_
_⊗s_ : Grade → Grade → Grade
shwm p₁ n₁ b₁ ⊗s shwm p₂ n₂ b₂ =
  shwm ⌈ p₁ , n₁ +d pk p₂ ⌉ (n₁ +d n₂)
       (≼→≤ᵈ (n₁ +d n₂) ⌈ p₁ , n₁ +d pk p₂ ⌉
         (subst (λ z → (n₁ +d n₂) ≼d z) (sym (pk-clamp p₁ (n₁ +d pk p₂)))
           (D.≼-trans (DO.⊗-monoˡ n₁ (≤ᵈ→≼ n₂ p₂ b₂))
                      (D.⊕-upperʳ (pk p₁) (n₁ +d pk p₂)))))

infixl 6 _⊕s_
_⊕s_ : Grade → Grade → Grade
shwm p₁ n₁ b₁ ⊕s shwm p₂ n₂ b₂ =
  shwm (max p₁ p₂) (maxd n₁ n₂)
       (≼→≤ᵈ (maxd n₁ n₂) (max p₁ p₂)
         (subst (λ z → maxd n₁ n₂ ≼d z) (sym (pk-max p₁ p₂))
           (D.⊕-mono (≤ᵈ→≼ n₁ p₁ b₁) (≤ᵈ→≼ n₂ p₂ b₂))))

-- Nothing on any branch: no peak, and no run ends.
𝟘s : Grade
𝟘s = shwm 0 −∞ tt

-- Doing nothing: no peak, no drift.
𝟙s : Grade
𝟙s = shwm 0 0d tt

----------------------------------------------------------------------
-- Alternatives: componentwise max
⊕s-assoc : ∀ a b c → (a ⊕s b) ⊕s c ≡ a ⊕s (b ⊕s c)
⊕s-assoc (shwm p n _) (shwm p' n' _) (shwm p'' n'' _) =
  shwm-≡ (max-assoc p p' p'') (DA.assoc n n' n'')

⊕s-comm : ∀ a b → a ⊕s b ≡ b ⊕s a
⊕s-comm (shwm p n _) (shwm p' n' _) = shwm-≡ (max-comm p p') (DA.comm n n')

⊕s-idem : ∀ a → a ⊕s a ≡ a
⊕s-idem (shwm p n _) = shwm-≡ (max-idem p) (DA.idem n)

⊕s-unitˡ : ∀ a → 𝟘s ⊕s a ≡ a
⊕s-unitˡ (shwm p n _) = shwm-≡ refl refl

----------------------------------------------------------------------
-- Sequence
⊗s-assoc : ∀ a b c → (a ⊗s b) ⊗s c ≡ a ⊗s (b ⊗s c)
⊗s-assoc (shwm p₁ n₁ _) (shwm p₂ n₂ _) (shwm p₃ n₃ _) =
  shwm-≡ (peak-≡ peaks) (DS.assoc n₁ n₂ n₃)
  where
  P₁ = pk p₁
  P₂ = pk p₂
  P₃ = pk p₃
  peaks : pk ⌈ ⌈ p₁ , n₁ +d P₂ ⌉ , (n₁ +d n₂) +d P₃ ⌉
        ≡ pk ⌈ p₁ , n₁ +d pk ⌈ p₂ , n₂ +d P₃ ⌉ ⌉
  peaks =
    trans (pk-clamp ⌈ p₁ , n₁ +d P₂ ⌉ ((n₁ +d n₂) +d P₃))
    (trans (cong (λ z → maxd z ((n₁ +d n₂) +d P₃)) (pk-clamp p₁ (n₁ +d P₂)))
    (trans (DA.assoc P₁ (n₁ +d P₂) ((n₁ +d n₂) +d P₃))
    (trans (cong (λ z → maxd P₁ (maxd (n₁ +d P₂) z)) (DS.assoc n₁ n₂ P₃))
    (trans (cong (maxd P₁) (sym (DD.distribˡ n₁ P₂ (n₂ +d P₃))))
    (trans (cong (λ z → maxd P₁ (n₁ +d z)) (sym (pk-clamp p₂ (n₂ +d P₃))))
           (sym (pk-clamp p₁ (n₁ +d pk ⌈ p₂ , n₂ +d P₃ ⌉))))))))

⊗s-unitˡ : ∀ a → 𝟙s ⊗s a ≡ a
⊗s-unitˡ (shwm p n _) = shwm-≡ (+-identityʳ p) (DS.unitˡ n)

-- a ; (no peak, drift d) keeps a's peak, because a's drift is below it.
peak-seq-flat : ∀ p n → n ≤ᵈ p → ⌈ p , n +d 0d ⌉ ≡ p
peak-seq-flat p n b =
  peak-≡ (trans (pk-clamp p (n +d 0d))
         (trans (cong (maxd (pk p)) (DS.unitʳ n))
         (trans (DA.comm (pk p) n) (≤ᵈ→≼ n p b))))

⊗s-unitʳ : ∀ a → a ⊗s 𝟙s ≡ a
⊗s-unitʳ (shwm p n b) = shwm-≡ (peak-seq-flat p n b) (DS.unitʳ n)

----------------------------------------------------------------------
-- The instance, and its layers
SHWM : ResourceAlgebra
SHWM = record
  { Grade = Grade
  ; _⊕_ = _⊕s_
  ; _⊗_ = _⊗s_
  ; 𝟘 = 𝟘s
  ; 𝟙 = 𝟙s
  ; alt = record { assoc = ⊕s-assoc ; comm = ⊕s-comm ; idem = ⊕s-idem ; unitˡ = ⊕s-unitˡ }
  ; seq = record { assoc = ⊗s-assoc ; unitˡ = ⊗s-unitˡ ; unitʳ = ⊗s-unitʳ }
  }

SHWM-dioid : IsDioid SHWM
SHWM-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }
  where
  distribˡ : ∀ a b c → a ⊗s (b ⊕s c) ≡ (a ⊗s b) ⊕s (a ⊗s c)
  distribˡ (shwm p n _) (shwm p₂ n₂ _) (shwm p₃ n₃ _) =
    shwm-≡ (peak-≡ peaks) (DD.distribˡ n n₂ n₃)
    where
    P = pk p
    P₂ = pk p₂
    P₃ = pk p₃
    peaks : pk ⌈ p , n +d pk (max p₂ p₃) ⌉
          ≡ pk (max ⌈ p , n +d P₂ ⌉ ⌈ p , n +d P₃ ⌉)
    peaks =
      trans (pk-clamp p (n +d pk (max p₂ p₃)))
      (trans (cong (λ z → maxd P (n +d z)) (pk-max p₂ p₃))
      (trans (cong (maxd P) (DD.distribˡ n P₂ P₃))
      (trans (sym (maxd-dup P (n +d P₂) (n +d P₃)))
      (trans (sym (cong₂ maxd (pk-clamp p (n +d P₂)) (pk-clamp p (n +d P₃))))
             (sym (pk-max ⌈ p , n +d P₂ ⌉ ⌈ p , n +d P₃ ⌉))))))

  distribʳ : ∀ a b c → (a ⊕s b) ⊗s c ≡ (a ⊗s c) ⊕s (b ⊗s c)
  distribʳ (shwm p₂ n₂ _) (shwm p₃ n₃ _) (shwm p n _) =
    shwm-≡ (peak-≡ peaks) (DD.distribʳ n₂ n₃ n)
    where
    P = pk p
    P₂ = pk p₂
    P₃ = pk p₃
    peaks : pk ⌈ max p₂ p₃ , maxd n₂ n₃ +d P ⌉
          ≡ pk (max ⌈ p₂ , n₂ +d P ⌉ ⌈ p₃ , n₃ +d P ⌉)
    peaks =
      trans (pk-clamp (max p₂ p₃) (maxd n₂ n₃ +d P))
      (trans (cong₂ maxd (pk-max p₂ p₃) (DD.distribʳ n₂ n₃ P))
      (trans (D.⊕-interchange P₂ P₃ (n₂ +d P) (n₃ +d P))
      (trans (sym (cong₂ maxd (pk-clamp p₂ (n₂ +d P)) (pk-clamp p₃ (n₃ +d P))))
             (sym (pk-max ⌈ p₂ , n₂ +d P ⌉ ⌈ p₃ , n₃ +d P ⌉)))))

SHWM-ordered : IsOrdered SHWM
SHWM-ordered = IsDioid.ordered SHWM-dioid

----------------------------------------------------------------------
-- Units and absorption (D-2)

-- 𝟘 is not 𝟙: componentwise max on integer drift needs a least drift.
SHWM-𝟘≢𝟙 : 𝟘s ≢ 𝟙s
SHWM-𝟘≢𝟙 e = −∞≢fin (cong drift e)
  where
  −∞≢fin : −∞ ≢ 0d
  −∞≢fin ()

-- 𝟘 absorbs on the left.
SHWM-absorbˡ : ∀ a → 𝟘s ⊗s a ≡ 𝟘s
SHWM-absorbˡ (shwm p n _) = shwm-≡ refl refl

-- On the right it keeps the peak of what ran first.
SHWM-seq-𝟘 : ∀ a → a ⊗s 𝟘s ≡ shwm (peak a) −∞ tt
SHWM-seq-𝟘 (shwm p −∞      b) = shwm-≡ refl refl
SHWM-seq-𝟘 (shwm p (fin x) b) = shwm-≡ (peak-seq-flat p (fin x) b) refl

-- So SHWM is not annihilating (its control is tests/reject/SHWMAnnihilates.agda).
SHWM-not-annihilating : ¬ IsAnnihilating SHWM
SHWM-not-annihilating z =
  one≢zero (cong peak (IsAnnihilating.annihilʳ z (shwm 1 0d tt)))
  where
  one≢zero : 1 ≢ 0
  one≢zero ()

----------------------------------------------------------------------
-- A prefix can lower the peak (D-4)

-- In HWM the peak of a ; b is at least the peak of b.
HWM-prefix-keeps-peak : ∀ a b → H.peak b ≤ H.peak (a H.⊗h b)
HWM-prefix-keeps-peak (hwm p₁ n₁ _) (hwm p₂ n₂ _) =
  ≤-trans (≤-+ˡ n₁ p₂) (≤-max-right p₁ (n₁ + p₂))

-- With consumption it is not: free one cell, then allocate one.  The
-- control is tests/reject/SHWMPrefixKeepsPeak.agda.
free-one alloc-one : Grade
free-one  = shwm 0 (fin (negsuc 0)) tt
alloc-one = shwm 1 (pk 1) tt

prefix-lowers-peak : ¬ (∀ a b → peak b ≤ peak (a ⊗s b))
prefix-lowers-peak f with f free-one alloc-one
... | le ()

----------------------------------------------------------------------
-- HWM inside SHWM (the maps are packaged in Morphism.agda, D-3)
embed : H.Grade → Grade
embed (hwm p n b) = shwm p (pk n) (_≤_.unle b)

-- Below zero, a drift counts as 0.
clampG : Grade → H.Grade
clampG (shwm p n b) = hwm p ⌈ 0 , n ⌉ bound
  where
  bound : ⌈ 0 , n ⌉ ≤ p
  bound = ⌈⌉-≼ 0 n p (D.⊕-least (pk-mono z≤n) (≤ᵈ→≼ n p b))

----------------------------------------------------------------------
-- The bicyclic monoid (D-8)
--
-- Read a grade with finite drift as (peak, peak − drift): how high it
-- goes, then how far it comes down.  Sequencing in those coordinates is
-- the bicyclic monoid's product
--     (a , b) · (c , d) = (a + (c ∸ b) , d + (b ∸ c)),
-- and bic is an isomorphism onto the grades with finite drift.  HWM is
-- the part where the fall is at most the peak (b ≤ a), that is drift ≥ 0.
record Bicyclic : Set where
  constructor ⟨_,_⟩
  field
    rise : Nat
    fall : Nat

infixl 7 _·_
_·_ : Bicyclic → Bicyclic → Bicyclic
⟨ a , b ⟩ · ⟨ c , d ⟩ = ⟨ a + (c - b) , d + (b - c) ⟩

private
  ≤ᵈ-suc : ∀ d p → d ≤ᵈ p → d ≤ᵈ suc p
  ≤ᵈ-suc −∞               p b = tt
  ≤ᵈ-suc (fin (pos n))    p b = _≤_.unle (≤-trans {n} {p} {suc p} (le b) (≤-+ˡ 1 p))
  ≤ᵈ-suc (fin (negsuc _)) p b = tt

  ⊖-≤ᵈ : ∀ a b → fin (a ⊖ b) ≤ᵈ a
  ⊖-≤ᵈ a       zero    = _≤_.unle (≤-refl a)
  ⊖-≤ᵈ zero    (suc b) = tt
  ⊖-≤ᵈ (suc a) (suc b) = ≤ᵈ-suc (fin (a ⊖ b)) a (⊖-≤ᵈ a b)

  -- max b c ≡ (c ∸ b) + b
  max-monus : ∀ b c → max b c ≡ (c - b) + b
  max-monus zero    c       = sym (+-identityʳ c)
  max-monus (suc b) zero    = refl
  max-monus (suc b) (suc c) =
    trans (cong suc (max-monus b c)) (sym (+-suc (c - b) b))

  monus-+ : ∀ n p → n ≤ p → (p - n) + n ≡ p
  monus-+ n p q = trans (sym (max-monus n p)) (max-≤ q)

  monus-≤ : ∀ a b → a - b ≤ a
  monus-≤ a       zero    = ≤-refl a
  monus-≤ zero    (suc b) = z≤n
  monus-≤ (suc a) (suc b) = ≤-trans (monus-≤ a b) (≤-+ˡ 1 a)

bic : Bicyclic → Grade
bic ⟨ a , b ⟩ = shwm a (fin (a ⊖ b)) (⊖-≤ᵈ a b)

bic-𝟙 : bic ⟨ 0 , 0 ⟩ ≡ 𝟙s
bic-𝟙 = shwm-≡ refl refl

bic-· : ∀ x y → bic (x · y) ≡ bic x ⊗s bic y
bic-· ⟨ a , b ⟩ ⟨ c , d ⟩ = shwm-≡ (peak-≡ peaks) (cong fin drifts)
  where
  peaks : pk (a + (c - b)) ≡ pk ⌈ a , fin (a ⊖ b) +d pk c ⌉
  peaks = sym
    (trans (pk-clamp a (fin ((a ⊖ b) +ℤ pos c)))
    (trans (cong (λ z → fin (maxℤ (pos a) z)) (+ℤ-⊖ˡ a b (pos c)))
    (trans (cong fin (maxℤ-⊖ʳ (pos a) (a + c) (b + 0)))
           (cong fin (⊖-≡ _ (0 + (b + 0)) (a + (c - b)) 0 e)))))
    where
    e : max (a + (b + 0)) ((a + c) + 0) + 0 ≡ (a + (c - b)) + (0 + (b + 0))
    e = trans (+-identityʳ _)
        (trans (cong₂ max (cong (a +_) (+-identityʳ b)) (+-identityʳ (a + c)))
        (trans (sym (+-distribˡ-max a b c))
        (trans (cong (a +_) (max-monus b c))
        (trans (sym (+-assoc a (c - b) b))
               (cong ((a + (c - b)) +_) (sym (+-identityʳ b)))))))
  drifts : (a + (c - b)) ⊖ (d + (b - c)) ≡ (a ⊖ b) +ℤ (c ⊖ d)
  drifts = trans (⊖-≡ _ _ (a + c) (b + d) e) (sym (+ℤ-⊖ a b c d))
    where
    e : (a + (c - b)) + (b + d) ≡ (a + c) + (d + (b - c))
    e = trans (sym (+-assoc (a + (c - b)) b d))
        (trans (cong (_+ d) (+-assoc a (c - b) b))
        (trans (cong (λ z → (a + z) + d)
                 (trans (sym (max-monus b c))
                 (trans (max-comm b c)
                 (trans (max-monus c b) (+-comm (b - c) c)))))
        (trans (cong (_+ d) (sym (+-assoc a c (b - c))))
        (trans (+-assoc (a + c) (b - c) d)
               (cong ((a + c) +_) (+-comm (b - c) d))))))

bic-injective : ∀ {x y} → bic x ≡ bic y → x ≡ y
bic-injective {⟨ a , b ⟩} {⟨ c , d ⟩} e with cong peak e
... | refl = cong ⟨ a ,_⟩ (⊖-injʳ a (fin-injective (cong drift e)))

Finite : Grade → Set
Finite (shwm _ −∞      _) = ⊥
Finite (shwm _ (fin _) _) = ⊤

bic-finite : ∀ x → Finite (bic x)
bic-finite ⟨ a , b ⟩ = tt

bic-onto : ∀ g → Finite g → Σ Bicyclic (λ x → bic x ≡ g)
bic-onto (shwm p −∞               _) ()
bic-onto (shwm p (fin (pos n))    b) _ =
  ⟨ p , p - n ⟩ ,
  shwm-≡ refl (cong fin (⊖-≡ p (p - n) n 0
    (trans (+-identityʳ p) (trans (sym (monus-+ n p (le b))) (+-comm (p - n) n)))))
bic-onto (shwm p (fin (negsuc n)) b) _ =
  ⟨ p , p + suc n ⟩ ,
  shwm-≡ refl (cong fin
    (trans (cong (_⊖ (p + suc n)) (sym (+-identityʳ p))) (⊖-cancel p 0 (suc n))))

-- HWM is the part with fall ≤ rise: embed lands there, and every such
-- pair comes from HWM.
bic-HWM : ∀ p n (b : n ≤ p) → bic ⟨ p , p - n ⟩ ≡ embed (hwm p n b)
bic-HWM p n b =
  shwm-≡ refl (cong fin (⊖-≡ p (p - n) n 0
    (trans (+-identityʳ p) (trans (sym (monus-+ n p b)) (+-comm (p - n) n)))))

HWM-bic : ∀ a b → b ≤ a → Σ H.Grade (λ h → embed h ≡ bic ⟨ a , b ⟩)
HWM-bic a b q =
  hwm a (a - b) (monus-≤ a b) ,
  shwm-≡ refl (cong fin (sym (⊖-pos a b q)))
