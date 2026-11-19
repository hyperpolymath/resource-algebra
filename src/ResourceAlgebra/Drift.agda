{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The drift carrier of the signed high-water-mark instance: the integers
-- with a bottom, −∞, under max and +.  It is the max-plus dioid on ℤ
-- (Drift-RA, Drift-dioid), the signed counterpart of Instances.MaxPlus.
--
-- No builtins beyond the Prelude's.  Every integer law is proved here, by
-- one device: an integer is a difference m ⊖ n of naturals, and two
-- differences are equal when their cross sums are (⊖-≡).  Addition and
-- max are defined on the parts (up, dn) of each argument, so each law
-- reduces to an equation between naturals.
--
-- The bound of a signed grade relates a drift to a natural peak
-- (_≤ᵈ_).  It is defined by recursion, so its proofs are unique
-- (≤ᵈ-irrelevant), and it agrees with the order of Drift-RA (≤ᵈ→≼,
-- ≼→≤ᵈ).
module ResourceAlgebra.Drift where

open import Agda.Builtin.Nat using (_-_)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

-- The integers, as Agda.Builtin.Int has them, defined here: the builtin
-- module imports Agda.Builtin.String, whose postulates the trusted-base
-- gate (scripts/check-agda.sh) refuses.
data Int : Set where
  pos    : Nat → Int   -- n
  negsuc : Nat → Int   -- −(n + 1)

----------------------------------------------------------------------
-- ℕ glue
private
  +-inter : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-inter a b c d =
    trans (+-assoc a b (c + d))
    (trans (cong (a +_)
      (trans (sym (+-assoc b c d))
      (trans (cong (_+ d) (+-comm b c))
             (+-assoc c b d))))
    (sym (+-assoc a c (b + d))))

  -- (p + q) + (r + s) ≡ r + (p + (q + s))
  +-rot : ∀ p q r s → (p + q) + (r + s) ≡ r + (p + (q + s))
  +-rot p q r s =
    trans (+-inter p q r s)
    (trans (cong (_+ (q + s)) (+-comm p r))
           (+-assoc r p (q + s)))

  -- (a + b) + c ≡ (a + c) + b
  +-swapʳ : ∀ a b c → (a + b) + c ≡ (a + c) + b
  +-swapʳ a b c =
    trans (+-assoc a b c)
    (trans (cong (a +_) (+-comm b c))
           (sym (+-assoc a c b)))

----------------------------------------------------------------------
-- Integers as differences
infix 6 _⊖_
_⊖_ : Nat → Nat → Int
m     ⊖ zero  = pos m
zero  ⊖ suc n = negsuc n
suc m ⊖ suc n = m ⊖ n

-- The canonical parts: x is up x ⊖ dn x.
up dn : Int → Nat
up (pos n)    = n
up (negsuc _) = zero
dn (pos _)    = zero
dn (negsuc n) = suc n

nf : ∀ x → up x ⊖ dn x ≡ x
nf (pos n)    = refl
nf (negsuc n) = refl

⊖-cancel : ∀ k m n → (k + m) ⊖ (k + n) ≡ m ⊖ n
⊖-cancel zero    m n = refl
⊖-cancel (suc k) m n = ⊖-cancel k m n

-- Differences with equal cross sums are equal.
⊖-≡ : ∀ a b c d → a + d ≡ c + b → a ⊖ b ≡ c ⊖ d
⊖-≡ a b c d e =
  trans (sym (⊖-cancel d a b))
  (trans (cong₂ _⊖_ (trans (+-comm d a) (trans e (+-comm c b))) (+-comm d b))
         (⊖-cancel b c d))

-- The parts of a difference have the cross sum of the difference.
cross : ∀ a b → up (a ⊖ b) + b ≡ dn (a ⊖ b) + a
cross a       zero    = +-identityʳ a
cross zero    (suc n) = sym (+-identityʳ (suc n))
cross (suc m) (suc n) =
  trans (+-suc (up (m ⊖ n)) n)
  (trans (cong suc (cross m n))
         (sym (+-suc (dn (m ⊖ n)) m)))

⊖-injʳ : ∀ a {b d} → a ⊖ b ≡ a ⊖ d → b ≡ d
⊖-injʳ a {b} {d} e =
  +-cancelˡ (up (a ⊖ b))
    (trans (cross a b)
    (trans (cong (λ z → dn z + a) e)
    (trans (sym (cross a d))
           (cong (λ z → up z + d) (sym e)))))

-- A difference whose subtrahend is smaller is a natural.
⊖-pos : ∀ m n → n ≤ m → m ⊖ n ≡ pos (m - n)
⊖-pos m       zero    _      = refl
⊖-pos zero    (suc n) (le ())
⊖-pos (suc m) (suc n) p      = ⊖-pos m n (≤-pred p)

----------------------------------------------------------------------
-- Addition and max on the parts
infixl 6 _+ℤ_
_+ℤ_ : Int → Int → Int
x +ℤ y = (up x + up y) ⊖ (dn x + dn y)

maxℤ : Int → Int → Int
maxℤ x y = max (up x + dn y) (up y + dn x) ⊖ (dn x + dn y)

-- A difference in an argument can be read through its parts.
+ℤ-⊖ˡ : ∀ a b y → (a ⊖ b) +ℤ y ≡ (a + up y) ⊖ (b + dn y)
+ℤ-⊖ˡ a b y = ⊖-≡ (up (a ⊖ b) + up y) (dn (a ⊖ b) + dn y) (a + up y) (b + dn y)
  (trans (+-inter (up (a ⊖ b)) (up y) b (dn y))
  (trans (cong (_+ (up y + dn y)) (cross a b))
  (trans (cong (_+ (up y + dn y)) (+-comm (dn (a ⊖ b)) a))
         (+-inter a (dn (a ⊖ b)) (up y) (dn y)))))

+ℤ-comm : ∀ x y → x +ℤ y ≡ y +ℤ x
+ℤ-comm x y = cong₂ _⊖_ (+-comm (up x) (up y)) (+-comm (dn x) (dn y))

+ℤ-⊖ʳ : ∀ x a b → x +ℤ (a ⊖ b) ≡ (up x + a) ⊖ (dn x + b)
+ℤ-⊖ʳ x a b =
  trans (+ℤ-comm x (a ⊖ b))
  (trans (+ℤ-⊖ˡ a b x)
         (cong₂ _⊖_ (+-comm a (up x)) (+-comm b (dn x))))

+ℤ-⊖ : ∀ a b c d → (a ⊖ b) +ℤ (c ⊖ d) ≡ (a + c) ⊖ (b + d)
+ℤ-⊖ a b c d =
  trans (+ℤ-⊖ˡ a b (c ⊖ d)) (⊖-≡ (a + up (c ⊖ d)) (b + dn (c ⊖ d)) (a + c) (b + d)
    (trans (+-inter a (up (c ⊖ d)) b d)
    (trans (cong ((a + b) +_) (cross c d))
    (trans (cong ((a + b) +_) (+-comm (dn (c ⊖ d)) c))
           (+-inter a b c (dn (c ⊖ d)))))))

+ℤ-assoc : ∀ x y z → (x +ℤ y) +ℤ z ≡ x +ℤ (y +ℤ z)
+ℤ-assoc x y z =
  trans (+ℤ-⊖ˡ (up x + up y) (dn x + dn y) z)
  (trans (cong₂ _⊖_ (+-assoc (up x) (up y) (up z)) (+-assoc (dn x) (dn y) (dn z)))
         (sym (+ℤ-⊖ʳ x (up y + up z) (dn y + dn z))))

+ℤ-identityˡ : ∀ x → pos 0 +ℤ x ≡ x
+ℤ-identityˡ x = nf x

maxℤ-comm : ∀ x y → maxℤ x y ≡ maxℤ y x
maxℤ-comm x y =
  cong₂ _⊖_ (max-comm (up x + dn y) (up y + dn x)) (+-comm (dn x) (dn y))

maxℤ-⊖ˡ : ∀ a b y → maxℤ (a ⊖ b) y ≡ max (a + dn y) (up y + b) ⊖ (b + dn y)
maxℤ-⊖ˡ a b y = ⊖-≡ (max (u + dn y) (up y + d)) (d + dn y) (max (a + dn y) (up y + b)) (b + dn y)
  (trans (+-distribʳ-max (u + dn y) (up y + d) (b + dn y))
  (trans (cong₂ max e₁ (+-inter (up y) d b (dn y)))
         (sym (+-distribʳ-max (a + dn y) (up y + b) (d + dn y)))))
  where
  u = up (a ⊖ b)
  d = dn (a ⊖ b)
  e₁ : (u + dn y) + (b + dn y) ≡ (a + dn y) + (d + dn y)
  e₁ = trans (+-inter u (dn y) b (dn y))
       (trans (cong (_+ (dn y + dn y)) (cross a b))
       (trans (cong (_+ (dn y + dn y)) (+-comm d a))
              (+-inter a d (dn y) (dn y))))

maxℤ-⊖ʳ : ∀ x a b → maxℤ x (a ⊖ b) ≡ max (up x + b) (a + dn x) ⊖ (dn x + b)
maxℤ-⊖ʳ x a b =
  trans (maxℤ-comm x (a ⊖ b))
  (trans (maxℤ-⊖ˡ a b x)
         (cong₂ _⊖_ (max-comm (a + dn x) (up x + b)) (+-comm b (dn x))))

maxℤ-⊖ : ∀ a b c d → maxℤ (a ⊖ b) (c ⊖ d) ≡ max (a + d) (c + b) ⊖ (b + d)
maxℤ-⊖ a b c d =
  trans (maxℤ-⊖ˡ a b (c ⊖ d)) (⊖-≡ (max (a + d') (c' + b)) (b + d') (max (a + d) (c + b)) (b + d)
    (trans (+-distribʳ-max (a + d') (c' + b) (b + d))
    (trans (cong₂ max f₁ f₂)
           (sym (+-distribʳ-max (a + d) (c + b) (b + d'))))))
  where
  c' = up (c ⊖ d)
  d' = dn (c ⊖ d)
  f₁ : (a + d') + (b + d) ≡ (a + d) + (b + d')
  f₁ = trans (+-inter a d' b d)
       (trans (cong ((a + b) +_) (+-comm d' d))
              (sym (+-inter a d b d')))
  f₂ : (c' + b) + (b + d) ≡ (c + b) + (b + d')
  f₂ = trans (cong ((c' + b) +_) (+-comm b d))
       (trans (+-inter c' b d b)
       (trans (cong (_+ (b + b)) (cross c d))
       (trans (cong (_+ (b + b)) (+-comm d' c))
       (trans (+-inter c d' b b)
              (cong ((c + b) +_) (+-comm d' b))))))

maxℤ-assoc : ∀ x y z → maxℤ (maxℤ x y) z ≡ maxℤ x (maxℤ y z)
maxℤ-assoc x y z =
  trans (maxℤ-⊖ˡ (max (ux + dy) (uy + dx)) (dx + dy) z)
  (trans (cong₂ _⊖_ peaks (+-assoc dx dy dz))
         (sym (maxℤ-⊖ʳ x (max (uy + dz) (uz + dy)) (dy + dz))))
  where
  ux = up x
  uy = up y
  uz = up z
  dx = dn x
  dy = dn y
  dz = dn z
  peaks : max (max (ux + dy) (uy + dx) + dz) (uz + (dx + dy))
        ≡ max (ux + (dy + dz)) (max (uy + dz) (uz + dy) + dx)
  peaks =
    trans (cong (λ m → max m (uz + (dx + dy))) (+-distribʳ-max (ux + dy) (uy + dx) dz))
    (trans (max-assoc ((ux + dy) + dz) ((uy + dx) + dz) (uz + (dx + dy)))
    (trans (cong₂ max (+-assoc ux dy dz)
             (cong₂ max (+-swapʳ uy dx dz)
               (trans (cong (uz +_) (+-comm dx dy)) (sym (+-assoc uz dy dx)))))
           (cong (max (ux + (dy + dz))) (sym (+-distribʳ-max (uy + dz) (uz + dy) dx)))))

maxℤ-idem : ∀ x → maxℤ x x ≡ x
maxℤ-idem x =
  trans (cong (_⊖ (dn x + dn x)) (max-idem (up x + dn x)))
  (trans (⊖-≡ (up x + dn x) (dn x + dn x) (up x) (dn x) (+-assoc (up x) (dn x) (dn x))) (nf x))

+ℤ-distribˡ-maxℤ : ∀ x y z → x +ℤ maxℤ y z ≡ maxℤ (x +ℤ y) (x +ℤ z)
+ℤ-distribˡ-maxℤ x y z =
  trans (+ℤ-⊖ʳ x (max (uy + dz) (uz + dy)) (dy + dz))
  (trans (sym (⊖-cancel dx (ux + max (uy + dz) (uz + dy)) (dx + (dy + dz))))
  (trans (cong₂ _⊖_ peaks (sym (+-rot dx dy dx dz)))
         (sym (maxℤ-⊖ (ux + uy) (dx + dy) (ux + uz) (dx + dz)))))
  where
  ux = up x
  uy = up y
  uz = up z
  dx = dn x
  dy = dn y
  dz = dn z
  peaks : dx + (ux + max (uy + dz) (uz + dy))
        ≡ max ((ux + uy) + (dx + dz)) ((ux + uz) + (dx + dy))
  peaks =
    trans (cong (dx +_) (+-distribˡ-max ux (uy + dz) (uz + dy)))
    (trans (+-distribˡ-max dx (ux + (uy + dz)) (ux + (uz + dy)))
           (sym (cong₂ max (+-rot ux uy dx dz) (+-rot ux uz dx dy))))

----------------------------------------------------------------------
-- Drift: the integers with −∞
data Drift : Set where
  −∞  : Drift
  fin : Int → Drift

infixl 6 _+d_
_+d_ : Drift → Drift → Drift
−∞    +d _     = −∞
fin x +d −∞    = −∞
fin x +d fin y = fin (x +ℤ y)

maxd : Drift → Drift → Drift
maxd −∞      e       = e
maxd (fin x) −∞      = fin x
maxd (fin x) (fin y) = fin (maxℤ x y)

0d : Drift
0d = fin (pos 0)

-- A natural as a drift.
pk : Nat → Drift
pk n = fin (pos n)

-- The natural part of a drift; 0 below zero.
clamp : Drift → Nat
clamp −∞             = zero
clamp (fin (pos n))    = n
clamp (fin (negsuc _)) = zero

unfin : Drift → Int
unfin −∞      = pos 0
unfin (fin x) = x

fin-injective : ∀ {x y} → fin x ≡ fin y → x ≡ y
fin-injective = cong unfin

pk-injective : ∀ {m n} → pk m ≡ pk n → m ≡ n
pk-injective = cong clamp

----------------------------------------------------------------------
-- The max-plus dioid on ℤ
private
  maxd-assoc : ∀ a b c → maxd (maxd a b) c ≡ maxd a (maxd b c)
  maxd-assoc −∞      b       c       = refl
  maxd-assoc (fin x) −∞      c       = refl
  maxd-assoc (fin x) (fin y) −∞      = refl
  maxd-assoc (fin x) (fin y) (fin z) = cong fin (maxℤ-assoc x y z)

  maxd-comm : ∀ a b → maxd a b ≡ maxd b a
  maxd-comm −∞      −∞      = refl
  maxd-comm −∞      (fin y) = refl
  maxd-comm (fin x) −∞      = refl
  maxd-comm (fin x) (fin y) = cong fin (maxℤ-comm x y)

  maxd-idem : ∀ a → maxd a a ≡ a
  maxd-idem −∞      = refl
  maxd-idem (fin x) = cong fin (maxℤ-idem x)

  +d-assoc : ∀ a b c → (a +d b) +d c ≡ a +d (b +d c)
  +d-assoc −∞      b       c       = refl
  +d-assoc (fin x) −∞      c       = refl
  +d-assoc (fin x) (fin y) −∞      = refl
  +d-assoc (fin x) (fin y) (fin z) = cong fin (+ℤ-assoc x y z)

  +d-identityˡ : ∀ a → 0d +d a ≡ a
  +d-identityˡ −∞      = refl
  +d-identityˡ (fin x) = cong fin (+ℤ-identityˡ x)

+d-comm : ∀ a b → a +d b ≡ b +d a
+d-comm −∞      −∞      = refl
+d-comm −∞      (fin y) = refl
+d-comm (fin x) −∞      = refl
+d-comm (fin x) (fin y) = cong fin (+ℤ-comm x y)

private
  +d-identityʳ : ∀ a → a +d 0d ≡ a
  +d-identityʳ a = trans (+d-comm a 0d) (+d-identityˡ a)

  distribˡ : ∀ a b c → a +d maxd b c ≡ maxd (a +d b) (a +d c)
  distribˡ −∞      b       c       = refl
  distribˡ (fin x) −∞      c       = refl
  distribˡ (fin x) (fin y) −∞      = refl
  distribˡ (fin x) (fin y) (fin z) = cong fin (+ℤ-distribˡ-maxℤ x y z)

  distribʳ : ∀ a b c → maxd a b +d c ≡ maxd (a +d c) (b +d c)
  distribʳ a b c =
    trans (+d-comm (maxd a b) c)
    (trans (distribˡ c a b) (cong₂ maxd (+d-comm c a) (+d-comm c b)))

Drift-RA : ResourceAlgebra
Drift-RA = record
  { Grade = Drift
  ; _⊕_ = maxd
  ; _⊗_ = _+d_
  ; 𝟘 = −∞
  ; 𝟙 = 0d
  ; alt = record { assoc = maxd-assoc ; comm = maxd-comm ; idem = maxd-idem ; unitˡ = λ _ → refl }
  ; seq = record { assoc = +d-assoc ; unitˡ = +d-identityˡ ; unitʳ = +d-identityʳ }
  }

Drift-dioid : IsDioid Drift-RA
Drift-dioid = record { distribˡ = distribˡ ; distribʳ = distribʳ }

----------------------------------------------------------------------
-- Naturals inside Drift
pk-max : ∀ a b → pk (max a b) ≡ maxd (pk a) (pk b)
pk-max a b = cong pk (sym (cong₂ max (+-identityʳ a) (+-identityʳ b)))

pk-+ : ∀ a b → pk (a + b) ≡ pk a +d pk b
pk-+ a b = refl

-- max (pk p) y is never below zero, so clamp keeps it.
pk-clamp : ∀ p y → pk (clamp (maxd (pk p) y)) ≡ maxd (pk p) y
pk-clamp p −∞      = refl
pk-clamp p (fin x) =
  trans (cong (λ z → pk (clamp (fin z))) e) (cong fin (sym e))
  where
  e : max (p + dn x) (up x + 0) ⊖ dn x ≡ pos (max (p + dn x) (up x + 0) - dn x)
  e = ⊖-pos _ (dn x) (≤-trans (≤-+ˡ p (dn x)) (≤-max-left (p + dn x) (up x + 0)))

----------------------------------------------------------------------
-- The bound of a signed grade
infix 4 _≤ᵈ_
_≤ᵈ_ : Drift → Nat → Set
−∞             ≤ᵈ _ = ⊤
fin (pos n)    ≤ᵈ p = n ≤ᵣ p
fin (negsuc _) ≤ᵈ _ = ⊤

private
  ≤ᵣ-irrelevant : ∀ m n (p q : m ≤ᵣ n) → p ≡ q
  ≤ᵣ-irrelevant zero    _       _  _ = refl
  ≤ᵣ-irrelevant (suc _) zero    () _
  ≤ᵣ-irrelevant (suc m) (suc n) p  q = ≤ᵣ-irrelevant m n p q

≤ᵈ-irrelevant : ∀ d p (x y : d ≤ᵈ p) → x ≡ y
≤ᵈ-irrelevant −∞             p x y = refl
≤ᵈ-irrelevant (fin (pos n))    p x y = ≤ᵣ-irrelevant n p x y
≤ᵈ-irrelevant (fin (negsuc _)) p x y = refl

open ResourceAlgebra Drift-RA public using () renaming (_≼_ to _≼d_)

≤ᵈ→≼ : ∀ d p → d ≤ᵈ p → d ≼d pk p
≤ᵈ→≼ −∞               p b = refl
≤ᵈ→≼ (fin (pos n))    p b =
  cong pk (trans (cong₂ max (+-identityʳ n) (+-identityʳ p)) (max-≤ (le b)))
≤ᵈ→≼ (fin (negsuc n)) p b =
  cong fin (⊖-≡ (p + suc n) (suc n + 0) p 0 (trans (+-identityʳ (p + suc n))
                       (cong (p +_) (sym (+-identityʳ (suc n))))))

≼→≤ᵈ : ∀ d p → d ≼d pk p → d ≤ᵈ p
≼→≤ᵈ −∞               p e = tt
≼→≤ᵈ (fin (pos n))    p e =
  _≤_.unle (max-≡→≤ (trans (sym (cong₂ max (+-identityʳ n) (+-identityʳ p)))
                           (pk-injective e)))
≼→≤ᵈ (fin (negsuc n)) p e = tt

pk-mono : ∀ {a b} → a ≤ b → pk a ≼d pk b
pk-mono {a} {b} p = ≤ᵈ→≼ (pk a) b (_≤_.unle p)

pk-≼→≤ : ∀ {a b} → pk a ≼d pk b → a ≤ b
pk-≼→≤ {a} {b} e = le (≼→≤ᵈ (pk a) b e)
