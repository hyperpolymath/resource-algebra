{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Builtins only (no standard library), so the development checks under
-- the Debian/Ubuntu agda package the estate pins and needs no library
-- resolution. Every ℕ lemma below is proved here, not imported.
module ResourceAlgebra.Prelude where

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Unit public using (⊤; tt)
open import Agda.Builtin.Sigma public using (Σ; _,_; fst; snd)

----------------------------------------------------------------------
-- Logic
data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

cong : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {a b : A} {c d : B}
      → a ≡ b → c ≡ d → f a c ≡ f b d
cong₂ f refl refl = refl

subst : {A : Set} (P : A → Set) {a b : A} → a ≡ b → P a → P b
subst P refl p = p

----------------------------------------------------------------------
-- Addition
+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-identityʳ n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

----------------------------------------------------------------------
-- max (the join of the usual order on ℕ)
max : Nat → Nat → Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

max-zeroʳ : ∀ m → max m zero ≡ m
max-zeroʳ zero    = refl
max-zeroʳ (suc m) = refl

max-comm : ∀ m n → max m n ≡ max n m
max-comm zero    n       = sym (max-zeroʳ n)
max-comm (suc m) zero    = refl
max-comm (suc m) (suc n) = cong suc (max-comm m n)

max-assoc : ∀ m n p → max (max m n) p ≡ max m (max n p)
max-assoc zero    n       p       = refl
max-assoc (suc m) zero    p       = refl
max-assoc (suc m) (suc n) zero    = refl
max-assoc (suc m) (suc n) (suc p) = cong suc (max-assoc m n p)

max-idem : ∀ m → max m m ≡ m
max-idem zero    = refl
max-idem (suc m) = cong suc (max-idem m)

-- max p (max x y) = max (max p x) (max p y): a join absorbs its duplicate.
max-dup : ∀ p x y → max (max p x) (max p y) ≡ max p (max x y)
max-dup p x y =
  trans (max-assoc p x (max p y))
  (trans (cong (max p) (sym (max-assoc x p y)))
  (trans (cong (λ z → max p (max z y)) (max-comm x p))
  (trans (cong (max p) (max-assoc p x y))
  (trans (sym (max-assoc p p (max x y)))
         (cong (λ z → max z (max x y)) (max-idem p))))))

-- max (max a b) (max c d) = max (max a c) (max b d)
max-interchange : ∀ a b c d → max (max a b) (max c d) ≡ max (max a c) (max b d)
max-interchange a b c d =
  trans (max-assoc a b (max c d))
  (trans (cong (max a)
    (trans (sym (max-assoc b c d))
    (trans (cong (λ z → max z d) (max-comm b c))
           (max-assoc c b d))))
  (sym (max-assoc a c (max b d))))

+-distribˡ-max : ∀ a b c → a + max b c ≡ max (a + b) (a + c)
+-distribˡ-max zero    b c = refl
+-distribˡ-max (suc a) b c = cong suc (+-distribˡ-max a b c)

+-distribʳ-max : ∀ a b c → max a b + c ≡ max (a + c) (b + c)
+-distribʳ-max a b c =
  trans (+-comm (max a b) c)
  (trans (+-distribˡ-max c a b)
         (cong₂ max (+-comm c a) (+-comm c b)))

----------------------------------------------------------------------
-- min (the meet of the usual order on ℕ)
min : Nat → Nat → Nat
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)

min-zeroʳ : ∀ m → min m zero ≡ zero
min-zeroʳ zero    = refl
min-zeroʳ (suc m) = refl

min-comm : ∀ m n → min m n ≡ min n m
min-comm zero    n       = sym (min-zeroʳ n)
min-comm (suc m) zero    = refl
min-comm (suc m) (suc n) = cong suc (min-comm m n)

min-assoc : ∀ m n p → min (min m n) p ≡ min m (min n p)
min-assoc zero    n       p       = refl
min-assoc (suc m) zero    p       = refl
min-assoc (suc m) (suc n) zero    = refl
min-assoc (suc m) (suc n) (suc p) = cong suc (min-assoc m n p)

min-idem : ∀ m → min m m ≡ m
min-idem zero    = refl
min-idem (suc m) = cong suc (min-idem m)

+-distribˡ-min : ∀ a b c → a + min b c ≡ min (a + b) (a + c)
+-distribˡ-min zero    b c = refl
+-distribˡ-min (suc a) b c = cong suc (+-distribˡ-min a b c)

+-distribʳ-min : ∀ a b c → min a b + c ≡ min (a + c) (b + c)
+-distribʳ-min a b c =
  trans (+-comm (min a b) c)
  (trans (+-distribˡ-min c a b)
         (cong₂ min (+-comm c a) (+-comm c b)))

----------------------------------------------------------------------
-- The usual order on ℕ (needed only by the high-water-mark instance)
infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

+-monoʳ-≤ : ∀ m {n p} → n ≤ p → m + n ≤ m + p
+-monoʳ-≤ zero    q = q
+-monoʳ-≤ (suc m) q = s≤s (+-monoʳ-≤ m q)

≤-max-right : ∀ m n → n ≤ max m n
≤-max-right zero    n       = ≤-refl n
≤-max-right (suc m) zero    = z≤n
≤-max-right (suc m) (suc n) = s≤s (≤-max-right m n)

≤-max-left : ∀ m n → m ≤ max m n
≤-max-left zero    n       = z≤n
≤-max-left (suc m) zero    = ≤-refl (suc m)
≤-max-left (suc m) (suc n) = s≤s (≤-max-left m n)

max-mono-≤ : ∀ {a a' b b'} → a ≤ a' → b ≤ b' → max a b ≤ max a' b'
max-mono-≤ {a' = a'}          z≤n     q       = ≤-trans q (≤-max-right a' _)
max-mono-≤ {a' = a'} {b' = b'} (s≤s p) z≤n     = ≤-trans (s≤s p) (≤-max-left a' b')
max-mono-≤                     (s≤s p) (s≤s q) = s≤s (max-mono-≤ p q)

----------------------------------------------------------------------
-- Disjoint sum (for the morphism classifications)
infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

----------------------------------------------------------------------
-- More of the usual order, for the min-max instance and the morphisms
suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

+-cancelˡ : ∀ k {m n} → k + m ≡ k + n → m ≡ n
+-cancelˡ zero    p = p
+-cancelˡ (suc k) p = +-cancelˡ k (suc-injective p)

≤-+ʳ : ∀ m n → m ≤ m + n
≤-+ʳ zero    n = z≤n
≤-+ʳ (suc m) n = s≤s (≤-+ʳ m n)

≤-+ˡ : ∀ m n → n ≤ m + n
≤-+ˡ m n = subst (λ x → n ≤ x) (+-comm n m) (≤-+ʳ n m)

+-monoˡ-≤ : ∀ {m n} p → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ {m} {n} p q =
  subst (λ x → x ≤ n + p) (+-comm p m)
        (subst (λ y → p + m ≤ y) (+-comm p n) (+-monoʳ-≤ p q))

max-lub : ∀ {a b c} → a ≤ c → b ≤ c → max a b ≤ c
max-lub {zero}           _       q       = q
max-lub {suc a} {zero}   p       _       = p
max-lub {suc a} {suc b}  (s≤s p) (s≤s q) = s≤s (max-lub p q)

-- max m n is n once m ≤ n; min m n is m once m ≤ n.
max-≤ : ∀ {m n} → m ≤ n → max m n ≡ n
max-≤ z≤n     = refl
max-≤ (s≤s p) = cong suc (max-≤ p)

min-≤ : ∀ {m n} → m ≤ n → min m n ≡ m
min-≤ z≤n     = refl
min-≤ (s≤s p) = cong suc (min-≤ p)

min-≥ : ∀ {m n} → n ≤ m → min m n ≡ n
min-≥ {m} {n} p = trans (min-comm m n) (min-≤ p)

-- A bottleneck never exceeds the sum: max m n ≤ m + n.
max-≤-+ : ∀ m n → max m n ≤ m + n
max-≤-+ m n = max-lub (≤-+ʳ m n) (≤-+ˡ m n)

-- max distributes over min: the min-max instance is a dioid.
max-distribˡ-min : ∀ a b c → max a (min b c) ≡ min (max a b) (max a c)
max-distribˡ-min zero    b       c       = refl
max-distribˡ-min (suc a) zero    c       =
  sym (min-≤ (≤-max-left (suc a) c))
max-distribˡ-min (suc a) (suc b) zero    =
  cong suc (sym (min-≥ (≤-max-left a b)))
max-distribˡ-min (suc a) (suc b) (suc c) = cong suc (max-distribˡ-min a b c)

max-distribʳ-min : ∀ a b c → max (min a b) c ≡ min (max a c) (max b c)
max-distribʳ-min a b c =
  trans (max-comm (min a b) c)
  (trans (max-distribˡ-min c a b)
         (cong₂ min (max-comm c a) (max-comm c b)))
