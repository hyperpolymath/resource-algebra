{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module MorphismTest where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Morphism
open import ResourceAlgebra.Instances.Loss as L using (Loss; fin; inf)
open import ResourceAlgebra.Instances.MaxPlus using (MaxPlus; val; bot)
open import ResourceAlgebra.Instances.HWM as H using (HWM; hwm; 𝟘h; _⊗h_; _⊕h_)
open import ResourceAlgebra.Instances.MinMax using (MinMax)

module MP = ResourceAlgebra MaxPlus
module MM = ResourceAlgebra MinMax

-- The two Loss maps agree at zero and infinity, but disagree at EVERY
-- positive finite grade. Test the functions via their exported records.
zero-test-at-zero : Hom.map zero-test-hom (fin 0) ≡ val 0
zero-test-at-zero = refl

zero-test-at-positive : ∀ n → Hom.map zero-test-hom (fin (suc n)) ≡ bot
zero-test-at-positive n = refl

zero-test-at-infinity : Hom.map zero-test-hom inf ≡ bot
zero-test-at-infinity = refl

support-at-finite : ∀ n → Hom.map support-hom (fin n) ≡ val 0
support-at-finite n = refl

support-at-infinity : Hom.map support-hom inf ≡ bot
support-at-infinity = refl

maps-disagree-at-positive : ∀ n → zero-test (fin (suc n)) ≢ support (fin (suc n))
maps-disagree-at-positive n ()

reverse-support-at-finite : ∀ n → Hom.map support′-hom (val n) ≡ fin 0
reverse-support-at-finite n = refl

reverse-support-at-bottom : Hom.map support′-hom bot ≡ inf
reverse-support-at-bottom = refl

-- The new classifiers compute the correct branch, including on maps
-- built by composition rather than just their canonical inhabitants.
branch : {A B : Set} → A ⊎ B → Nat
branch (inj₁ _) = 0
branch (inj₂ _) = 1

classify-zero-test : branch (Loss→MaxPlus zero-test-hom) ≡ 0
classify-zero-test = refl

classify-support : branch (Loss→MaxPlus support-hom) ≡ 1
classify-support = refl

classify-composed-support :
  branch (Loss→MaxPlus (zero-test-hom ∘h support′-hom ∘h support-hom)) ≡ 1
classify-composed-support = refl

unique-reverse-map-finite : ∀ n → Hom.map support′-hom (val n) ≡ fin 0
unique-reverse-map-finite n = MaxPlus→Loss support′-hom (val n)

unique-reverse-map-bottom : Hom.map support′-hom bot ≡ inf
unique-reverse-map-bottom = MaxPlus→Loss support′-hom bot

zero-test-collapses-witnesses :
  Hom.map zero-test-hom (fin 1) ≡ Hom.map zero-test-hom (fin 2)
zero-test-collapses-witnesses = Loss→MaxPlus-collapses zero-test-hom

support-collapses-witnesses :
  Hom.map support-hom (fin 1) ≡ Hom.map support-hom (fin 2)
support-collapses-witnesses = Loss→MaxPlus-collapses support-hom

-- A client cannot recover distinct positive grades through either map.
cannot-recover-positive-loss : (h : Hom Loss MaxPlus)
  → (∀ a b → Hom.map h a ≡ Hom.map h b → a ≡ b) → ⊥
cannot-recover-positive-loss = no-injective-Loss→MaxPlus

strict-round-trip-zero : Hom.map (support′-hom ∘h zero-test-hom) (fin 0) ≡ fin 0
strict-round-trip-zero = refl

strict-round-trip-positive :
  Hom.map (support′-hom ∘h zero-test-hom) (fin 3) ≡ inf
strict-round-trip-positive = refl

support-round-trip-positive :
  Hom.map (support′-hom ∘h support-hom) (fin 3) ≡ fin 0
support-round-trip-positive = refl

strict-round-trip-infinity : Hom.map (support′-hom ∘h zero-test-hom) inf ≡ inf
strict-round-trip-infinity = refl

reverse-round-trip-positive :
  Hom.map (zero-test-hom ∘h support′-hom) (val 3) ≡ val 0
reverse-round-trip-positive = refl

reverse-round-trip-bottom : Hom.map (zero-test-hom ∘h support′-hom) bot ≡ bot
reverse-round-trip-bottom = refl

-- Pointwise category laws avoid function extensionality and test every
-- grade, including the sentinel grades, of every compatible algebra.
strict-identity : (A : ResourceAlgebra) (a : ResourceAlgebra.Grade A)
  → Hom.map (id-hom A) a ≡ a
strict-identity A a = refl

strict-left-identity : {A B : ResourceAlgebra} (h : Hom A B)
  (a : ResourceAlgebra.Grade A) → Hom.map (id-hom B ∘h h) a ≡ Hom.map h a
strict-left-identity h a = refl

strict-right-identity : {A B : ResourceAlgebra} (h : Hom A B)
  (a : ResourceAlgebra.Grade A) → Hom.map (h ∘h id-hom A) a ≡ Hom.map h a
strict-right-identity h a = refl

strict-associativity : {A B C D : ResourceAlgebra}
  (f : Hom A B) (g : Hom B C) (h : Hom C D) (a : ResourceAlgebra.Grade A)
  → Hom.map ((h ∘h g) ∘h f) a ≡ Hom.map (h ∘h (g ∘h f)) a
strict-associativity f g h a = refl

lax-identity : (A : ResourceAlgebra) (a : ResourceAlgebra.Grade A)
  → LaxHom.map (id-lax A) a ≡ a
lax-identity A a = refl

lax-left-identity : {A B : ResourceAlgebra} (h : LaxHom A B)
  (a : ResourceAlgebra.Grade A) → LaxHom.map (id-lax B ∘l h) a ≡ LaxHom.map h a
lax-left-identity h a = refl

lax-right-identity : {A B : ResourceAlgebra} (h : LaxHom A B)
  (a : ResourceAlgebra.Grade A) → LaxHom.map (h ∘l id-lax A) a ≡ LaxHom.map h a
lax-right-identity h a = refl

lax-associativity : {A B C D : ResourceAlgebra}
  (f : LaxHom A B) (g : LaxHom B C) (h : LaxHom C D) (a : ResourceAlgebra.Grade A)
  → LaxHom.map ((h ∘l g) ∘l f) a ≡ LaxHom.map (h ∘l (g ∘l f)) a
lax-associativity f g h a = refl

strict-to-lax-keeps-map : (A B : ResourceAlgebra) (h : Hom A B)
  (a : ResourceAlgebra.Grade A) → LaxHom.map (lax A B h) a ≡ Hom.map h a
strict-to-lax-keeps-map A B h a = refl

-- Multiplication and monotonicity of a converted non-identity map.
converted-zero-test-sequence :
  LaxHom.map (lax Loss MaxPlus zero-test-hom) (fin 3) MP.≼ bot
converted-zero-test-sequence =
  LaxHom.map-⊗ (lax Loss MaxPlus zero-test-hom) (fin 1) (fin 2)

converted-support-monotone : val 0 MP.≼ val 0
converted-support-monotone = LaxHom.mono (lax Loss MaxPlus support-hom)
  {a = fin 7} {b = fin 2} refl

-- Peaks need not preserve zero. Released state yields a strict bound;
-- retaining the full peak makes the bound an equality.
released-two released-three retained-two partial-four : H.Grade
released-two = hwm 2 0 z≤n
released-three = hwm 3 0 z≤n
retained-two = hwm 2 2 (≤-refl 2)
partial-four = hwm 4 1 (s≤s z≤n)

peak-of-zero : LaxHom.map peak-lax 𝟘h ≡ val 0
peak-of-zero = refl

peak-zero-is-not-bottom : LaxHom.map peak-lax 𝟘h ≢ bot
peak-zero-is-not-bottom ()

peak-zero-bound : bot MP.≼ LaxHom.map peak-lax 𝟘h
peak-zero-bound = LaxHom.map-𝟘 peak-lax

peak-ignores-drift : LaxHom.map peak-lax retained-two ≡ val 2
peak-ignores-drift = refl

peak-of-alternatives : LaxHom.map peak-lax (released-two ⊕h released-three) ≡ val 3
peak-of-alternatives = refl

released-sequence-peak :
  LaxHom.map peak-lax (released-two ⊗h released-three) ≡ val 3
released-sequence-peak = refl

released-sequence-bound : val 3 MP.≼ val 5
released-sequence-bound = LaxHom.map-⊗ peak-lax released-two released-three

retained-sequence-peak :
  LaxHom.map peak-lax (retained-two ⊗h released-three) ≡ val 5
retained-sequence-peak = refl

retained-sequence-tight-bound : val 5 MP.≼ val 5
retained-sequence-tight-bound = LaxHom.map-⊗ peak-lax retained-two released-three

first-peak-dominates : LaxHom.map peak-lax (partial-four ⊗h released-two) ≡ val 4
first-peak-dominates = refl

peak-is-monotone : val 2 MP.≼ val 3
peak-is-monotone = LaxHom.mono peak-lax
  {a = released-two} {b = released-three} (H.hwm-≡ refl refl)

-- HWM's equal units rule out strict maps even to the new MinMax instance.
no-strict-HWM-to-MinMax : Hom HWM MinMax → ⊥
no-strict-HWM-to-MinMax = no-strict-from-HWM MinMax (λ ())

-- The bottleneck map preserves all grades but weakens an additive bound
-- in the REVERSED order induced by min. Infinity must remain unreachable.
bottleneck-keeps-finite : ∀ n → LaxHom.map loss-bottleneck (fin n) ≡ fin n
bottleneck-keeps-finite n = refl

bottleneck-keeps-infinity : LaxHom.map loss-bottleneck inf ≡ inf
bottleneck-keeps-infinity = refl

bottleneck-positive-bound : fin 5 MM.≼ fin 3
bottleneck-positive-bound = LaxHom.map-⊗ loss-bottleneck (fin 2) (fin 3)

bottleneck-zero-bound : fin 3 MM.≼ fin 3
bottleneck-zero-bound = LaxHom.map-⊗ loss-bottleneck (fin 0) (fin 3)

bottleneck-infinite-left-bound : inf MM.≼ inf
bottleneck-infinite-left-bound = LaxHom.map-⊗ loss-bottleneck inf (fin 3)

bottleneck-infinite-right-bound : inf MM.≼ inf
bottleneck-infinite-right-bound = LaxHom.map-⊗ loss-bottleneck (fin 3) inf

bottleneck-both-infinite-bound : inf MM.≼ inf
bottleneck-both-infinite-bound = LaxHom.map-⊗ loss-bottleneck inf inf

bottleneck-monotone : fin 7 MM.≼ fin 2
bottleneck-monotone = LaxHom.mono loss-bottleneck {a = fin 7} {b = fin 2} refl

bottleneck-zero-bound-is-least : inf MM.≼ inf
bottleneck-zero-bound-is-least = LaxHom.map-𝟘 loss-bottleneck

-- Composition must retain a strict inequality when it passes through an
-- identity, including the reversed inequality in the MinMax target.
composed-peak-keeps-loose-bound : val 3 MP.≼ val 5
composed-peak-keeps-loose-bound =
  LaxHom.map-⊗ (id-lax MaxPlus ∘l peak-lax) released-two released-three

composed-bottleneck-keeps-loose-bound : fin 5 MM.≼ fin 3
composed-bottleneck-keeps-loose-bound =
  LaxHom.map-⊗ (id-lax MinMax ∘l loss-bottleneck) (fin 2) (fin 3)

-- A genuinely lax composition crosses three instances. This also tests
-- that strict-to-lax conversion interoperates with both lax maps.
peak-bottleneck : LaxHom HWM MinMax
peak-bottleneck = loss-bottleneck ∘l lax MaxPlus Loss support′-hom ∘l peak-lax

composed-lax-map : LaxHom.map peak-bottleneck retained-two ≡ fin 0
composed-lax-map = refl

composed-lax-unit : LaxHom.map peak-bottleneck 𝟘h ≡ fin 0
composed-lax-unit = LaxHom.map-𝟙 peak-bottleneck

composed-lax-sequence : fin 0 MM.≼ fin 0
composed-lax-sequence = LaxHom.map-⊗ peak-bottleneck released-two released-three

composed-lax-monotone : fin 0 MM.≼ fin 0
composed-lax-monotone = LaxHom.mono peak-bottleneck
  {a = released-two} {b = released-three} (H.hwm-≡ refl refl)
