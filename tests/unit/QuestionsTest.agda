{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module QuestionsTest where

open import Agda.Builtin.Bool using (true; false)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Morphism
open import ResourceAlgebra.Instances.Loss using (Loss; fin; inf)
open import ResourceAlgebra.Instances.Questions

module Q3 = ResourceAlgebra (Questions 3)

-- Three questions.  true = this question is lost.
a b : Q 3
a = true  , false , false , tt
b = false , false , true  , tt

-- Use the public record: its units and operations are the consumer contract.
zero-is-all-lost : Q3.𝟘 ≡ (true , true , true , tt)
zero-is-all-lost = refl

one-is-none-lost : Q3.𝟙 ≡ (false , false , false , tt)
one-is-none-lost = refl

sequence-is-union : a Q3.⊗ b ≡ (true , false , true , tt)
sequence-is-union = refl

alternatives-is-intersection : a Q3.⊕ b ≡ Q3.𝟙
alternatives-is-intersection = refl

alternatives-keeps-a-shared-loss : a Q3.⊕ (a Q3.⊗ b) ≡ a
alternatives-keeps-a-shared-loss = refl

sequence-repeats-nothing : a Q3.⊗ a ≡ a
sequence-repeats-nothing = refl

no-questions-is-trivial : (x y : Q 0) → x ≡ y
no-questions-is-trivial _ _ = refl

-- The exported layers, at these grades.
distribute-left : a Q3.⊗ (b Q3.⊕ Q3.𝟘) ≡ (a Q3.⊗ b) Q3.⊕ (a Q3.⊗ Q3.𝟘)
distribute-left = IsDioid.distribˡ (Questions-dioid 3) a b Q3.𝟘

annihilate-left : Q3.𝟘 Q3.⊗ a ≡ Q3.𝟘
annihilate-left = IsAnnihilating.annihilˡ (Questions-annihilating 3) a

annihilate-right : a Q3.⊗ Q3.𝟘 ≡ Q3.𝟘
annihilate-right = IsAnnihilating.annihilʳ (Questions-annihilating 3) a

-- The induced order: fewer lost questions is above.  𝟘 (all lost) is least.
losing-more-is-below : (a Q3.⊗ b) Q3.≼ a
losing-more-is-below = refl

losing-less-is-not-below : ¬ (a Q3.≼ (a Q3.⊗ b))
losing-less-is-not-below p with cong (λ x → fst (snd (snd x))) p
... | ()

-- Each question lost alone is incomparable with the other.
incomparable : ¬ (collapse ≡ shuffle)
incomparable = same-amount-different-loss

-- The morphisms, through their exported records.
lost-maps-to-unreachable : Hom.map (one-question-hom Loss refl) (true , tt) ≡ inf
lost-maps-to-unreachable = refl

kept-maps-to-no-cost : Hom.map (one-question-hom Loss refl) (false , tt) ≡ fin 0
kept-maps-to-no-cost = refl

first-question-of-a : Hom.map (first-question 2) a ≡ (true , tt)
first-question-of-a = refl

later-questions-of-a : Hom.map (later-questions 2) a ≡ (false , false , tt)
later-questions-of-a = refl

count-of-collapse : count 2 collapse ≡ 1
count-of-collapse = refl

count-of-shuffle : count 2 shuffle ≡ 1
count-of-shuffle = refl

count-of-their-alternatives : count 2 (ResourceAlgebra._⊕_ (Questions 2) collapse shuffle) ≡ 0
count-of-their-alternatives = refl
