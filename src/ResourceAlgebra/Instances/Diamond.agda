{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The diamond lattice M3: a bottom, a top and three pairwise incomparable
-- atoms.  Alternatives are the join, sequence is the meet, 𝟘 is the bottom
-- and 𝟙 the top.
--
-- It is the witness for C-4b: an annihilating ordered resource algebra
-- that is not a dioid.  The meet is monotone and the bottom absorbs under
-- it, but M3 is not a distributive lattice, so the meet does not
-- distribute over the join:  a ∧ (b ∨ c) = a ∧ ⊤ = a,  while
-- (a ∧ b) ∨ (a ∧ c) = ⊥ ∨ ⊥ = ⊥.
--
-- The laws are closed statements over a five-element carrier.  Each is
-- proved by one Boolean check that Agda evaluates (the check is `tt`),
-- read back through the soundness lemmas below.
module ResourceAlgebra.Instances.Diamond where

open import Agda.Builtin.Bool using (Bool; true; false)
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core

data Grade : Set where
  bot top a b c : Grade

infixl 6 _⊔d_
infixl 7 _⊓d_

-- Join: the alternatives.
_⊔d_ : Grade → Grade → Grade
bot ⊔d y   = y
top ⊔d _   = top
a   ⊔d bot = a
a   ⊔d top = top
a   ⊔d a   = a
a   ⊔d b   = top
a   ⊔d c   = top
b   ⊔d bot = b
b   ⊔d top = top
b   ⊔d a   = top
b   ⊔d b   = b
b   ⊔d c   = top
c   ⊔d bot = c
c   ⊔d top = top
c   ⊔d a   = top
c   ⊔d b   = top
c   ⊔d c   = c

-- Meet: the sequence.
_⊓d_ : Grade → Grade → Grade
bot ⊓d _   = bot
top ⊓d y   = y
a   ⊓d bot = bot
a   ⊓d top = a
a   ⊓d a   = a
a   ⊓d b   = bot
a   ⊓d c   = bot
b   ⊓d bot = bot
b   ⊓d top = b
b   ⊓d a   = bot
b   ⊓d b   = b
b   ⊓d c   = bot
c   ⊓d bot = bot
c   ⊓d top = c
c   ⊓d a   = bot
c   ⊓d b   = bot
c   ⊓d c   = c

----------------------------------------------------------------------
-- A decision procedure for closed statements over the carrier

private
  infix  4 _==_
  infixr 3 _&&_
  infixr 2 _⇒_

  T : Bool → Set
  T true  = ⊤
  T false = ⊥

  _&&_ : Bool → Bool → Bool
  true  && y = y
  false && _ = false

  _⇒_ : Bool → Bool → Bool
  true  ⇒ y = y
  false ⇒ _ = true

  &&-l : ∀ x y → T (x && y) → T x
  &&-l true  _ _ = tt
  &&-l false _ ()

  &&-r : ∀ x y → T (x && y) → T y
  &&-r true  _ p = p
  &&-r false _ ()

  ⇒-mp : ∀ x y → T (x ⇒ y) → T x → T y
  ⇒-mp true  _ p _ = p
  ⇒-mp false _ _ ()

  -- Every grade satisfies p.
  every : (Grade → Bool) → Bool
  every p = p bot && (p top && (p a && (p b && p c)))

  every-sound : ∀ p → T (every p) → ∀ x → T (p x)
  every-sound p h bot = &&-l (p bot) _ h
  every-sound p h top = &&-l (p top) _ (&&-r (p bot) _ h)
  every-sound p h a   = &&-l (p a) _ (&&-r (p top) _ (&&-r (p bot) _ h))
  every-sound p h b   =
    &&-l (p b) _ (&&-r (p a) _ (&&-r (p top) _ (&&-r (p bot) _ h)))
  every-sound p h c   =
    &&-r (p b) _ (&&-r (p a) _ (&&-r (p top) _ (&&-r (p bot) _ h)))

  _==_ : Grade → Grade → Bool
  bot == bot = true
  top == top = true
  a   == a   = true
  b   == b   = true
  c   == c   = true
  bot == top = false
  bot == a   = false
  bot == b   = false
  bot == c   = false
  top == bot = false
  top == a   = false
  top == b   = false
  top == c   = false
  a   == bot = false
  a   == top = false
  a   == b   = false
  a   == c   = false
  b   == bot = false
  b   == top = false
  b   == a   = false
  b   == c   = false
  c   == bot = false
  c   == top = false
  c   == a   = false
  c   == b   = false

  ==-sound : ∀ x y → T (x == y) → x ≡ y
  ==-sound bot bot _ = refl
  ==-sound top top _ = refl
  ==-sound a   a   _ = refl
  ==-sound b   b   _ = refl
  ==-sound c   c   _ = refl
  ==-sound bot top ()
  ==-sound bot a   ()
  ==-sound bot b   ()
  ==-sound bot c   ()
  ==-sound top bot ()
  ==-sound top a   ()
  ==-sound top b   ()
  ==-sound top c   ()
  ==-sound a   bot ()
  ==-sound a   top ()
  ==-sound a   b   ()
  ==-sound a   c   ()
  ==-sound b   bot ()
  ==-sound b   top ()
  ==-sound b   a   ()
  ==-sound b   c   ()
  ==-sound c   bot ()
  ==-sound c   top ()
  ==-sound c   a   ()
  ==-sound c   b   ()

  ==-refl : ∀ x → T (x == x)
  ==-refl bot = tt
  ==-refl top = tt
  ==-refl a   = tt
  ==-refl b   = tt
  ==-refl c   = tt

  -- An equation between two closed expressions in x, y, z, checked for
  -- all 125 triples.
  law₃ : (f g : Grade → Grade → Grade → Grade)
       → T (every λ x → every λ y → every λ z → f x y z == g x y z)
       → ∀ x y z → f x y z ≡ g x y z
  law₃ f g h x y z =
    ==-sound _ _
      (every-sound (λ z → f x y z == g x y z)
        (every-sound (λ y → every λ z → f x y z == g x y z)
          (every-sound (λ x → every λ y → every λ z → f x y z == g x y z)
            h x) y) z)

  law₂ : (f g : Grade → Grade → Grade)
       → T (every λ x → every λ y → f x y == g x y)
       → ∀ x y → f x y ≡ g x y
  law₂ f g h x y =
    ==-sound _ _
      (every-sound (λ y → f x y == g x y)
        (every-sound (λ x → every λ y → f x y == g x y) h x) y)

  law₁ : (f g : Grade → Grade)
       → T (every λ x → f x == g x) → ∀ x → f x ≡ g x
  law₁ f g h x = ==-sound _ _ (every-sound (λ x → f x == g x) h x)

  -- A conditional equation: x ⊔ y = y implies f x y z = g x y z.
  cond₃ : (f g : Grade → Grade → Grade → Grade)
        → T (every λ z → every λ x → every λ y →
               (x ⊔d y == y) ⇒ (f z x y == g z x y))
        → ∀ z {x y} → x ⊔d y ≡ y → f z x y ≡ g z x y
  cond₃ f g h z {x} {y} p =
    ==-sound _ _
      (⇒-mp (x ⊔d y == y) (f z x y == g z x y)
        (every-sound (λ y → x ⊔d y == y ⇒ f z x y == g z x y)
          (every-sound (λ x → every λ y → x ⊔d y == y ⇒ f z x y == g z x y)
            (every-sound
              (λ z → every λ x → every λ y →
                x ⊔d y == y ⇒ f z x y == g z x y)
              h z) x) y)
        (subst (λ w → T (w == y)) (sym p) (==-refl y)))

----------------------------------------------------------------------
-- The laws

⊔d-assoc : ∀ x y z → (x ⊔d y) ⊔d z ≡ x ⊔d (y ⊔d z)
⊔d-assoc = law₃ (λ x y z → (x ⊔d y) ⊔d z) (λ x y z → x ⊔d (y ⊔d z)) tt

⊔d-comm : ∀ x y → x ⊔d y ≡ y ⊔d x
⊔d-comm = law₂ _⊔d_ (λ x y → y ⊔d x) tt

⊔d-idem : ∀ x → x ⊔d x ≡ x
⊔d-idem = law₁ (λ x → x ⊔d x) (λ x → x) tt

⊓d-assoc : ∀ x y z → (x ⊓d y) ⊓d z ≡ x ⊓d (y ⊓d z)
⊓d-assoc = law₃ (λ x y z → (x ⊓d y) ⊓d z) (λ x y z → x ⊓d (y ⊓d z)) tt

⊓d-top : ∀ x → x ⊓d top ≡ x
⊓d-top = law₁ (λ x → x ⊓d top) (λ x → x) tt

⊓d-bot : ∀ x → x ⊓d bot ≡ bot
⊓d-bot = law₁ (λ x → x ⊓d bot) (λ _ → bot) tt

Diamond : ResourceAlgebra
Diamond = record
  { Grade = Grade
  ; _⊕_   = _⊔d_
  ; _⊗_   = _⊓d_
  ; 𝟘     = bot
  ; 𝟙     = top
  ; alt   = record { assoc = ⊔d-assoc ; comm = ⊔d-comm
                   ; idem = ⊔d-idem ; unitˡ = λ _ → refl }
  ; seq   = record { assoc = ⊓d-assoc ; unitˡ = λ _ → refl
                   ; unitʳ = ⊓d-top }
  }

-- Sequencing is monotone on both sides for the order ⊕ induces.
Diamond-ordered : IsOrdered Diamond
Diamond-ordered = record
  { ⊗-monoˡ = cond₃ (λ z x y → (z ⊓d x) ⊔d (z ⊓d y)) (λ z x y → z ⊓d y) tt
  ; ⊗-monoʳ = cond₃ (λ z x y → (x ⊓d z) ⊔d (y ⊓d z)) (λ z x y → y ⊓d z) tt
  }

Diamond-annihilating : IsAnnihilating Diamond
Diamond-annihilating = record
  { annihilˡ = λ _ → refl
  ; annihilʳ = ⊓d-bot
  }

-- Not a dioid: sequencing does not distribute over alternatives.
Diamond-not-dioid : ¬ IsDioid Diamond
Diamond-not-dioid d with IsDioid.distribˡ d a b c
... | ()
