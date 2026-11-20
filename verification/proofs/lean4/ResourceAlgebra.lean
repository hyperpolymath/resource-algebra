/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean recheck leg of the Agda theorems in src/ResourceAlgebra (standards
PROOF-POLICY §2). Route: re-proved by hand, Lean 4 core only, no Mathlib.
No exporter reaches Lean from Dedukti, so nothing here is transported.

Every theorem is axiom-free: the arithmetic is proved by structural
recursion, as in Agda's Prelude, rather than with `simp` or `omega`, which
would bring in `propext` and `Quot.sound`. The `#print axioms` block at the
end reports this, and CI fails if any theorem depends on an axiom.

Each theorem names its PROOF-STATUS row. The correspondence with the Agda
statements is recorded in docs/status/PROOF-STATUS.adoc. The differences
that hold throughout:

* Agda's `≡` lives in `Set` (and the gate runs `--without-K`); Lean's `=`
  lives in the impredicative, proof-irrelevant `Prop`. Every statement
  here is an equation, an order fact or a negation, so this changes no
  statement's strength.
* The law records (`IsAltMonoid`, `IsDioid`, …) are `Prop` structures here
  and `Set` records in Agda, with the same fields.
* `rmax`/`rmin` are defined by the same equations as Agda's `max`/`min`.
  `_+_` is Lean's `Nat.add`, which recurses on its second argument where
  Agda's recurses on its first; the two are the same function.
* HWM's bound is Lean's `Nat.le`; Agda uses its own `_≤_`. Both are the
  usual order on ℕ, so the carriers have the same elements.
-/

namespace RA

/-! ## Prelude: max and min by Agda's recursion -/

def rmax : Nat → Nat → Nat
  | 0, n => n
  | m + 1, 0 => m + 1
  | m + 1, n + 1 => rmax m n + 1

def rmin : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | m + 1, n + 1 => rmin m n + 1

theorem rmax_zero_r : ∀ m, rmax m 0 = m
  | 0 => rfl
  | _ + 1 => rfl

theorem rmax_comm : ∀ m n, rmax m n = rmax n m
  | 0, n => (rmax_zero_r n).symm
  | _ + 1, 0 => rfl
  | m + 1, n + 1 => congrArg (· + 1) (rmax_comm m n)

theorem rmax_assoc : ∀ m n p, rmax (rmax m n) p = rmax m (rmax n p)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | _ + 1, _ + 1, 0 => rfl
  | m + 1, n + 1, p + 1 => congrArg (· + 1) (rmax_assoc m n p)

theorem rmax_idem : ∀ m, rmax m m = m
  | 0 => rfl
  | m + 1 => congrArg (· + 1) (rmax_idem m)

theorem rmin_zero_r : ∀ m, rmin m 0 = 0
  | 0 => rfl
  | _ + 1 => rfl

theorem rmin_comm : ∀ m n, rmin m n = rmin n m
  | 0, n => (rmin_zero_r n).symm
  | _ + 1, 0 => rfl
  | m + 1, n + 1 => congrArg (· + 1) (rmin_comm m n)

theorem rmin_assoc : ∀ m n p, rmin (rmin m n) p = rmin m (rmin n p)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | _ + 1, _ + 1, 0 => rfl
  | m + 1, n + 1, p + 1 => congrArg (· + 1) (rmin_assoc m n p)

theorem rmin_idem : ∀ m, rmin m m = m
  | 0 => rfl
  | m + 1 => congrArg (· + 1) (rmin_idem m)

/-- `a + max b c = max (a + b) (a + c)` (Agda: `+-distribˡ-max`). -/
theorem add_rmax_l : ∀ a b c, a + rmax b c = rmax (a + b) (a + c)
  | a, 0, c => by
      rw [show rmax 0 c = c from rfl, Nat.add_zero]
      exact (rmax_absorb_add a c).symm
  | a, b + 1, 0 => by
      rw [show rmax (b + 1) 0 = b + 1 from rfl, Nat.add_zero]
      exact (rmax_absorb_add' a b).symm
  | a, b + 1, c + 1 => by
      show a + (rmax b c + 1) = rmax (a + b + 1) (a + c + 1)
      rw [rmax_succ_succ, ← add_rmax_l a b c]
      rfl
where
  rmax_succ_succ (x y : Nat) : rmax (x + 1) (y + 1) = rmax x y + 1 := rfl
  rmax_absorb_add : ∀ a c, rmax a (a + c) = a + c
    | 0, c => by rw [Nat.zero_add]; rfl
    | a + 1, c => by
        rw [Nat.succ_add]
        exact congrArg (· + 1) (rmax_absorb_add a c)
  rmax_absorb_add' : ∀ a b, rmax (a + (b + 1)) a = a + (b + 1)
    | 0, b => by rw [Nat.zero_add]; rfl
    | a + 1, b => by
        rw [Nat.succ_add]
        exact congrArg (· + 1) (rmax_absorb_add' a b)

/-- `max a b + c = max (a + c) (b + c)` (Agda: `+-distribʳ-max`). -/
theorem add_rmax_r (a b c : Nat) : rmax a b + c = rmax (a + c) (b + c) := by
  rw [Nat.add_comm, add_rmax_l, Nat.add_comm c a, Nat.add_comm c b]

/-- `a + min b c = min (a + b) (a + c)` (Agda: `+-distribˡ-min`). -/
theorem add_rmin_l : ∀ a b c, a + rmin b c = rmin (a + b) (a + c)
  | 0, b, c => by rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
  | a + 1, b, c => by
      rw [Nat.succ_add, Nat.succ_add, Nat.succ_add, add_rmin_l a b c]
      rfl

theorem add_rmin_r (a b c : Nat) : rmin a b + c = rmin (a + c) (b + c) := by
  rw [Nat.add_comm, add_rmin_l, Nat.add_comm c a, Nat.add_comm c b]

/-- `max (max p x) (max p y) = max p (max x y)` (Agda: `max-dup`). -/
theorem rmax_dup (p x y : Nat) : rmax (rmax p x) (rmax p y) = rmax p (rmax x y) := by
  rw [rmax_assoc, ← rmax_assoc x p y, rmax_comm x p, rmax_assoc p x y,
      ← rmax_assoc p p, rmax_idem]

/-- `max (max a b) (max c d) = max (max a c) (max b d)`. -/
theorem rmax_interchange (a b c d : Nat) :
    rmax (rmax a b) (rmax c d) = rmax (rmax a c) (rmax b d) := by
  rw [rmax_assoc, ← rmax_assoc b c d, rmax_comm b c, rmax_assoc c b d,
      ← rmax_assoc a c]

theorem le_rmax_left : ∀ m n, m ≤ rmax m n
  | 0, _ => Nat.zero_le _
  | _ + 1, 0 => Nat.le_refl _
  | m + 1, n + 1 => Nat.succ_le_succ (le_rmax_left m n)

theorem le_rmax_right : ∀ m n, n ≤ rmax m n
  | 0, _ => Nat.le_refl _
  | _ + 1, 0 => Nat.zero_le _
  | m + 1, n + 1 => Nat.succ_le_succ (le_rmax_right m n)

theorem rmax_lub : ∀ {a b c : Nat}, a ≤ c → b ≤ c → rmax a b ≤ c
  | 0, _, _, _, q => q
  | _ + 1, 0, _, p, _ => p
  | _ + 1, _ + 1, 0, p, _ => absurd p (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, _ + 1, p, q =>
      Nat.succ_le_succ (rmax_lub (Nat.le_of_succ_le_succ p) (Nat.le_of_succ_le_succ q))

theorem rmax_mono {a a' b b' : Nat} (p : a ≤ a') (q : b ≤ b') : rmax a b ≤ rmax a' b' :=
  rmax_lub (Nat.le_trans p (le_rmax_left a' b')) (Nat.le_trans q (le_rmax_right a' b'))

/-- `m ≤ n → max m n = n` (Agda: `max-≤`). -/
theorem rmax_of_le : ∀ {m n : Nat}, m ≤ n → rmax m n = n
  | 0, _, _ => rfl
  | _ + 1, 0, p => absurd p (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, p => congrArg (· + 1) (rmax_of_le (Nat.le_of_succ_le_succ p))

/-- `n ≤ p → max p n = p` (Agda: `max-absorb-≤`). -/
theorem rmax_absorb {n p : Nat} (q : n ≤ p) : rmax p n = p :=
  (rmax_comm p n).trans (rmax_of_le q)

/-- `m ≤ n → min m n = m` (Agda: `min-≤`). -/
theorem rmin_of_le : ∀ {m n : Nat}, m ≤ n → rmin m n = m
  | 0, _, _ => rfl
  | _ + 1, 0, p => absurd p (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, p => congrArg (· + 1) (rmin_of_le (Nat.le_of_succ_le_succ p))

/-- `n ≤ m → min m n = n` (Agda: `min-≥`). -/
theorem rmin_of_ge {m n : Nat} (p : n ≤ m) : rmin m n = n :=
  (rmin_comm m n).trans (rmin_of_le p)

/-- `max m n ≤ m + n` (Agda: `max-≤-+`). -/
theorem rmax_le_add (m n : Nat) : rmax m n ≤ m + n :=
  rmax_lub (Nat.le_add_right m n) (Nat.le_add_left n m)

/-- `max a (min b c) = min (max a b) (max a c)` (Agda: `max-distribˡ-min`). -/
theorem rmax_rmin_l : ∀ a b c, rmax a (rmin b c) = rmin (rmax a b) (rmax a c)
  | 0, _, _ => rfl
  | a + 1, 0, c => (rmin_of_le (le_rmax_left (a + 1) c)).symm
  | a + 1, b + 1, 0 => congrArg (· + 1) (rmin_of_ge (le_rmax_left a b)).symm
  | a + 1, b + 1, c + 1 => congrArg (· + 1) (rmax_rmin_l a b c)

theorem rmax_rmin_r (a b c : Nat) : rmax (rmin a b) c = rmin (rmax a c) (rmax b c) := by
  rw [rmax_comm, rmax_rmin_l, rmax_comm c a, rmax_comm c b]

/-! ## Core (C-1 .. C-3) -/

structure IsAltMonoid {G : Type} (op : G → G → G) (e : G) : Prop where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  comm  : ∀ a b, op a b = op b a
  idem  : ∀ a, op a a = a
  unitl : ∀ a, op e a = a

/-- C-1: the derived right unit. -/
theorem IsAltMonoid.unitr {G : Type} {op : G → G → G} {e : G}
    (m : IsAltMonoid op e) (a : G) : op a e = a :=
  (m.comm a e).trans (m.unitl a)

structure IsSeqMonoid {G : Type} (op : G → G → G) (e : G) : Prop where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  unitl : ∀ a, op e a = a
  unitr : ∀ a, op a e = a

/-- C-1: alternatives form an idempotent commutative monoid, sequence a monoid. -/
structure ResourceAlgebra : Type 1 where
  Grade : Type
  add   : Grade → Grade → Grade   -- ⊕, alternatives
  mul   : Grade → Grade → Grade   -- ⊗, sequence
  zero  : Grade                   -- 𝟘
  one   : Grade                   -- 𝟙
  alt   : IsAltMonoid add zero
  seq   : IsSeqMonoid mul one

namespace ResourceAlgebra
variable (R : ResourceAlgebra)

/-- The induced order: `a ≼ b` when `b` absorbs `a`. -/
def Le (a b : R.Grade) : Prop := R.add a b = b

/-! C-2: `≼` is a partial order, `𝟘` is least and `⊕` is its join. -/
theorem le_refl (a : R.Grade) : R.Le a a := R.alt.idem a

theorem le_trans {a b c : R.Grade} (p : R.Le a b) (q : R.Le b c) : R.Le a c := by
  unfold Le at *
  calc R.add a c = R.add a (R.add b c) := by rw [q]
    _ = R.add (R.add a b) c := (R.alt.assoc a b c).symm
    _ = c := by rw [p, q]

theorem le_antisym {a b : R.Grade} (p : R.Le a b) (q : R.Le b a) : a = b :=
  q.symm.trans ((R.alt.comm b a).trans p)

theorem zero_least (a : R.Grade) : R.Le R.zero a := R.alt.unitl a

theorem add_upperl (a b : R.Grade) : R.Le a (R.add a b) := by
  unfold Le
  rw [← R.alt.assoc, R.alt.idem]

theorem add_upperr (a b : R.Grade) : R.Le b (R.add a b) := by
  unfold Le
  rw [R.alt.comm a b, ← R.alt.assoc, R.alt.idem]

/-- Agda `⊕-least`: any common upper bound of `a` and `b` is above `a ⊕ b`,
so with `add_upperl`/`add_upperr` `⊕` is the join of `≼`. -/
theorem add_least {a b c : R.Grade} (p : R.Le a c) (q : R.Le b c) :
    R.Le (R.add a b) c :=
  (R.alt.assoc a b c).trans ((congrArg (R.add a) q).trans p)

end ResourceAlgebra

structure IsOrdered (R : ResourceAlgebra) : Prop where
  mono_l : ∀ c {a b}, R.Le a b → R.Le (R.mul c a) (R.mul c b)
  mono_r : ∀ c {a b}, R.Le a b → R.Le (R.mul a c) (R.mul b c)

structure IsDioid (R : ResourceAlgebra) : Prop where
  distribl : ∀ a b c, R.mul a (R.add b c) = R.add (R.mul a b) (R.mul a c)
  distribr : ∀ a b c, R.mul (R.add a b) c = R.add (R.mul a c) (R.mul b c)

/-- C-3: every dioid is ordered. -/
theorem IsDioid.ordered {R : ResourceAlgebra} (d : IsDioid R) : IsOrdered R where
  mono_l c {a b} p := by
    unfold ResourceAlgebra.Le at *
    rw [← d.distribl, p]
  mono_r c {a b} p := by
    unfold ResourceAlgebra.Le at *
    rw [← d.distribr, p]

structure IsAnnihilating (R : ResourceAlgebra) : Prop where
  annihill : ∀ a, R.mul R.zero a = R.zero
  annihilr : ∀ a, R.mul a R.zero = R.zero

/-! ## Loss (L-1) -/

inductive LGrade where
  | fin : Nat → LGrade
  | inf : LGrade
  deriving DecidableEq

open LGrade

/-- `_+g_` -/
def lplus : LGrade → LGrade → LGrade
  | fin m, fin n => fin (m + n)
  | fin _, inf => inf
  | inf, _ => inf

/-- `_⊓g_` -/
def lmin : LGrade → LGrade → LGrade
  | fin m, fin n => fin (rmin m n)
  | fin m, inf => fin m
  | inf, g => g

theorem fin_injective {m n : Nat} (h : fin m = fin n) : m = n :=
  LGrade.fin.inj h

abbrev Loss : ResourceAlgebra where
  Grade := LGrade
  add := lmin
  mul := lplus
  zero := inf
  one := fin 0
  alt := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg fin (rmin_assoc _ _ _)
    comm := by
      intro a b
      cases a <;> cases b <;> first | rfl | exact congrArg fin (rmin_comm _ _)
    idem := by intro a; cases a <;> first | rfl | exact congrArg fin (rmin_idem _)
    unitl := by intro a; rfl }
  seq := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg fin (Nat.add_assoc _ _ _)
    unitl := by intro a; cases a <;> first | rfl | exact congrArg fin (Nat.zero_add _)
    unitr := by intro a; cases a <;> rfl }

theorem Loss_dioid : IsDioid Loss where
  distribl := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg fin (add_rmin_l _ _ _)
  distribr := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg fin (add_rmin_r _ _ _)

theorem Loss_ordered : IsOrdered Loss := Loss_dioid.ordered

theorem Loss_annihilating : IsAnnihilating Loss where
  annihill := by intro a; rfl
  annihilr := by intro a; cases a <;> rfl

/-! ## MaxPlus (M-1) -/

inductive Tropical where
  | val : Nat → Tropical
  | bot : Tropical
  deriving DecidableEq

open Tropical

def tAdd : Tropical → Tropical → Tropical
  | bot, b => b
  | val m, bot => val m
  | val m, val n => val (rmax m n)

def tMul : Tropical → Tropical → Tropical
  | bot, _ => bot
  | val _, bot => bot
  | val m, val n => val (m + n)

theorem val_injective {m n : Nat} (h : val m = val n) : m = n :=
  Tropical.val.inj h

abbrev MaxPlus : ResourceAlgebra where
  Grade := Tropical
  add := tAdd
  mul := tMul
  zero := bot
  one := val 0
  alt := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg val (rmax_assoc _ _ _)
    comm := by
      intro a b
      cases a <;> cases b <;> first | rfl | exact congrArg val (rmax_comm _ _)
    idem := by intro a; cases a <;> first | rfl | exact congrArg val (rmax_idem _)
    unitl := by intro a; rfl }
  seq := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg val (Nat.add_assoc _ _ _)
    unitl := by intro a; cases a <;> first | rfl | exact congrArg val (Nat.zero_add _)
    unitr := by intro a; cases a <;> rfl }

theorem MaxPlus_dioid : IsDioid MaxPlus where
  distribl := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg val (add_rmax_l _ _ _)
  distribr := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg val (add_rmax_r _ _ _)

theorem MaxPlus_ordered : IsOrdered MaxPlus := MaxPlus_dioid.ordered

theorem MaxPlus_annihilating : IsAnnihilating MaxPlus where
  annihill := by intro a; rfl
  annihilr := by intro a; cases a <;> rfl

/-! ## HWM (H-1, H-3) -/

structure HGrade where
  peak    : Nat
  drift   : Nat
  bounded : drift ≤ peak

/-- `hwm-≡`: grades are equal when peak and drift are (the bound is a
proposition). -/
theorem HGrade.ext' : ∀ {a b : HGrade}, a.peak = b.peak → a.drift = b.drift → a = b
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

def mulH (a b : HGrade) : HGrade :=
  ⟨rmax a.peak (a.drift + b.peak), a.drift + b.drift,
   Nat.le_trans (Nat.add_le_add_left b.bounded a.drift) (le_rmax_right _ _)⟩

def addH (a b : HGrade) : HGrade :=
  ⟨rmax a.peak b.peak, rmax a.drift b.drift, rmax_mono a.bounded b.bounded⟩

def zeroH : HGrade := ⟨0, 0, Nat.le_refl 0⟩

/-- H-1 (with 𝟘 ≡ 𝟙 by construction). -/
abbrev HWM : ResourceAlgebra where
  Grade := HGrade
  add := addH
  mul := mulH
  zero := zeroH
  one := zeroH
  alt := {
    assoc := fun _ _ _ => HGrade.ext' (rmax_assoc _ _ _) (rmax_assoc _ _ _)
    comm := fun _ _ => HGrade.ext' (rmax_comm _ _) (rmax_comm _ _)
    idem := fun _ => HGrade.ext' (rmax_idem _) (rmax_idem _)
    unitl := fun _ => HGrade.ext' rfl rfl }
  seq := {
    assoc := fun a b c => HGrade.ext'
      (show rmax (rmax a.peak (a.drift + b.peak)) ((a.drift + b.drift) + c.peak)
          = rmax a.peak (a.drift + rmax b.peak (b.drift + c.peak)) by
        rw [Nat.add_assoc, rmax_assoc, add_rmax_l])
      (Nat.add_assoc _ _ _)
    unitl := fun a => HGrade.ext'
      (show rmax 0 (0 + a.peak) = a.peak by rw [Nat.zero_add]; rfl)
      (Nat.zero_add _)
    unitr := fun a => HGrade.ext'
      (show rmax a.peak (a.drift + 0) = a.peak by rw [Nat.add_zero]; exact rmax_absorb a.bounded)
      (Nat.add_zero _) }

theorem HWM_zero_eq_one : HWM.zero = HWM.one := rfl

theorem HWM_dioid : IsDioid HWM where
  distribl := fun a b c => HGrade.ext'
    (show rmax a.peak (a.drift + rmax b.peak c.peak)
        = rmax (rmax a.peak (a.drift + b.peak)) (rmax a.peak (a.drift + c.peak)) by
      rw [add_rmax_l, rmax_dup])
    (add_rmax_l _ _ _)
  distribr := fun a b c => HGrade.ext'
    (show rmax (rmax a.peak b.peak) (rmax a.drift b.drift + c.peak)
        = rmax (rmax a.peak (a.drift + c.peak)) (rmax b.peak (b.drift + c.peak)) by
      rw [add_rmax_r, rmax_interchange])
    (add_rmax_r _ _ _)

theorem HWM_ordered : IsOrdered HWM := HWM_dioid.ordered

/-- H-3: HWM has no annihilating zero. -/
theorem HWM_not_annihilating : ¬ IsAnnihilating HWM := fun z =>
  absurd (congrArg HGrade.peak (z.annihill ⟨1, 0, Nat.zero_le 1⟩) : (1 : Nat) = 0) (by decide)

/-- C-4a: a dioid need not be annihilating. -/
theorem dioid_not_annihilating : IsDioid HWM ∧ ¬ IsAnnihilating HWM :=
  ⟨HWM_dioid, HWM_not_annihilating⟩

/-! ## MinMax (N-1) -/

/-- `_⊔g_` -/
def lmax : LGrade → LGrade → LGrade
  | inf, _ => inf
  | fin _, inf => inf
  | fin m, fin n => fin (rmax m n)

abbrev MinMax : ResourceAlgebra where
  Grade := LGrade
  add := lmin
  mul := lmax
  zero := inf
  one := fin 0
  alt := Loss.alt
  seq := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg fin (rmax_assoc _ _ _)
    unitl := by intro a; cases a <;> rfl
    unitr := by intro a; cases a <;> first | rfl | exact congrArg fin (rmax_zero_r _) }

theorem MinMax_dioid : IsDioid MinMax where
  distribl := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg fin (rmax_rmin_l _ _ _)
  distribr := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg fin (rmax_rmin_r _ _ _)

theorem MinMax_ordered : IsOrdered MinMax := MinMax_dioid.ordered

theorem MinMax_annihilating : IsAnnihilating MinMax where
  annihill := by intro a; rfl
  annihilr := by intro a; cases a <;> rfl

/-! ## Morphisms (F-1 .. F-7) -/

structure Hom (A B : ResourceAlgebra) : Type where
  map    : A.Grade → B.Grade
  map_zero : map A.zero = B.zero
  map_one  : map A.one = B.one
  map_add  : ∀ a b, map (A.add a b) = B.add (map a) (map b)
  map_mul  : ∀ a b, map (A.mul a b) = B.mul (map a) (map b)

structure LaxHom (A B : ResourceAlgebra) : Type where
  map    : A.Grade → B.Grade
  map_one  : map A.one = B.one
  map_add  : ∀ a b, map (A.add a b) = B.add (map a) (map b)
  map_mul  : ∀ a b, B.Le (map (A.mul a b)) (B.mul (map a) (map b))

theorem LaxHom.mono {A B : ResourceAlgebra} (f : LaxHom A B) {a b : A.Grade}
    (p : A.Le a b) : B.Le (f.map a) (f.map b) := by
  unfold ResourceAlgebra.Le at *
  rw [← f.map_add, p]

/-- F-1: every strict morphism is lax. -/
def lax {A B : ResourceAlgebra} (h : Hom A B) : LaxHom A B where
  map := h.map
  map_one := h.map_one
  map_add := h.map_add
  map_mul a b := by rw [h.map_mul]; exact B.le_refl _

/-- F-1: identities and composition. -/
def idHom (A : ResourceAlgebra) : Hom A A :=
  ⟨id, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def Hom.comp {A B C : ResourceAlgebra} (g : Hom B C) (f : Hom A B) : Hom A C where
  map a := g.map (f.map a)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_one := by rw [f.map_one, g.map_one]
  map_add a b := by rw [f.map_add, g.map_add]
  map_mul a b := by rw [f.map_mul, g.map_mul]

def idLax (A : ResourceAlgebra) : LaxHom A A := lax (idHom A)

def LaxHom.comp {A B C : ResourceAlgebra} (g : LaxHom B C) (f : LaxHom A B) :
    LaxHom A C where
  map a := g.map (f.map a)
  map_one := by rw [f.map_one, g.map_one]
  map_add a b := by rw [f.map_add, g.map_add]
  map_mul a b := C.le_trans (g.mono (f.map_mul a b)) (g.map_mul _ _)

/-- F-2: `peak : HWM → MaxPlus` is lax. -/
def peakLax : LaxHom HWM MaxPlus where
  map g := val g.peak
  map_one := rfl
  map_add _ _ := rfl
  map_mul a b := congrArg val (rmax_of_le (rmax_lub (Nat.le_add_right a.peak b.peak)
    (Nat.add_le_add_right a.bounded b.peak)))

/-- F-3: `peak` does not preserve ⊗. -/
theorem peak_not_strict :
    ¬ ∀ a b : HGrade, val (mulH a b).peak = tMul (val a.peak) (val b.peak) := fun f =>
  absurd (val_injective (f ⟨2, 0, Nat.zero_le 2⟩ ⟨3, 0, Nat.zero_le 3⟩) : (3 : Nat) = 5)
    (by decide)

/-- F-4: no strict morphism leaves HWM for an algebra with 𝟘 ≠ 𝟙. -/
theorem no_strict_from_HWM (B : ResourceAlgebra) (hne : B.zero ≠ B.one)
    (h : Hom HWM B) : False :=
  hne (h.map_zero.symm.trans h.map_one)

theorem no_strict_HWM_MaxPlus (h : Hom HWM MaxPlus) : False :=
  no_strict_from_HWM MaxPlus (fun e => Tropical.noConfusion e) h

theorem no_strict_HWM_Loss (h : Hom HWM Loss) : False :=
  no_strict_from_HWM Loss (fun e => LGrade.noConfusion e) h

/-! F-5: exactly two strict morphisms Loss → MaxPlus. -/

def zeroTest : LGrade → Tropical
  | fin 0 => val 0
  | fin (_ + 1) => bot
  | inf => bot

def support : LGrade → Tropical
  | fin _ => val 0
  | inf => bot

/-- `zeroTest` sends every positive sum to `bot`. -/
theorem zeroTest_succ_add (m : Nat) : ∀ n, zeroTest (fin (m + 1 + n)) = bot
  | 0 => rfl
  | _ + 1 => rfl

def zeroTestHom : Hom Loss MaxPlus where
  map := zeroTest
  map_zero := rfl
  map_one := rfl
  map_add a b := by
    rcases a with (_ | _) | _ <;> rcases b with (_ | _) | _ <;> rfl
  map_mul a b := by
    rcases a with (_ | m) | _ <;> rcases b with (_ | _) | _ <;>
      first | rfl | exact zeroTest_succ_add m _

def supportHom : Hom Loss MaxPlus where
  map := support
  map_zero := rfl
  map_one := rfl
  map_add a b := by cases a <;> cases b <;> rfl
  map_mul a b := by cases a <;> cases b <;> rfl

/-- F-5: the two maps differ (Agda: `maps-disagree-at-positive`). -/
theorem maps_disagree_at_positive (n : Nat) :
    zeroTest (fin (n + 1)) ≠ support (fin (n + 1)) :=
  fun e => Tropical.noConfusion e

/-- F-5: every strict morphism Loss → MaxPlus is one of the two, and the
result says which. As Agda's `_⊎_`, this is a sum a caller can branch on
(`PSum`), not a propositional `Or`. -/
def Loss_to_MaxPlus (h : Hom Loss MaxPlus) :
    PSum (∀ a, h.map a = zeroTest a) (∀ a, h.map a = support a) := by
  have one : h.map (fin 0) = val 0 := h.map_one
  have step : ∀ n, h.map (fin (n + 1)) = tMul (h.map (fin n)) (h.map (fin 1)) :=
    fun n => h.map_mul (fin n) (fin 1)
  have pin : h.map (fin 0) = tAdd (h.map (fin 0)) (h.map (fin 1)) :=
    h.map_add (fin 0) (fin 1)
  rw [one] at pin
  cases e : h.map (fin 1) with
  | bot =>
    left
    intro a
    rcases a with (_ | n) | _
    · exact one
    · rw [step n, e]; cases h.map (fin n) <;> rfl
    · exact h.map_zero
  | val c =>
    right
    have c0 : c = 0 := by
      rw [e] at pin
      exact (val_injective pin : 0 = rmax 0 c).trans rfl |>.symm
    have fv : ∀ n, h.map (fin n) = val 0 := by
      intro n
      induction n with
      | zero => exact one
      | succ n ih => rw [step n, ih, e, c0]; rfl
    intro a
    cases a with
    | fin n => exact fv n
    | inf => exact h.map_zero

theorem Loss_to_MaxPlus_collapses (h : Hom Loss MaxPlus) : h.map (fin 1) = h.map (fin 2) := by
  rcases Loss_to_MaxPlus h with z | s
  · rw [z, z]; rfl
  · rw [s, s]; rfl

theorem no_injective_Loss_to_MaxPlus (h : Hom Loss MaxPlus)
    (inj : ∀ a b, h.map a = h.map b → a = b) : False :=
  absurd (fin_injective (inj (fin 1) (fin 2) (Loss_to_MaxPlus_collapses h))) (by decide)

/-! F-6: exactly one strict morphism MaxPlus → Loss. -/

def support' : Tropical → LGrade
  | val _ => fin 0
  | bot => inf

def support'Hom : Hom MaxPlus Loss where
  map := support'
  map_zero := rfl
  map_one := rfl
  map_add a b := by cases a <;> cases b <;> rfl
  map_mul a b := by cases a <;> cases b <;> rfl

theorem MaxPlus_to_Loss (h : Hom MaxPlus Loss) : ∀ a, h.map a = support' a := by
  have one : h.map (val 0) = fin 0 := h.map_one
  have absorb : h.map (val 1) = lmin (h.map (val 0)) (h.map (val 1)) :=
    h.map_add (val 0) (val 1)
  rw [one] at absorb
  have v1 : h.map (val 1) = fin 0 := by
    cases e : h.map (val 1) with
    | fin c => rw [e] at absorb; exact absorb
    | inf => rw [e] at absorb; exact LGrade.noConfusion absorb
  have fv : ∀ n, h.map (val n) = fin 0 := by
    intro n
    induction n with
    | zero => exact one
    | succ n ih =>
      have step : h.map (val (n + 1)) = lplus (h.map (val n)) (h.map (val 1)) :=
        h.map_mul (val n) (val 1)
      rw [step, ih, v1]; rfl
  intro a
  cases a with
  | val n => exact fv n
  | bot => exact h.map_zero

/-- F-7: the identity is lax Loss → MinMax. -/
def lossBottleneck : LaxHom Loss MinMax where
  map a := a
  map_one := rfl
  map_add _ _ := rfl
  map_mul a b := by
    cases a <;> cases b <;>
      first | rfl | exact congrArg fin (rmin_of_ge (rmax_le_add _ _))

/-! ## Separation (S-1 .. S-4) -/

def two : HGrade := ⟨2, 0, Nat.zero_le 2⟩
def three : HGrade := ⟨3, 0, Nat.zero_le 3⟩

/-- S-1 -/
theorem occupancy_is_not_cost : (mulH two three).peak ≠ 5 := by decide

/-- S-2 -/
theorem alternatives_differ : lmin (fin 2) (fin 3) ≠ fin 3 := by decide

/-- S-3 -/
theorem maxplus_order : MaxPlus.Le (val 1) (val 2) := rfl
theorem loss_order_reversed : Loss.Le (fin 2) (fin 1) := rfl

/-- S-4 -/
theorem bottleneck_is_not_sum : lmax (fin 2) (fin 3) ≠ lplus (fin 2) (fin 3) := by decide

/-! ## Questions (Q-1 .. Q-4) -/

/-- `Q n`: n booleans, by recursion on n. `true` means the question is lost. -/
def Q : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Q n

/-- `rep` -/
def qrep (b : Bool) : (n : Nat) → Q n
  | 0 => ()
  | n + 1 => (b, qrep b n)

/-- `zip` -/
def qzip (f : Bool → Bool → Bool) : (n : Nat) → Q n → Q n → Q n
  | 0, _, _ => ()
  | n + 1, x, y => (f x.1 y.1, qzip f n x.2 y.2)

theorem qcons_eq {n : Nat} {a a' : Bool} {q q' : Q n} :
    a = a' → q = q' → ((a, q) : Q (n + 1)) = (a', q')
  | rfl, rfl => rfl

theorem qzip_assoc {f : Bool → Bool → Bool} (p : ∀ a b c, f (f a b) c = f a (f b c)) :
    ∀ n (x y z : Q n), qzip f n (qzip f n x y) z = qzip f n x (qzip f n y z)
  | 0, _, _, _ => rfl
  | n + 1, x, y, z => qcons_eq (p x.1 y.1 z.1) (qzip_assoc p n x.2 y.2 z.2)

theorem qzip_comm {f : Bool → Bool → Bool} (p : ∀ a b, f a b = f b a) :
    ∀ n (x y : Q n), qzip f n x y = qzip f n y x
  | 0, _, _ => rfl
  | n + 1, x, y => qcons_eq (p x.1 y.1) (qzip_comm p n x.2 y.2)

theorem qzip_idem {f : Bool → Bool → Bool} (p : ∀ a, f a a = a) :
    ∀ n (x : Q n), qzip f n x x = x
  | 0, _ => rfl
  | n + 1, (a, x) => qcons_eq (p a) (qzip_idem p n x)

theorem qzip_unitl {f : Bool → Bool → Bool} (e : Bool) (p : ∀ a, f e a = a) :
    ∀ n (x : Q n), qzip f n (qrep e n) x = x
  | 0, _ => rfl
  | n + 1, (a, x) => qcons_eq (p a) (qzip_unitl e p n x)

theorem qzip_unitr {f : Bool → Bool → Bool} (e : Bool) (p : ∀ a, f a e = a) :
    ∀ n (x : Q n), qzip f n x (qrep e n) = x
  | 0, _ => rfl
  | n + 1, (a, x) => qcons_eq (p a) (qzip_unitr e p n x)

theorem qzip_zerol {f : Bool → Bool → Bool} (z : Bool) (p : ∀ a, f z a = z) :
    ∀ n (x : Q n), qzip f n (qrep z n) x = qrep z n
  | 0, _ => rfl
  | n + 1, x => qcons_eq (p x.1) (qzip_zerol z p n x.2)

theorem qzip_zeror {f : Bool → Bool → Bool} (z : Bool) (p : ∀ a, f a z = z) :
    ∀ n (x : Q n), qzip f n x (qrep z n) = qrep z n
  | 0, _ => rfl
  | n + 1, x => qcons_eq (p x.1) (qzip_zeror z p n x.2)

/-- Q-1: ⊕ = intersection (`and`), ⊗ = union (`or`), 𝟘 = all lost, 𝟙 = none lost. -/
abbrev Questions (n : Nat) : ResourceAlgebra where
  Grade := Q n
  add := qzip and n
  mul := qzip or n
  zero := qrep true n
  one := qrep false n
  alt := {
    assoc := qzip_assoc (by intro a b c; cases a <;> rfl) n
    comm := qzip_comm (by intro a b; cases a <;> cases b <;> rfl) n
    idem := qzip_idem (by intro a; cases a <;> rfl) n
    unitl := qzip_unitl true (fun _ => rfl) n }
  seq := {
    assoc := qzip_assoc (by intro a b c; cases a <;> rfl) n
    unitl := qzip_unitl false (fun _ => rfl) n
    unitr := qzip_unitr false (by intro a; cases a <;> rfl) n }

theorem bor_band_l : ∀ a b c : Bool, or a (and b c) = and (or a b) (or a c)
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem bor_band_r : ∀ a b c : Bool, or (and a b) c = and (or a c) (or b c)
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true => rfl
  | false, true, false => rfl
  | false, false, true => rfl
  | false, false, false => rfl

theorem qzip_distribl : ∀ n (a b c : Q n),
    qzip or n a (qzip and n b c) = qzip and n (qzip or n a b) (qzip or n a c)
  | 0, _, _, _ => rfl
  | n + 1, a, b, c => qcons_eq (bor_band_l a.1 b.1 c.1) (qzip_distribl n a.2 b.2 c.2)

theorem qzip_distribr : ∀ n (a b c : Q n),
    qzip or n (qzip and n a b) c = qzip and n (qzip or n a c) (qzip or n b c)
  | 0, _, _, _ => rfl
  | n + 1, a, b, c => qcons_eq (bor_band_r a.1 b.1 c.1) (qzip_distribr n a.2 b.2 c.2)

theorem Questions_dioid (n : Nat) : IsDioid (Questions n) where
  distribl := qzip_distribl n
  distribr := qzip_distribr n

theorem Questions_ordered (n : Nat) : IsOrdered (Questions n) := (Questions_dioid n).ordered

theorem Questions_annihilating (n : Nat) : IsAnnihilating (Questions n) where
  annihill := qzip_zerol true (fun _ => rfl) n
  annihilr := qzip_zeror true (by intro a; cases a <;> rfl) n

/-- Question 0: the order of the pieces. Question 1: do the two copies differ. -/
def collapse : Q 2 := (false, true, ())
def shuffle : Q 2 := (true, false, ())

/-- Q-2 -/
theorem same_amount_different_loss : collapse ≠ shuffle :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

/-- Q-3 -/
theorem both_lost : (Questions 2).mul collapse shuffle = qrep true 2 := rfl

/-- Q-4 -/
theorem no_branch_achieves_meet : (Questions 2).add collapse shuffle = qrep false 2 := rfl

/-! ## Morphisms out of Questions (F-8 .. F-10) -/

/-- Lost goes to 𝟘, kept goes to 𝟙. -/
def verdict (B : ResourceAlgebra) : Bool → B.Grade
  | true => B.zero
  | false => B.one

theorem verdict_and (B : ResourceAlgebra) :
    ∀ a b, verdict B (and a b) = B.add (verdict B a) (verdict B b)
  | true, true => (B.alt.idem B.zero).symm
  | true, false => (B.alt.unitl B.one).symm
  | false, true => (B.alt.unitr B.one).symm
  | false, false => (B.alt.idem B.one).symm

theorem verdict_or (B : ResourceAlgebra) (zz : B.mul B.zero B.zero = B.zero) :
    ∀ a b, verdict B (or a b) = B.mul (verdict B a) (verdict B b)
  | true, true => zz.symm
  | true, false => (B.seq.unitr B.zero).symm
  | false, true => (B.seq.unitl B.zero).symm
  | false, false => (B.seq.unitl B.one).symm

/-- F-8: the one strict morphism out of one question. -/
def oneQuestionHom (B : ResourceAlgebra) (zz : B.mul B.zero B.zero = B.zero) :
    Hom (Questions 1) B where
  map x := verdict B x.1
  map_zero := rfl
  map_one := rfl
  map_add x y := verdict_and B x.1 y.1
  map_mul x y := verdict_or B zz x.1 y.1

/-- F-8: the condition is necessary. -/
theorem one_question_needs {B : ResourceAlgebra} (h : Hom (Questions 1) B) :
    B.mul B.zero B.zero = B.zero :=
  have z : h.map (qrep true 1) = B.zero := h.map_zero
  have m : h.map (qrep true 1) = B.mul (h.map (qrep true 1)) (h.map (qrep true 1)) :=
    h.map_mul (qrep true 1) (qrep true 1)
  (congrArg (fun g => B.mul g g) z).symm.trans (m.symm.trans z)

/-- F-8: every strict morphism out of one question is that map. -/
theorem one_question_unique {B : ResourceAlgebra} (h : Hom (Questions 1) B) :
    ∀ x : Q 1, h.map x = verdict B x.1
  | (true, ()) => h.map_zero
  | (false, ()) => h.map_one

/-- F-9: each question can be read alone. -/
def firstQuestion (n : Nat) : Hom (Questions (n + 1)) (Questions 1) where
  map x := (x.1, ())
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def laterQuestions (n : Nat) : Hom (Questions (n + 1)) (Questions n) where
  map x := x.2
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

/-- `count`: how many questions are lost. -/
def qcount : (n : Nat) → Q n → Nat
  | 0, _ => 0
  | n + 1, x => cond x.1 (qcount n x.2 + 1) (qcount n x.2)

/-- F-10: the number of lost questions does not preserve alternatives. -/
theorem count_not_add :
    ¬ ∀ a b : Q 2, fin (qcount 2 ((Questions 2).add a b))
        = lmin (fin (qcount 2 a)) (fin (qcount 2 b)) := fun f =>
  absurd (fin_injective (f collapse shuffle) : (0 : Nat) = 1) (by decide)

/-! ## Evidence (E-1)

The status of a proof-ledger row, as a chain, weakest first:
`openRow < testedOnly < argued < provenWithPostulates < proven`. A status
is coded by its rank (0 to 4); alternatives take the max of the ranks and
sequence the min, as in Agda's `Instances/Evidence.agda`. -/

/-- `min m n ≤ m` (Agda: `min-≤-left`). -/
theorem rmin_le_left : ∀ m n, rmin m n ≤ m
  | 0, _ => Nat.zero_le _
  | _ + 1, 0 => Nat.zero_le _
  | m + 1, n + 1 => Nat.succ_le_succ (rmin_le_left m n)

/-- `min m n ≤ n` (Agda: `min-≤-right`). -/
theorem rmin_le_right (m n : Nat) : rmin m n ≤ n := by
  rw [rmin_comm]
  exact rmin_le_left n m

/-- `k ≤ m → k ≤ n → k ≤ min m n` (Agda: `min-glb`). -/
theorem rmin_glb : ∀ {k m n : Nat}, k ≤ m → k ≤ n → k ≤ rmin m n
  | 0, _, _, _, _ => Nat.zero_le _
  | _ + 1, 0, _, p, _ => absurd p (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, 0, _, q => absurd q (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, _ + 1, p, q =>
      Nat.succ_le_succ (rmin_glb (Nat.le_of_succ_le_succ p) (Nat.le_of_succ_le_succ q))

/-- `min a (max b c) = max (min a b) (min a c)` (Agda: `min-distribˡ-max`). -/
theorem rmin_rmax_l : ∀ a b c, rmin a (rmax b c) = rmax (rmin a b) (rmin a c)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | a + 1, b + 1, 0 => (rmax_zero_r (rmin a b + 1)).symm
  | a + 1, b + 1, c + 1 => congrArg (· + 1) (rmin_rmax_l a b c)

/-- `max m n = n → m ≤ n` (Agda: `max-≡→≤`). -/
theorem rmax_eq_le {m n : Nat} (p : rmax m n = n) : m ≤ n := by
  rw [← p]
  exact le_rmax_left m n

/-- The closed status vocabulary of PROOF-POLICY §5, weakest first. -/
inductive Status where
  | openRow
  | testedOnly
  | argued
  | provenWithPostulates
  | proven

open Status

def rank : Status → Nat
  | openRow => 0
  | testedOnly => 1
  | argued => 2
  | provenWithPostulates => 3
  | proven => 4

/-- Every rank from 4 up names `proven`. -/
def fromRank : Nat → Status
  | 0 => openRow
  | 1 => testedOnly
  | 2 => argued
  | 3 => provenWithPostulates
  | _ + 4 => proven

theorem fromRank_rank : ∀ s, fromRank (rank s) = s
  | openRow => rfl
  | testedOnly => rfl
  | argued => rfl
  | provenWithPostulates => rfl
  | proven => rfl

theorem rank_le_four : ∀ s, rank s ≤ 4
  | openRow => Nat.zero_le 4
  | testedOnly => Nat.succ_le_succ (Nat.zero_le 3)
  | argued => Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2))
  | provenWithPostulates => Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1)))
  | proven => Nat.le_refl 4

theorem rank_fromRank : ∀ {n : Nat}, n ≤ 4 → rank (fromRank n) = n
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, p => absurd
      (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
        (Nat.le_of_succ_le_succ p))))
      (Nat.not_succ_le_zero _)

/-- Two statuses with one rank are one status. -/
theorem rank_injective {s t : Status} (p : rank s = rank t) : s = t :=
  (fromRank_rank s).symm.trans ((congrArg fromRank p).trans (fromRank_rank t))

/-- `_⊔e_`: alternatives keep the stronger status. -/
def eJoin (s t : Status) : Status := fromRank (rmax (rank s) (rank t))

/-- `_⊓e_`: sequence keeps the weaker status. -/
def eMeet (s t : Status) : Status := fromRank (rmin (rank s) (rank t))

theorem rank_eJoin (s t : Status) : rank (eJoin s t) = rmax (rank s) (rank t) :=
  rank_fromRank (rmax_lub (rank_le_four s) (rank_le_four t))

theorem rank_eMeet (s t : Status) : rank (eMeet s t) = rmin (rank s) (rank t) :=
  rank_fromRank (Nat.le_trans (rmin_le_left (rank s) (rank t)) (rank_le_four s))

theorem eJoin_assoc (a b c : Status) : eJoin (eJoin a b) c = eJoin a (eJoin b c) :=
  rank_injective (by rw [rank_eJoin, rank_eJoin, rank_eJoin, rank_eJoin, rmax_assoc])

theorem eJoin_comm (a b : Status) : eJoin a b = eJoin b a :=
  congrArg fromRank (rmax_comm (rank a) (rank b))

theorem eJoin_idem (a : Status) : eJoin a a = a :=
  (congrArg fromRank (rmax_idem (rank a))).trans (fromRank_rank a)

theorem eJoin_unitl (a : Status) : eJoin openRow a = a := fromRank_rank a

theorem eMeet_assoc (a b c : Status) : eMeet (eMeet a b) c = eMeet a (eMeet b c) :=
  rank_injective (by rw [rank_eMeet, rank_eMeet, rank_eMeet, rank_eMeet, rmin_assoc])

theorem eMeet_comm (a b : Status) : eMeet a b = eMeet b a :=
  congrArg fromRank (rmin_comm (rank a) (rank b))

theorem eMeet_unitl (a : Status) : eMeet proven a = a :=
  (congrArg fromRank (rmin_of_ge (rank_le_four a))).trans (fromRank_rank a)

theorem eMeet_unitr (a : Status) : eMeet a proven = a :=
  (eMeet_comm a proven).trans (eMeet_unitl a)

/-- E-1: ⊕ = the stronger, ⊗ = the weaker, 𝟘 = `openRow`, 𝟙 = `proven`. -/
abbrev Evidence : ResourceAlgebra where
  Grade := Status
  add := eJoin
  mul := eMeet
  zero := openRow
  one := proven
  alt := { assoc := eJoin_assoc, comm := eJoin_comm, idem := eJoin_idem, unitl := eJoin_unitl }
  seq := { assoc := eMeet_assoc, unitl := eMeet_unitl, unitr := eMeet_unitr }

theorem eMeet_distribl (a b c : Status) :
    eMeet a (eJoin b c) = eJoin (eMeet a b) (eMeet a c) :=
  rank_injective (by
    rw [rank_eMeet, rank_eJoin, rmin_rmax_l, rank_eJoin, rank_eMeet, rank_eMeet])

theorem eMeet_distribr (a b c : Status) :
    eMeet (eJoin a b) c = eJoin (eMeet a c) (eMeet b c) := by
  rw [eMeet_comm, eMeet_distribl, eMeet_comm c a, eMeet_comm c b]

/-- E-1 -/
theorem Evidence_dioid : IsDioid Evidence where
  distribl := eMeet_distribl
  distribr := eMeet_distribr

theorem Evidence_ordered : IsOrdered Evidence := Evidence_dioid.ordered

theorem Evidence_annihilating : IsAnnihilating Evidence where
  annihill _ := rfl
  annihilr a := congrArg fromRank (rmin_zero_r (rank a))

/-! E-1: the order is the rank order, and sequence is its meet. -/

/-- Agda `≼→≤`. -/
theorem le_to_rank {a b : Status} (p : Evidence.Le a b) : rank a ≤ rank b :=
  rmax_eq_le ((rank_eJoin a b).symm.trans (congrArg rank p))

/-- Agda `≤→≼`. -/
theorem rank_to_le {a b : Status} (p : rank a ≤ rank b) : Evidence.Le a b :=
  (congrArg fromRank (rmax_of_le p)).trans (fromRank_rank b)

/-- Agda `≼-proven`. -/
theorem le_proven (a : Status) : Evidence.Le a proven := rank_to_le (rank_le_four a)

/-- Agda `⊓e-lowerˡ`. -/
theorem eMeet_lowerl (a b : Status) : Evidence.Le (eMeet a b) a :=
  rank_to_le (by rw [rank_eMeet]; exact rmin_le_left (rank a) (rank b))

/-- Agda `⊓e-lowerʳ`. -/
theorem eMeet_lowerr (a b : Status) : Evidence.Le (eMeet a b) b :=
  rank_to_le (by rw [rank_eMeet]; exact rmin_le_right (rank a) (rank b))

/-- Agda `⊓e-greatest`. -/
theorem eMeet_greatest {a b c : Status} (p : Evidence.Le c a) (q : Evidence.Le c b) :
    Evidence.Le c (eMeet a b) :=
  rank_to_le (by rw [rank_eMeet]; exact rmin_glb (le_to_rank p) (le_to_rank q))

/-! ## Evidence ledger (E-2, E-3)

A ledger is a list of rows, newest first. A row's dependencies index the
rows after it, so no dependency cycle can be written.

`Mem`, `Dep`, `Reach` and `Respects` are `Prop` here, where Agda's are
`Set` (`_⊎_` and `⊥` become `∨` and `False`). They occur only as
hypotheses, or, for `Respects`, as a record whose fields conclude in
equations, so no statement changes strength. `Reach` takes its starting
row as an index, not a parameter. -/

/-- Agda's `map`, by the same two equations. -/
def mapList {A B : Type} (f : A → B) : List A → List B
  | [] => []
  | x :: xs => f x :: mapList f xs

/-- `_∈_`, by recursion on the list. -/
def Mem (j : Nat) : List Nat → Prop
  | [] => False
  | k :: ks => j = k ∨ Mem j ks

/-- `⨅`: the meet of a list of statuses; the empty meet is `proven`. -/
def meetAll : List Status → Status
  | [] => proven
  | s :: ss => eMeet s (meetAll ss)

theorem meetAll_lower {f : Nat → Status} :
    ∀ (js : List Nat) {j : Nat}, Mem j js → Evidence.Le (meetAll (mapList f js)) (f j)
  | [], _, h => False.elim h
  | k :: ks, _, Or.inl rfl => eMeet_lowerl (f k) (meetAll (mapList f ks))
  | k :: ks, _, Or.inr p =>
      Evidence.le_trans (eMeet_lowerr (f k) (meetAll (mapList f ks))) (meetAll_lower ks p)

theorem meetAll_greatest {f : Nat → Status} {z : Status} :
    ∀ (js : List Nat), (∀ {j}, Mem j js → Evidence.Le z (f j)) →
      Evidence.Le z (meetAll (mapList f js))
  | [], _ => le_proven z
  | _ :: ks, h => eMeet_greatest (h (Or.inl rfl)) (meetAll_greatest ks (fun p => h (Or.inr p)))

structure Row where
  row ::
  own  : Status      -- the §5 token of the row's own artefact
  deps : List Nat    -- the rows it depends on, as indices into the rows after it

abbrev Ledger := List Row

def ownOf : Ledger → Nat → Status
  | [], _ => proven
  | r :: _, 0 => r.own
  | _ :: L, i + 1 => ownOf L i

/-- `Dep L i j`: row `i` depends directly on row `j`. -/
def Dep : Ledger → Nat → Nat → Prop
  | [], _, _ => False
  | _ :: _, 0, 0 => False
  | r :: _, 0, j + 1 => Mem j r.deps
  | _ :: _, _ + 1, 0 => False
  | _ :: L, i + 1, j + 1 => Dep L i j

/-- `Reach L i j`: row `i` depends on row `j` through zero or more steps. -/
inductive Reach (L : Ledger) : Nat → Nat → Prop where
  | stay {i : Nat} : Reach L i i
  | step {i k j : Nat} : Dep L i k → Reach L k j → Reach L i j

/-- The derived status. -/
def eff : Ledger → Nat → Status
  | [], _ => proven
  | r :: L, 0 => eMeet r.own (meetAll (mapList (eff L) r.deps))
  | _ :: L, i + 1 => eff L i

/-- E-2: never stronger than the row's own evidence. -/
theorem eff_le_own : ∀ L i, Evidence.Le (eff L i) (ownOf L i)
  | [], _ => Evidence.le_refl proven
  | r :: L, 0 => eMeet_lowerl r.own (meetAll (mapList (eff L) r.deps))
  | _ :: L, i + 1 => eff_le_own L i

/-- E-2: nor than any row it depends on. -/
theorem eff_le_dep : ∀ L i j, Dep L i j → Evidence.Le (eff L i) (eff L j)
  | [], _, _, d => False.elim d
  | _ :: _, 0, 0, d => False.elim d
  | r :: L, 0, _ + 1, p =>
      Evidence.le_trans (eMeet_lowerr r.own (meetAll (mapList (eff L) r.deps)))
        (meetAll_lower r.deps p)
  | _ :: _, _ + 1, 0, d => False.elim d
  | _ :: L, i + 1, j + 1, d => eff_le_dep L i j d

/-- E-2: a row is only as strong as the weakest step it depends on. -/
theorem eff_le_reach (L : Ledger) {i j : Nat} (r : Reach L i j) :
    Evidence.Le (eff L i) (ownOf L j) := by
  induction r with
  | stay => exact eff_le_own L _
  | step d _ ih => exact Evidence.le_trans (eff_le_dep L _ _ d) ih

/-- An assignment respects a ledger when no row is stronger than its own
evidence or than a row it depends on. -/
structure Respects (L : Ledger) (s : Nat → Status) : Prop where
  below_own : ∀ i, Evidence.Le (s i) (ownOf L i)
  below_dep : ∀ i j, Dep L i j → Evidence.Le (s i) (s j)

/-- E-3 -/
theorem eff_respects (L : Ledger) : Respects L (eff L) :=
  ⟨eff_le_own L, eff_le_dep L⟩

/-- Restricting an assignment of `r :: L` to `L` keeps it respectful. -/
theorem restrict {r : Row} {L : Ledger} {s : Nat → Status} (ρ : Respects (r :: L) s) :
    Respects L (fun i => s (i + 1)) :=
  ⟨fun i => ρ.below_own (i + 1), fun i j d => ρ.below_dep (i + 1) (j + 1) d⟩

/-- E-3: every assignment that respects the ledger is below `eff`. -/
theorem eff_greatest : ∀ L s, Respects L s → ∀ i, Evidence.Le (s i) (eff L i)
  | [], s, _, i => le_proven (s i)
  | r :: L, s, ρ, 0 =>
      eMeet_greatest (ρ.below_own 0)
        (meetAll_greatest r.deps (fun {j} p =>
          Evidence.le_trans (ρ.below_dep 0 (j + 1) p)
            (eff_greatest L (fun k => s (k + 1)) (restrict ρ) j)))
  | _ :: L, s, ρ, i + 1 => eff_greatest L (fun k => s (k + 1)) (restrict ρ) i

/-! The worked ledger of `tests/unit/EvidenceTest.agda`, with its expected
values. They pin the chain order, which the laws above cannot see. -/

theorem sequence_keeps_the_weaker : Evidence.mul argued testedOnly = testedOnly := rfl
theorem alternative_keeps_the_stronger : Evidence.add argued testedOnly = argued := rfl
theorem provenWithPostulates_below_proven :
    Evidence.mul proven provenWithPostulates = provenWithPostulates := rfl
theorem open_annihilates : Evidence.mul proven openRow = openRow := rfl

/-- Newest first; indices count back from each row. -/
def exampleLedger : Ledger :=
  [ Row.row proven [0, 1]      -- row 4: on row 3 and row 2
  , Row.row testedOnly []      -- row 3
  , Row.row proven [0, 1]      -- row 2: on row 1 and row 0
  , Row.row argued []          -- row 1
  , Row.row proven [] ]        -- row 0

theorem row2_is_argued : eff exampleLedger 2 = argued := rfl
theorem row4_is_tested_only : eff exampleLedger 0 = testedOnly := rfl
theorem row0_keeps_its_evidence : eff exampleLedger 4 = proven := rfl
/-! ## Diamond (C-4b)

The diamond lattice M3: join for alternatives, meet for sequence, bottom
for 𝟘 and top for 𝟙. Meet is monotone and the bottom annihilates, but M3 is
not distributive, so meet does not distribute over join. Every law is a
closed statement over five constructors, discharged case by case. -/

inductive DGrade where
  | bot | top | a | b | c
  deriving DecidableEq

/-- Agda `_⊔d_`, the join. -/
def djoin : DGrade → DGrade → DGrade
  | .bot, y => y
  | .top, _ => .top
  | .a, .bot => .a
  | .a, .top => .top
  | .a, .a => .a
  | .a, .b => .top
  | .a, .c => .top
  | .b, .bot => .b
  | .b, .top => .top
  | .b, .a => .top
  | .b, .b => .b
  | .b, .c => .top
  | .c, .bot => .c
  | .c, .top => .top
  | .c, .a => .top
  | .c, .b => .top
  | .c, .c => .c

/-- Agda `_⊓d_`, the meet. -/
def dmeet : DGrade → DGrade → DGrade
  | .bot, _ => .bot
  | .top, y => y
  | .a, .bot => .bot
  | .a, .top => .a
  | .a, .a => .a
  | .a, .b => .bot
  | .a, .c => .bot
  | .b, .bot => .bot
  | .b, .top => .b
  | .b, .a => .bot
  | .b, .b => .b
  | .b, .c => .bot
  | .c, .bot => .bot
  | .c, .top => .c
  | .c, .a => .bot
  | .c, .b => .bot
  | .c, .c => .c

abbrev Diamond : ResourceAlgebra where
  Grade := DGrade
  add := djoin
  mul := dmeet
  zero := .bot
  one := .top
  alt := {
    assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
    comm := by intro x y; cases x <;> cases y <;> rfl
    idem := by intro x; cases x <;> rfl
    unitl := fun _ => rfl }
  seq := {
    assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
    unitl := fun _ => rfl
    unitr := by intro x; cases x <;> rfl }

theorem Diamond_ordered : IsOrdered Diamond where
  mono_l z {x y} p := by
    cases z <;> cases x <;> cases y <;> first | rfl | (cases p)
  mono_r z {x y} p := by
    cases z <;> cases x <;> cases y <;> first | rfl | (cases p)

theorem Diamond_annihilating : IsAnnihilating Diamond where
  annihill _ := rfl
  annihilr x := by cases x <;> rfl

/-- Not a dioid: `a ⊓ (b ⊔ c) = a`, while `(a ⊓ b) ⊔ (a ⊓ c) = ⊥`. -/
theorem Diamond_not_dioid : ¬ IsDioid Diamond := fun d =>
  absurd (d.distribl .a .b .c : DGrade.a = DGrade.bot) (by decide)

/-- C-4b: an annihilating ordered algebra need not be a dioid. -/
theorem ordered_annihilating_not_dioid :
    IsOrdered Diamond ∧ IsAnnihilating Diamond ∧ ¬ IsDioid Diamond :=
  ⟨Diamond_ordered, Diamond_annihilating, Diamond_not_dioid⟩

/-! ## Parallel composition (P-1 .. P-4)

A second, commutative product on the same unit, distributing over
alternatives. Which way it exchanges with sequence depends on the resource,
so the two exchange laws are stated apart. -/

structure IsParallel (R : ResourceAlgebra) (par : R.Grade → R.Grade → R.Grade) : Prop where
  assoc    : ∀ a b c, par (par a b) c = par a (par b c)
  comm     : ∀ a b, par a b = par b a
  unitl    : ∀ a, par R.one a = a
  distribl : ∀ a b c, par a (R.add b c) = R.add (par a b) (par a c)

/-- P-1: the derived right unit, right distributivity and monotonicity. -/
theorem IsParallel.unitr {R : ResourceAlgebra} {par : R.Grade → R.Grade → R.Grade}
    (p : IsParallel R par) (a : R.Grade) : par a R.one = a :=
  (p.comm a R.one).trans (p.unitl a)

theorem IsParallel.distribr {R : ResourceAlgebra} {par : R.Grade → R.Grade → R.Grade}
    (p : IsParallel R par) (a b c : R.Grade) :
    par (R.add a b) c = R.add (par a c) (par b c) := by
  rw [p.comm (R.add a b) c, p.distribl c a b, p.comm c a, p.comm c b]

theorem IsParallel.mono_l {R : ResourceAlgebra} {par : R.Grade → R.Grade → R.Grade}
    (p : IsParallel R par) (c : R.Grade) {a b : R.Grade} (h : R.Le a b) :
    R.Le (par c a) (par c b) := by
  unfold ResourceAlgebra.Le at *
  rw [← p.distribl, h]

theorem IsParallel.mono_r {R : ResourceAlgebra} {par : R.Grade → R.Grade → R.Grade}
    (p : IsParallel R par) (c : R.Grade) {a b : R.Grade} (h : R.Le a b) :
    R.Le (par a c) (par b c) := by
  unfold ResourceAlgebra.Le at *
  rw [← p.distribr, h]

/-- Threads that meet in the middle are graded at most as threads that run
free. -/
def SyncBelow (R : ResourceAlgebra) (par : R.Grade → R.Grade → R.Grade) : Prop :=
  ∀ a b c d, R.Le (R.mul (par a b) (par c d)) (par (R.mul a c) (R.mul b d))

/-- Threads that meet in the middle are graded at least as threads that run
free. -/
def SyncAbove (R : ResourceAlgebra) (par : R.Grade → R.Grade → R.Grade) : Prop :=
  ∀ a b c d, R.Le (par (R.mul a c) (R.mul b d)) (R.mul (par a b) (par c d))

/-- P-1: a dioid with a commutative sequence is parallel with ∥ = ⊗. -/
theorem seq_parallel {R : ResourceAlgebra} (d : IsDioid R)
    (mc : ∀ a b, R.mul a b = R.mul b a) : IsParallel R R.mul where
  assoc := R.seq.assoc
  comm := mc
  unitl := R.seq.unitl
  distribl := d.distribl

theorem mul_interchange {R : ResourceAlgebra} (mc : ∀ a b, R.mul a b = R.mul b a)
    (a b c d : R.Grade) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.seq.assoc a b (R.mul c d), ← R.seq.assoc b c d, mc b c,
      R.seq.assoc c b d, ← R.seq.assoc a c (R.mul b d)]

/-- P-1: and it has both exchange laws. -/
theorem seq_sync_below {R : ResourceAlgebra} (mc : ∀ a b, R.mul a b = R.mul b a) :
    SyncBelow R R.mul := fun a b c d => by
  rw [mul_interchange mc a b c d]
  exact R.le_refl _

theorem seq_sync_above {R : ResourceAlgebra} (mc : ∀ a b, R.mul a b = R.mul b a) :
    SyncAbove R R.mul := fun a b c d => by
  rw [mul_interchange mc a b c d]
  exact R.le_refl _

/-! P-2: work. Loss and MaxPlus, parallel = sequence. -/
theorem lplus_comm (a b : LGrade) : lplus a b = lplus b a := by
  cases a <;> cases b <;> first | rfl | exact congrArg fin (Nat.add_comm _ _)

theorem Loss_parallel : IsParallel Loss lplus := seq_parallel Loss_dioid lplus_comm

theorem Loss_sync_below : SyncBelow Loss lplus := seq_sync_below (R := Loss) lplus_comm

theorem Loss_sync_above : SyncAbove Loss lplus := seq_sync_above (R := Loss) lplus_comm

theorem tMul_comm (a b : Tropical) : tMul a b = tMul b a := by
  cases a <;> cases b <;> first | rfl | exact congrArg val (Nat.add_comm _ _)

theorem MaxPlus_work : IsParallel MaxPlus tMul := seq_parallel MaxPlus_dioid tMul_comm

theorem MaxPlus_work_sync_below : SyncBelow MaxPlus tMul :=
  seq_sync_below (R := MaxPlus) tMul_comm

theorem MaxPlus_work_sync_above : SyncAbove MaxPlus tMul :=
  seq_sync_above (R := MaxPlus) tMul_comm

/-! P-3: span. MaxPlus, parallel = max on finite costs. -/
def tPar : Tropical → Tropical → Tropical
  | bot, _ => bot
  | val _, bot => bot
  | val m, val n => val (rmax m n)

theorem MaxPlus_span : IsParallel MaxPlus tPar where
  assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg val (rmax_assoc _ _ _)
  comm := by
    intro a b
    cases a <;> cases b <;> first | rfl | exact congrArg val (rmax_comm _ _)
  unitl := by intro a; cases a <;> rfl
  distribl := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg val (rmax_dup _ _ _).symm

theorem MaxPlus_span_sync_above : SyncAbove MaxPlus tPar := by
  intro a b c d
  unfold ResourceAlgebra.Le
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | rfl
    | exact congrArg val (rmax_of_le (rmax_lub
        (Nat.add_le_add (le_rmax_left _ _) (le_rmax_left _ _))
        (Nat.add_le_add (le_rmax_right _ _) (le_rmax_right _ _))))

theorem MaxPlus_span_not_sync_below : ¬ SyncBelow MaxPlus tPar := fun f =>
  absurd (val_injective (f (val 1) (val 0) (val 0) (val 1)) : (2 : Nat) = 1) (by decide)

/-! P-4: occupancy. HWM, parallel = sum of peaks and sum of drifts. -/
def parH (a b : HGrade) : HGrade :=
  ⟨a.peak + b.peak, a.drift + b.drift, Nat.add_le_add a.bounded b.bounded⟩

theorem add_interchange (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, ← Nat.add_assoc a c (b + d)]

theorem HWM_parallel : IsParallel HWM parH where
  assoc := fun _ _ _ => HGrade.ext' (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _)
  comm := fun _ _ => HGrade.ext' (Nat.add_comm _ _) (Nat.add_comm _ _)
  unitl := fun _ => HGrade.ext' (Nat.zero_add _) (Nat.zero_add _)
  distribl := fun _ _ _ => HGrade.ext' (add_rmax_l _ _ _) (add_rmax_l _ _ _)

theorem HWM_sync_below : SyncBelow HWM parH := fun a b c d => HGrade.ext'
  (show rmax (rmax (a.peak + b.peak) ((a.drift + b.drift) + (c.peak + d.peak)))
          (rmax a.peak (a.drift + c.peak) + rmax b.peak (b.drift + d.peak))
        = rmax a.peak (a.drift + c.peak) + rmax b.peak (b.drift + d.peak) from
    rmax_of_le (rmax_lub
      (Nat.add_le_add (le_rmax_left _ _) (le_rmax_left _ _))
      (Nat.le_trans (Nat.le_of_eq (add_interchange a.drift b.drift c.peak d.peak))
        (Nat.add_le_add (le_rmax_right _ _) (le_rmax_right _ _)))))
  (show rmax ((a.drift + b.drift) + (c.drift + d.drift))
          ((a.drift + c.drift) + (b.drift + d.drift))
        = (a.drift + c.drift) + (b.drift + d.drift) from
    rmax_of_le (Nat.le_of_eq (add_interchange _ _ _ _)))

theorem HWM_not_sync_above : ¬ SyncAbove HWM parH := fun f =>
  absurd (congrArg HGrade.peak
      (f ⟨1, 0, Nat.zero_le 1⟩ zeroH zeroH ⟨1, 0, Nat.zero_le 1⟩) : (2 : Nat) = 1)
    (by decide)

/-! ## The loop grade (K-1 .. K-4)

`star a` is the grade of "a, any number of times": a fixed point of
x ↦ 𝟙 ⊕ (a ⊗ x), and the least one on both sides (Kozen's axioms). -/

structure IsStar (R : ResourceAlgebra) (star : R.Grade → R.Grade) : Prop where
  unfold_eq : ∀ a, R.add R.one (R.mul a (star a)) = star a
  leastl : ∀ a b x, R.Le (R.add b (R.mul a x)) x → R.Le (R.mul (star a) b) x
  leastr : ∀ a b x, R.Le (R.add b (R.mul x a)) x → R.Le (R.mul b (star a)) x

/-- K-1: the loop grade bounds no turn and one more turn. -/
theorem IsStar.one_le {R : ResourceAlgebra} {star : R.Grade → R.Grade}
    (s : IsStar R star) (a : R.Grade) : R.Le R.one (star a) := by
  have h := R.add_upperl R.one (R.mul a (star a))
  rw [s.unfold_eq a] at h
  exact h

theorem IsStar.step {R : ResourceAlgebra} {star : R.Grade → R.Grade}
    (s : IsStar R star) (a : R.Grade) : R.Le (R.mul a (star a)) (star a) := by
  have h := R.add_upperr R.one (R.mul a (star a))
  rw [s.unfold_eq a] at h
  exact h

/-- K-1: if 𝟙 is the greatest grade, every loop grades as 𝟙. -/
theorem unit_top_star {R : ResourceAlgebra} (greatest : ∀ a, R.Le a R.one) :
    IsStar R (fun _ => R.one) where
  unfold_eq a := (R.alt.comm R.one (R.mul a R.one)).trans (greatest (R.mul a R.one))
  leastl a b x h := by
    show R.Le (R.mul R.one b) x
    rw [R.seq.unitl]
    exact R.le_trans (R.add_upperl b (R.mul a x)) h
  leastr a b x h := by
    show R.Le (R.mul b R.one) x
    rw [R.seq.unitr]
    exact R.le_trans (R.add_upperl b (R.mul x a)) h

theorem Loss_unit_top (a : LGrade) : Loss.Le a Loss.one := by
  unfold ResourceAlgebra.Le
  cases a <;> first | rfl | exact congrArg fin (rmin_zero_r _)

theorem Loss_star : IsStar Loss (fun _ => fin 0) := unit_top_star Loss_unit_top

/-- K-2: a grade whose loop equation has no solution rules a star out. -/
def NoFixpoint (R : ResourceAlgebra) (a : R.Grade) : Prop :=
  ∀ s, R.add R.one (R.mul a s) ≠ s

theorem no_star {R : ResourceAlgebra} (a : R.Grade) (nf : NoFixpoint R a)
    (star : R.Grade → R.Grade) : ¬ IsStar R star :=
  fun st => nf (star a) (st.unfold_eq a)

theorem MaxPlus_no_fixpoint : NoFixpoint MaxPlus (val 1) := fun s h => by
  cases s with
  | val n =>
      have e : 1 + n = n := val_injective h
      exact Nat.succ_ne_self n ((Nat.add_comm n 1).trans e)
  | bot =>
      have h' : val 0 = bot := h
      cases h'

theorem MaxPlus_no_star (star : Tropical → Tropical) : ¬ IsStar MaxPlus star :=
  no_star (R := MaxPlus) (val 1) MaxPlus_no_fixpoint star

theorem HWM_no_fixpoint : NoFixpoint HWM ⟨1, 1, Nat.le_refl 1⟩ := fun s h =>
  have e : 1 + s.drift = s.drift := congrArg HGrade.drift h
  Nat.succ_ne_self s.drift ((Nat.add_comm s.drift 1).trans e)

theorem HWM_no_star (star : HGrade → HGrade) : ¬ IsStar HWM star :=
  no_star (R := HWM) ⟨1, 1, Nat.le_refl 1⟩ HWM_no_fixpoint star

/-! K-3: MaxPlus with a top, (ℕ ∪ {−∞, +∞}, max, +). -/
inductive TGrade where
  | bot : TGrade
  | val : Nat → TGrade
  | top : TGrade
  deriving DecidableEq

def taddT : TGrade → TGrade → TGrade
  | .bot, y => y
  | .val m, .bot => .val m
  | .val m, .val n => .val (rmax m n)
  | .val _, .top => .top
  | .top, _ => .top

def tmulT : TGrade → TGrade → TGrade
  | .bot, _ => .bot
  | .val _, .bot => .bot
  | .val m, .val n => .val (m + n)
  | .val _, .top => .top
  | .top, .bot => .bot
  | .top, .val _ => .top
  | .top, .top => .top

abbrev MaxPlusTop : ResourceAlgebra where
  Grade := TGrade
  add := taddT
  mul := tmulT
  zero := .bot
  one := .val 0
  alt := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg TGrade.val (rmax_assoc _ _ _)
    comm := by
      intro a b
      cases a <;> cases b <;> first | rfl | exact congrArg TGrade.val (rmax_comm _ _)
    idem := by intro a; cases a <;> first | rfl | exact congrArg TGrade.val (rmax_idem _)
    unitl := by intro a; rfl }
  seq := {
    assoc := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact congrArg TGrade.val (Nat.add_assoc _ _ _)
    unitl := by
      intro a; cases a <;> first | rfl | exact congrArg TGrade.val (Nat.zero_add _)
    unitr := by intro a; cases a <;> rfl }

theorem tmulT_comm (a b : TGrade) : tmulT a b = tmulT b a := by
  cases a <;> cases b <;> first | rfl | exact congrArg TGrade.val (Nat.add_comm _ _)

theorem MaxPlusTop_dioid : IsDioid MaxPlusTop where
  distribl := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg TGrade.val (add_rmax_l _ _ _)
  distribr := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact congrArg TGrade.val (add_rmax_r _ _ _)

theorem MaxPlusTop_ordered : IsOrdered MaxPlusTop := MaxPlusTop_dioid.ordered

theorem MaxPlusTop_annihilating : IsAnnihilating MaxPlusTop where
  annihill := by intro a; rfl
  annihilr := by intro a; cases a <;> rfl

/-- K-3: MaxPlus embeds in it by a strict, injective morphism. -/
def liftT : Tropical → TGrade
  | val n => .val n
  | bot => .bot

def liftHom : Hom MaxPlus MaxPlusTop where
  map := liftT
  map_zero := rfl
  map_one := rfl
  map_add := by intro a b; cases a <;> cases b <;> rfl
  map_mul := by intro a b; cases a <;> cases b <;> rfl

theorem lift_injective : ∀ a b : Tropical, liftT a = liftT b → a = b
  | val _, val _, h => congrArg val (TGrade.val.inj h)
  | val _, bot, h => by cases h
  | bot, val _, h => by cases h
  | bot, bot, _ => rfl

/-! K-4: its star. bot and val 0 loop for nothing; a dearer body loops to
top. -/
def starT : TGrade → TGrade
  | .bot => .val 0
  | .val 0 => .val 0
  | .val (_ + 1) => .top
  | .top => .top

/-- `max (suc n + k) k` is never `k` (Agda: `max-suc-+`). -/
theorem rmax_succ_add_ne (n k : Nat) : rmax (n + 1 + k) k ≠ k := fun e =>
  have h2 : n + 1 + k ≤ k := Nat.le_trans (le_rmax_left _ _) (Nat.le_of_eq e)
  have h3 : k + 1 ≤ n + 1 + k := by
    rw [Nat.add_assoc, Nat.add_comm 1 k]
    exact Nat.le_add_left (k + 1) n
  Nat.not_succ_le_self k (Nat.le_trans h3 h2)

/-- From `b ≼ x` and `a ⊗ x ≼ x`. A body that costs something, sequenced
before a possible `x`, forces `x` to be top. -/
theorem starT_go : ∀ a b x : TGrade,
    taddT b x = x → taddT (tmulT a x) x = x → taddT (tmulT (starT a) b) x = x
  | .bot, b, x, hb, _ => by
      rw [show tmulT (starT .bot) b = b from MaxPlusTop.seq.unitl b]; exact hb
  | .val 0, b, x, hb, _ => by
      rw [show tmulT (starT (.val 0)) b = b from MaxPlusTop.seq.unitl b]; exact hb
  | .val (_ + 1), .bot, x, _, _ => by cases x <;> rfl
  | .val (_ + 1), .val _, .bot, hb, _ => by cases hb
  | .val (n + 1), .val _, .val k, _, ha =>
      absurd (TGrade.val.inj ha) (rmax_succ_add_ne n k)
  | .val (_ + 1), .val _, .top, _, _ => rfl
  | .val (_ + 1), .top, .bot, hb, _ => by cases hb
  | .val (_ + 1), .top, .val _, hb, _ => by cases hb
  | .val (_ + 1), .top, .top, _, _ => rfl
  | .top, .bot, x, _, _ => by cases x <;> rfl
  | .top, .val _, .bot, hb, _ => by cases hb
  | .top, .val _, .val _, _, ha => by cases ha
  | .top, .val _, .top, _, _ => rfl
  | .top, .top, .bot, hb, _ => by cases hb
  | .top, .top, .val _, hb, _ => by cases hb
  | .top, .top, .top, _, _ => rfl

theorem MaxPlusTop_star : IsStar MaxPlusTop starT where
  unfold_eq := by
    intro a
    cases a with
    | bot => rfl
    | top => rfl
    | val n => cases n <;> rfl
  leastl a b x h :=
    starT_go a b x
      (MaxPlusTop.le_trans (MaxPlusTop.add_upperl b (tmulT a x)) h)
      (MaxPlusTop.le_trans (MaxPlusTop.add_upperr b (tmulT a x)) h)
  leastr a b x h := by
    have h' : MaxPlusTop.Le (taddT b (tmulT a x)) x := by
      rw [tmulT_comm a x]; exact h
    have g := starT_go a b x
      (MaxPlusTop.le_trans (MaxPlusTop.add_upperl b (tmulT a x)) h')
      (MaxPlusTop.le_trans (MaxPlusTop.add_upperr b (tmulT a x)) h')
    show taddT (tmulT b (starT a)) x = x
    rw [tmulT_comm b (starT a)]
    exact g

/-! ## Signed drift (D-1 .. D-8)

The drift carrier is the integers with a bottom, `ninf`, under max and +
(Agda: Drift.agda). As in Agda, an integer is read as a difference of
naturals (`isub`, Agda `_⊖_`), and addition and max are defined on its
parts (`iup`, `idn`), so every law reduces to an equation between naturals.
Lean's `Int` supplies only its two constructors here; none of its library
lemmas is used. The bound `drift ≤ peak` is a `Prop` (`dle`), defined by
the same cases as Agda's `_≤ᵈ_`. -/

/-- A generic interchange law for alternatives, and monotonicity. -/
theorem ResourceAlgebra.alt_interchange (R : ResourceAlgebra) (a b c d : R.Grade) :
    R.add (R.add a b) (R.add c d) = R.add (R.add a c) (R.add b d) := by
  rw [R.alt.assoc a b, ← R.alt.assoc b c d, R.alt.comm b c, R.alt.assoc c b d,
      ← R.alt.assoc a c]

theorem ResourceAlgebra.alt_mono (R : ResourceAlgebra) {a a' b b' : R.Grade}
    (p : R.Le a a') (q : R.Le b b') : R.Le (R.add a b) (R.add a' b') := by
  unfold ResourceAlgebra.Le at *
  rw [R.alt_interchange, p, q]

theorem IsOrdered.mono {R : ResourceAlgebra} (o : IsOrdered R) {a a' b b' : R.Grade}
    (p : R.Le a a') (q : R.Le b b') : R.Le (R.mul a b) (R.mul a' b') :=
  R.le_trans (o.mono_r b p) (o.mono_l a' q)

theorem nat_rot (p q r s : Nat) : (p + q) + (r + s) = r + (p + (q + s)) := by
  rw [add_interchange p q r s, Nat.add_comm p r, Nat.add_assoc r p (q + s)]

theorem nat_swapr (a b c : Nat) : (a + b) + c = (a + c) + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

/-! Natural-number lemmas by recursion (core's versions bring in `propext`). -/
theorem nat_cancel_r : ∀ k {m n : Nat}, m + k = n + k → m = n
  | 0, _, _, h => h
  | k + 1, _, _, h => nat_cancel_r k (congrArg Nat.pred h)

theorem nat_cancel_l (k : Nat) {m n : Nat} (h : k + m = k + n) : m = n :=
  nat_cancel_r k ((Nat.add_comm m k).trans (h.trans (Nat.add_comm k n)))

theorem sub_succ_succ : ∀ m n, (m + 1) - (n + 1) = m - n
  | _, 0 => rfl
  | m, n + 1 => congrArg Nat.pred (sub_succ_succ m n)

theorem zero_sub' : ∀ b : Nat, 0 - b = 0
  | 0 => rfl
  | b + 1 => congrArg Nat.pred (zero_sub' b)

theorem sub_le' : ∀ a b : Nat, a - b ≤ a
  | a, 0 => Nat.le_refl a
  | a, b + 1 => Nat.le_trans (Nat.pred_le (a - b)) (sub_le' a b)

/-- `_⊖_` -/
def isub : Nat → Nat → Int
  | m, 0 => Int.ofNat m
  | 0, n + 1 => Int.negSucc n
  | m + 1, n + 1 => isub m n
termination_by structural _ n => n

def iup : Int → Nat
  | Int.ofNat n => n
  | Int.negSucc _ => 0

def idn : Int → Nat
  | Int.ofNat _ => 0
  | Int.negSucc n => n + 1

theorem isub_nf : ∀ x, isub (iup x) (idn x) = x
  | Int.ofNat _ => rfl
  | Int.negSucc _ => rfl

theorem isub_cancel : ∀ k m n, isub (k + m) (k + n) = isub m n
  | 0, m, n => by rw [Nat.zero_add, Nat.zero_add]
  | k + 1, m, n => by
      rw [Nat.succ_add, Nat.succ_add]
      exact isub_cancel k m n

/-- `⊖-≡`: differences with equal cross sums are equal. -/
theorem isub_eq (a b c d : Nat) (e : a + d = c + b) : isub a b = isub c d := by
  rw [← isub_cancel d a b, Nat.add_comm d a, e, Nat.add_comm c b, Nat.add_comm d b,
      isub_cancel b c d]

theorem isub_cross : ∀ a b, iup (isub a b) + b = idn (isub a b) + a
  | a, 0 => by show a + 0 = 0 + a; rw [Nat.add_zero, Nat.zero_add]
  | 0, n + 1 => by show 0 + (n + 1) = (n + 1) + 0; rw [Nat.zero_add, Nat.add_zero]
  | m + 1, n + 1 => congrArg (· + 1) (isub_cross m n)

theorem isub_injr (a : Nat) {b d : Nat} (e : isub a b = isub a d) : b = d :=
  nat_cancel_l _ ((isub_cross a b).trans (by rw [e]; exact (isub_cross a d).symm))

theorem isub_pos : ∀ m n, n ≤ m → isub m n = Int.ofNat (m - n)
  | _, 0, _ => rfl
  | 0, n + 1, h => absurd h (Nat.not_succ_le_zero n)
  | m + 1, n + 1, h =>
      (isub_pos m n (Nat.le_of_succ_le_succ h)).trans (congrArg Int.ofNat (sub_succ_succ m n).symm)

def iadd (x y : Int) : Int := isub (iup x + iup y) (idn x + idn y)

def imax (x y : Int) : Int := isub (rmax (iup x + idn y) (iup y + idn x)) (idn x + idn y)

theorem iadd_sub_l (a b : Nat) (y : Int) :
    iadd (isub a b) y = isub (a + iup y) (b + idn y) :=
  isub_eq _ _ _ _ (by
    rw [add_interchange (iup (isub a b)) (iup y) b (idn y), isub_cross a b,
        Nat.add_comm (idn (isub a b)) a, add_interchange a (idn (isub a b)) (iup y) (idn y)])

theorem iadd_comm (x y : Int) : iadd x y = iadd y x := by
  unfold iadd; rw [Nat.add_comm (iup x), Nat.add_comm (idn x)]

theorem iadd_sub_r (x : Int) (a b : Nat) :
    iadd x (isub a b) = isub (iup x + a) (idn x + b) := by
  rw [iadd_comm, iadd_sub_l, Nat.add_comm a, Nat.add_comm b]

theorem iadd_sub (a b c d : Nat) : iadd (isub a b) (isub c d) = isub (a + c) (b + d) := by
  rw [iadd_sub_l]
  exact isub_eq _ _ _ _ (by
    rw [add_interchange a (iup (isub c d)) b d, isub_cross c d,
        Nat.add_comm (idn (isub c d)) c, add_interchange a b c (idn (isub c d))])

theorem iadd_assoc (x y z : Int) : iadd (iadd x y) z = iadd x (iadd y z) := by
  show iadd (isub (iup x + iup y) (idn x + idn y)) z
     = iadd x (isub (iup y + iup z) (idn y + idn z))
  rw [iadd_sub_l, iadd_sub_r, Nat.add_assoc (iup x), Nat.add_assoc (idn x)]

theorem iadd_zero_l (x : Int) : iadd (Int.ofNat 0) x = x := by
  show isub (0 + iup x) (0 + idn x) = x
  rw [Nat.zero_add, Nat.zero_add]; exact isub_nf x

theorem imax_comm (x y : Int) : imax x y = imax y x := by
  unfold imax; rw [rmax_comm, Nat.add_comm (idn x)]

theorem imax_sub_l (a b : Nat) (y : Int) :
    imax (isub a b) y = isub (rmax (a + idn y) (iup y + b)) (b + idn y) :=
  isub_eq _ _ _ _ ((add_rmax_r _ _ _).trans
    ((congr (congrArg rmax e₁) (add_interchange (iup y) (idn (isub a b)) b (idn y))).trans
      (add_rmax_r _ _ _).symm))
where
  e₁ : (iup (isub a b) + idn y) + (b + idn y) = (a + idn y) + (idn (isub a b) + idn y) := by
    rw [add_interchange (iup (isub a b)) (idn y) b (idn y), isub_cross a b,
        Nat.add_comm (idn (isub a b)) a, add_interchange a (idn (isub a b)) (idn y) (idn y)]

theorem imax_sub_r (x : Int) (a b : Nat) :
    imax x (isub a b) = isub (rmax (iup x + b) (a + idn x)) (idn x + b) := by
  rw [imax_comm, imax_sub_l, rmax_comm, Nat.add_comm b]

theorem imax_sub (a b c d : Nat) :
    imax (isub a b) (isub c d) = isub (rmax (a + d) (c + b)) (b + d) :=
  (imax_sub_l a b (isub c d)).trans (isub_eq _ _ _ _ ((add_rmax_r _ _ _).trans
    ((congr (congrArg rmax f₁) f₂).trans (add_rmax_r _ _ _).symm)))
where
  f₁ : (a + idn (isub c d)) + (b + d) = (a + d) + (b + idn (isub c d)) := by
    rw [add_interchange a (idn (isub c d)) b d, Nat.add_comm (idn (isub c d)) d,
        ← add_interchange a d b (idn (isub c d))]
  f₂ : (iup (isub c d) + b) + (b + d) = (c + b) + (b + idn (isub c d)) := by
    rw [Nat.add_comm b d, add_interchange (iup (isub c d)) b d b, isub_cross c d,
        Nat.add_comm (idn (isub c d)) c, add_interchange c (idn (isub c d)) b b,
        Nat.add_comm (idn (isub c d)) b]

theorem imax_assoc (x y z : Int) : imax (imax x y) z = imax x (imax y z) := by
  show imax (isub (rmax (iup x + idn y) (iup y + idn x)) (idn x + idn y)) z
     = imax x (isub (rmax (iup y + idn z) (iup z + idn y)) (idn y + idn z))
  rw [imax_sub_l, imax_sub_r, Nat.add_assoc (idn x)]
  exact congrArg (isub · _) (by
    rw [add_rmax_r (iup x + idn y) (iup y + idn x) (idn z),
        add_rmax_r (iup y + idn z) (iup z + idn y) (idn x), rmax_assoc,
        Nat.add_assoc (iup x) (idn y) (idn z), nat_swapr (iup y) (idn x) (idn z),
        Nat.add_comm (idn x) (idn y), ← Nat.add_assoc (iup z) (idn y) (idn x)])

theorem imax_idem (x : Int) : imax x x = x := by
  show isub (rmax (iup x + idn x) (iup x + idn x)) (idn x + idn x) = x
  rw [rmax_idem]
  exact (isub_eq _ _ _ _ (Nat.add_assoc (iup x) (idn x) (idn x))).trans (isub_nf x)

theorem iadd_imax (x y z : Int) : iadd x (imax y z) = imax (iadd x y) (iadd x z) := by
  show iadd x (isub (rmax (iup y + idn z) (iup z + idn y)) (idn y + idn z))
     = imax (isub (iup x + iup y) (idn x + idn y)) (isub (iup x + iup z) (idn x + idn z))
  rw [iadd_sub_r, imax_sub,
      ← isub_cancel (idn x) (iup x + rmax (iup y + idn z) (iup z + idn y))
          (idn x + (idn y + idn z)),
      add_rmax_l (iup x), add_rmax_l (idn x),
      nat_rot (iup x) (iup y) (idn x) (idn z), nat_rot (iup x) (iup z) (idn x) (idn y),
      nat_rot (idn x) (idn y) (idn x) (idn z)]

/-! D-1: the drift carrier, the max-plus dioid on ℤ. -/
inductive Drift where
  | ninf : Drift
  | dfin : Int → Drift

open Drift

def dadd : Drift → Drift → Drift
  | ninf, _ => ninf
  | dfin _, ninf => ninf
  | dfin x, dfin y => dfin (iadd x y)

def dmax : Drift → Drift → Drift
  | ninf, e => e
  | dfin x, ninf => dfin x
  | dfin x, dfin y => dfin (imax x y)

def dzero : Drift := dfin (Int.ofNat 0)

/-- A natural as a drift, and the natural part of a drift (0 below zero). -/
def pkd (n : Nat) : Drift := dfin (Int.ofNat n)

def dclamp : Drift → Nat
  | ninf => 0
  | dfin (Int.ofNat n) => n
  | dfin (Int.negSucc _) => 0

theorem dmax_assoc : ∀ a b c, dmax (dmax a b) c = dmax a (dmax b c)
  | ninf, _, _ => rfl
  | dfin _, ninf, _ => rfl
  | dfin _, dfin _, ninf => rfl
  | dfin x, dfin y, dfin z => congrArg dfin (imax_assoc x y z)

theorem dmax_comm : ∀ a b, dmax a b = dmax b a
  | ninf, ninf => rfl
  | ninf, dfin _ => rfl
  | dfin _, ninf => rfl
  | dfin x, dfin y => congrArg dfin (imax_comm x y)

theorem dmax_idem : ∀ a, dmax a a = a
  | ninf => rfl
  | dfin x => congrArg dfin (imax_idem x)

theorem dadd_assoc : ∀ a b c, dadd (dadd a b) c = dadd a (dadd b c)
  | ninf, _, _ => rfl
  | dfin _, ninf, _ => rfl
  | dfin _, dfin _, ninf => rfl
  | dfin x, dfin y, dfin z => congrArg dfin (iadd_assoc x y z)

theorem dadd_comm : ∀ a b, dadd a b = dadd b a
  | ninf, ninf => rfl
  | ninf, dfin _ => rfl
  | dfin _, ninf => rfl
  | dfin x, dfin y => congrArg dfin (iadd_comm x y)

theorem dadd_zero_l : ∀ a, dadd dzero a = a
  | ninf => rfl
  | dfin x => congrArg dfin (iadd_zero_l x)

theorem dadd_zero_r (a : Drift) : dadd a dzero = a := (dadd_comm a dzero).trans (dadd_zero_l a)

theorem dadd_dmax_l : ∀ a b c, dadd a (dmax b c) = dmax (dadd a b) (dadd a c)
  | ninf, _, _ => rfl
  | dfin _, ninf, _ => rfl
  | dfin _, dfin _, ninf => rfl
  | dfin x, dfin y, dfin z => congrArg dfin (iadd_imax x y z)

theorem dadd_dmax_r (a b c : Drift) : dadd (dmax a b) c = dmax (dadd a c) (dadd b c) := by
  rw [dadd_comm, dadd_dmax_l, dadd_comm c a, dadd_comm c b]

abbrev Drift_RA : ResourceAlgebra where
  Grade := Drift
  add := dmax
  mul := dadd
  zero := ninf
  one := dzero
  alt := { assoc := dmax_assoc, comm := dmax_comm, idem := dmax_idem, unitl := fun _ => rfl }
  seq := { assoc := dadd_assoc, unitl := dadd_zero_l, unitr := dadd_zero_r }

theorem Drift_dioid : IsDioid Drift_RA where
  distribl := dadd_dmax_l
  distribr := dadd_dmax_r

theorem Drift_ordered : IsOrdered Drift_RA := Drift_dioid.ordered

theorem dmax_dup (p x y : Drift) : dmax (dmax p x) (dmax p y) = dmax p (dmax x y) := by
  have h := Drift_RA.alt_interchange p x p y
  exact h.trans (congrArg (dmax · (dmax x y)) (dmax_idem p))

theorem dmax_interchange (a b c d : Drift) :
    dmax (dmax a b) (dmax c d) = dmax (dmax a c) (dmax b d) :=
  Drift_RA.alt_interchange a b c d

theorem pkd_max (a b : Nat) : pkd (rmax a b) = dmax (pkd a) (pkd b) := rfl

theorem pkd_add (a b : Nat) : pkd (a + b) = dadd (pkd a) (pkd b) := rfl

theorem pkd_injective {m n : Nat} (h : pkd m = pkd n) : m = n := congrArg dclamp h

theorem pkd_clamp : ∀ (p : Nat) (y : Drift), pkd (dclamp (dmax (pkd p) y)) = dmax (pkd p) y
  | _, ninf => rfl
  | p, dfin x => by
      show pkd (dclamp (dfin (isub (rmax (p + idn x) (iup x + 0)) (0 + idn x))))
         = dfin (isub (rmax (p + idn x) (iup x + 0)) (0 + idn x))
      rw [Nat.zero_add,
          isub_pos _ _ (Nat.le_trans (Nat.le_add_left (idn x) p) (le_rmax_left _ _))]
      rfl

/-- The bound of a signed grade (Agda `_≤ᵈ_`). -/
def dle : Drift → Nat → Prop
  | ninf, _ => True
  | dfin (Int.ofNat n), p => n ≤ p
  | dfin (Int.negSucc _), _ => True

theorem dle_le : ∀ (d : Drift) (p : Nat), dle d p → dmax d (pkd p) = pkd p
  | ninf, _, _ => rfl
  | dfin (Int.ofNat n), p, b => congrArg pkd (rmax_of_le b)
  | dfin (Int.negSucc n), p, _ => by
      show dfin (isub (p + (n + 1)) (n + 1)) = dfin (isub p 0)
      exact congrArg dfin (isub_eq _ _ _ _ rfl)

theorem le_dle : ∀ (d : Drift) (p : Nat), dmax d (pkd p) = pkd p → dle d p
  | ninf, _, _ => trivial
  | dfin (Int.ofNat n), p, e =>
      Nat.le_trans (le_rmax_left n p) (Nat.le_of_eq (pkd_injective e))
  | dfin (Int.negSucc _), _, _ => trivial

theorem pkd_mono {a b : Nat} (h : a ≤ b) : Drift_RA.Le (pkd a) (pkd b) := dle_le (pkd a) b h

theorem pkd_le {a b : Nat} (e : Drift_RA.Le (pkd a) (pkd b)) : a ≤ b := le_dle (pkd a) b e

theorem ceil_le (p : Nat) (y : Drift) (q : Nat) (h : Drift_RA.Le (dmax (pkd p) y) (pkd q)) :
    dclamp (dmax (pkd p) y) ≤ q :=
  pkd_le (by rw [pkd_clamp]; exact h)

/-! D-1: the signed-drift grade. -/
structure SGrade where
  peak    : Nat
  drift   : Drift
  bounded : dle drift peak

theorem SGrade.ext' : ∀ {a b : SGrade}, a.peak = b.peak → a.drift = b.drift → a = b
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

/-- `max (pk p) y`, read as a natural (Agda `⌈ p , y ⌉`). -/
def ceil (p : Nat) (y : Drift) : Nat := dclamp (dmax (pkd p) y)

def mulS (a b : SGrade) : SGrade :=
  ⟨ceil a.peak (dadd a.drift (pkd b.peak)), dadd a.drift b.drift,
   le_dle _ _ (by
     unfold ceil; rw [pkd_clamp]
     exact Drift_RA.le_trans (Drift_ordered.mono_l a.drift (dle_le _ _ b.bounded))
       (Drift_RA.add_upperr (pkd a.peak) (dadd a.drift (pkd b.peak))))⟩

def addS (a b : SGrade) : SGrade :=
  ⟨rmax a.peak b.peak, dmax a.drift b.drift,
   le_dle _ _ (by
     rw [pkd_max]
     exact Drift_RA.alt_mono (dle_le _ _ a.bounded) (dle_le _ _ b.bounded))⟩

def zeroS : SGrade := ⟨0, ninf, trivial⟩
def oneS : SGrade := ⟨0, dzero, Nat.le_refl 0⟩

theorem seq_flat (p : Nat) (n : Drift) (b : dle n p) : ceil p (dadd n dzero) = p := by
  unfold ceil; rw [dadd_zero_r, dmax_comm, dle_le n p b]; rfl

abbrev SHWM : ResourceAlgebra where
  Grade := SGrade
  add := addS
  mul := mulS
  zero := zeroS
  one := oneS
  alt := {
    assoc := fun _ _ _ => SGrade.ext' (rmax_assoc _ _ _) (dmax_assoc _ _ _)
    comm := fun _ _ => SGrade.ext' (rmax_comm _ _) (dmax_comm _ _)
    idem := fun _ => SGrade.ext' (rmax_idem _) (dmax_idem _)
    unitl := fun _ => SGrade.ext' rfl rfl }
  seq := {
    assoc := fun a b c => SGrade.ext'
      (show ceil (ceil a.peak (dadd a.drift (pkd b.peak))) (dadd (dadd a.drift b.drift) (pkd c.peak))
          = ceil a.peak (dadd a.drift (pkd (ceil b.peak (dadd b.drift (pkd c.peak))))) by
        unfold ceil
        rw [pkd_clamp, pkd_clamp, dmax_assoc, dadd_assoc, dadd_dmax_l])
      (dadd_assoc _ _ _)
    unitl := fun a => SGrade.ext'
      (show ceil 0 (dadd dzero (pkd a.peak)) = a.peak from Nat.zero_add a.peak)
      (dadd_zero_l _)
    unitr := fun a => SGrade.ext' (seq_flat a.peak a.drift a.bounded) (dadd_zero_r _) }

theorem SHWM_dioid : IsDioid SHWM where
  distribl := fun a b c => SGrade.ext'
    (show ceil a.peak (dadd a.drift (pkd (rmax b.peak c.peak)))
        = rmax (ceil a.peak (dadd a.drift (pkd b.peak))) (ceil a.peak (dadd a.drift (pkd c.peak))) by
      apply pkd_injective
      unfold ceil
      rw [pkd_max b.peak c.peak, pkd_clamp, pkd_max, pkd_clamp, pkd_clamp, dadd_dmax_l, dmax_dup])
    (dadd_dmax_l _ _ _)
  distribr := fun a b c => SGrade.ext'
    (show ceil (rmax a.peak b.peak) (dadd (dmax a.drift b.drift) (pkd c.peak))
        = rmax (ceil a.peak (dadd a.drift (pkd c.peak))) (ceil b.peak (dadd b.drift (pkd c.peak))) by
      apply pkd_injective
      unfold ceil
      rw [pkd_clamp, pkd_max a.peak b.peak, pkd_max, pkd_clamp, pkd_clamp, dadd_dmax_r,
          dmax_interchange])
    (dadd_dmax_r _ _ _)

theorem SHWM_ordered : IsOrdered SHWM := SHWM_dioid.ordered

/-- D-2: 𝟘 is not 𝟙. -/
theorem SHWM_zero_ne_one : SHWM.zero ≠ SHWM.one := fun h =>
  Drift.noConfusion (congrArg SGrade.drift h : ninf = dzero)

/-- D-2: 𝟘 absorbs on the left. -/
theorem SHWM_absorbl (a : SGrade) : mulS zeroS a = zeroS := SGrade.ext' rfl rfl

/-- D-2: on the right it keeps the peak of what ran first. -/
theorem SHWM_seq_zero : ∀ a : SGrade, mulS a zeroS = ⟨a.peak, ninf, trivial⟩
  | ⟨_, ninf, _⟩ => SGrade.ext' rfl rfl
  | ⟨p, dfin x, b⟩ => SGrade.ext' (seq_flat p (dfin x) b) rfl

theorem SHWM_not_annihilating : ¬ IsAnnihilating SHWM := fun z =>
  absurd (congrArg SGrade.peak (z.annihilr ⟨1, dzero, Nat.zero_le 1⟩) : (1 : Nat) = 0)
    (by decide)

/-- D-4: in HWM a prefix keeps the peak. -/
theorem HWM_prefix_keeps_peak (a b : HGrade) : b.peak ≤ (mulH a b).peak :=
  Nat.le_trans (Nat.le_add_left b.peak a.drift) (le_rmax_right _ _)

def freeOne : SGrade := ⟨0, dfin (Int.negSucc 0), trivial⟩
def allocOne : SGrade := ⟨1, pkd 1, Nat.le_refl 1⟩

/-- D-4: with consumption a prefix can lower the peak. -/
theorem prefix_lowers_peak : ¬ ∀ a b : SGrade, b.peak ≤ (mulS a b).peak := fun f =>
  absurd (f freeOne allocOne) (by decide)

/-! D-3: HWM inside SHWM, and back. -/
def embed (a : HGrade) : SGrade := ⟨a.peak, pkd a.drift, a.bounded⟩

def clampG (a : SGrade) : HGrade :=
  ⟨a.peak, ceil 0 a.drift,
   ceil_le 0 a.drift a.peak
     (Drift_RA.add_least (pkd_mono (Nat.zero_le a.peak)) (dle_le _ _ a.bounded))⟩

theorem embed_mul (a b : HGrade) : embed (mulH a b) = mulS (embed a) (embed b) :=
  SGrade.ext' rfl rfl

theorem embed_add (a b : HGrade) : embed (addH a b) = addS (embed a) (embed b) :=
  SGrade.ext' rfl rfl

def embedLax : LaxHom HWM SHWM where
  map := embed
  map_one := SGrade.ext' rfl rfl
  map_add := embed_add
  map_mul a b := by
    show SHWM.Le (embed (mulH a b)) (mulS (embed a) (embed b))
    rw [embed_mul]; exact SHWM.le_refl _

theorem embed_injective {a b : HGrade} (e : embed a = embed b) : a = b :=
  HGrade.ext' (congrArg SGrade.peak e) (pkd_injective (congrArg SGrade.drift e))

theorem embed_zero : embed zeroH ≠ zeroS := fun h =>
  Drift.noConfusion (congrArg SGrade.drift h : pkd 0 = ninf)

theorem no_strict_HWM_SHWM (h : Hom HWM SHWM) : False :=
  no_strict_from_HWM SHWM SHWM_zero_ne_one h

theorem clamp_embed (a : HGrade) : clampG (embed a) = a := HGrade.ext' rfl rfl

def clampLax : LaxHom SHWM HWM where
  map := clampG
  map_one := HGrade.ext' rfl rfl
  map_add a b := HGrade.ext' rfl (by
    show ceil 0 (dmax a.drift b.drift) = rmax (ceil 0 a.drift) (ceil 0 b.drift)
    apply pkd_injective
    unfold ceil
    rw [pkd_max, pkd_clamp, pkd_clamp, pkd_clamp, dmax_dup])
  map_mul a b := HGrade.ext'
    (rmax_of_le (ceil_le _ _ _ (by
      show dmax (dmax (pkd a.peak) (dadd a.drift (pkd b.peak))) (pkd (rmax a.peak (ceil 0 a.drift + b.peak)))
         = pkd (rmax a.peak (ceil 0 a.drift + b.peak))
      rw [pkd_max a.peak, pkd_add, ceil, pkd_clamp]
      exact Drift_RA.alt_mono (Drift_RA.le_refl (pkd a.peak))
        (Drift_ordered.mono_r (pkd b.peak) (Drift_RA.add_upperr (pkd 0) a.drift)))))
    (rmax_of_le (ceil_le _ _ _ (by
      show dmax (dmax (pkd 0) (dadd a.drift b.drift)) (pkd (ceil 0 a.drift + ceil 0 b.drift))
         = pkd (ceil 0 a.drift + ceil 0 b.drift)
      rw [pkd_add, ceil, ceil, pkd_clamp, pkd_clamp]
      exact Drift_RA.add_least
        (Drift_ordered.mono (Drift_RA.add_upperl (pkd 0) a.drift)
          (Drift_RA.add_upperl (pkd 0) b.drift))
        (Drift_ordered.mono (Drift_RA.add_upperr (pkd 0) a.drift)
          (Drift_RA.add_upperr (pkd 0) b.drift)))))

theorem clamp_not_strict :
    ¬ ∀ a b : SGrade, clampG (mulS a b) = mulH (clampG a) (clampG b) := fun f =>
  absurd (congrArg HGrade.peak (f freeOne allocOne) : (0 : Nat) = 1) (by decide)

/-- D-7: the peak is lax into MaxPlus, and agrees with HWM's on HWM. -/
def speakLax : LaxHom SHWM MaxPlus where
  map g := val g.peak
  map_one := rfl
  map_add _ _ := rfl
  map_mul a b := congrArg val (rmax_of_le (ceil_le _ _ _
    (Drift_RA.add_least (pkd_mono (Nat.le_add_right a.peak b.peak))
      (Drift_ordered.mono_r (pkd b.peak) (dle_le _ _ a.bounded)))))

theorem speak_embed (a : HGrade) : (embed a).peak = a.peak := rfl

/-! D-5: parallel = sum of peaks and sum of drifts. -/
def parS (a b : SGrade) : SGrade :=
  ⟨a.peak + b.peak, dadd a.drift b.drift,
   le_dle _ _ (Drift_ordered.mono (dle_le _ _ a.bounded) (dle_le _ _ b.bounded))⟩

theorem SHWM_parallel : IsParallel SHWM parS where
  assoc := fun _ _ _ => SGrade.ext' (Nat.add_assoc _ _ _) (dadd_assoc _ _ _)
  comm := fun _ _ => SGrade.ext' (Nat.add_comm _ _) (dadd_comm _ _)
  unitl := fun _ => SGrade.ext' (Nat.zero_add _) (dadd_zero_l _)
  distribl := fun _ _ _ => SGrade.ext' (add_rmax_l _ _ _) (dadd_dmax_l _ _ _)

theorem dadd_interchange (a b c d : Drift) :
    dadd (dadd a b) (dadd c d) = dadd (dadd a c) (dadd b d) := by
  rw [dadd_assoc a b, ← dadd_assoc b c d, dadd_comm b c, dadd_assoc c b d, ← dadd_assoc a c]

theorem SHWM_sync_below : SyncBelow SHWM parS := fun a b c d => SGrade.ext'
  (rmax_of_le (ceil_le _ _ _ (by
    show Drift_RA.Le
      (dmax (pkd (a.peak + b.peak)) (dadd (dadd a.drift b.drift) (pkd (c.peak + d.peak))))
      (pkd (ceil a.peak (dadd a.drift (pkd c.peak)) + ceil b.peak (dadd b.drift (pkd d.peak))))
    rw [pkd_add (ceil _ _), ceil, ceil, pkd_clamp, pkd_clamp, pkd_add, pkd_add,
        dadd_interchange a.drift b.drift]
    exact Drift_RA.add_least
      (Drift_ordered.mono (Drift_RA.add_upperl (pkd a.peak) (dadd a.drift (pkd c.peak)))
        (Drift_RA.add_upperl (pkd b.peak) (dadd b.drift (pkd d.peak))))
      (Drift_ordered.mono (Drift_RA.add_upperr (pkd a.peak) (dadd a.drift (pkd c.peak)))
        (Drift_RA.add_upperr (pkd b.peak) (dadd b.drift (pkd d.peak)))))))
  (show dmax (dadd (dadd a.drift b.drift) (dadd c.drift d.drift))
          (dadd (dadd a.drift c.drift) (dadd b.drift d.drift))
        = dadd (dadd a.drift c.drift) (dadd b.drift d.drift) by
    rw [dadd_interchange a.drift b.drift, dmax_idem])

theorem SHWM_not_sync_above : ¬ SyncAbove SHWM parS := fun f =>
  absurd (congrArg SGrade.peak
      (f ⟨1, dzero, Nat.zero_le 1⟩ oneS oneS ⟨1, dzero, Nat.zero_le 1⟩) : (2 : Nat) = 1)
    (by decide)

/-! D-6: no star. -/
theorem SHWM_no_fixpoint : NoFixpoint SHWM ⟨1, pkd 1, Nat.le_refl 1⟩ := fun s h =>
  have e : rmax 1 (1 + s.peak) = s.peak := congrArg SGrade.peak h
  Nat.succ_ne_self s.peak (by rw [Nat.add_comm] at e; exact e)

theorem SHWM_no_star (star : SGrade → SGrade) : ¬ IsStar SHWM star :=
  no_star (R := SHWM) ⟨1, pkd 1, Nat.le_refl 1⟩ SHWM_no_fixpoint star

/-! D-8: the bicyclic monoid. -/
structure Bicyclic where
  rise : Nat
  fall : Nat

def bmul (x y : Bicyclic) : Bicyclic :=
  ⟨x.rise + (y.rise - x.fall), y.fall + (x.fall - y.rise)⟩

theorem dle_succ : ∀ (d : Drift) (p : Nat), dle d p → dle d (p + 1)
  | ninf, _, _ => trivial
  | dfin (Int.ofNat _), _, b => Nat.le_succ_of_le b
  | dfin (Int.negSucc _), _, _ => trivial

theorem isub_dle : ∀ a b, dle (dfin (isub a b)) a
  | a, 0 => Nat.le_refl a
  | 0, _ + 1 => trivial
  | a + 1, b + 1 => dle_succ _ _ (isub_dle a b)

/-- `max b c = (c ∸ b) + b` -/
theorem max_monus : ∀ b c, rmax b c = (c - b) + b
  | 0, _ => rfl
  | b + 1, 0 => by rw [zero_sub', Nat.zero_add]; rfl
  | b + 1, c + 1 => by
      show rmax b c + 1 = (c + 1 - (b + 1)) + (b + 1)
      rw [sub_succ_succ, max_monus b c]; rfl

theorem sub_add_cancel' {n p : Nat} (h : n ≤ p) : (p - n) + n = p :=
  (max_monus n p).symm.trans (rmax_of_le h)

def bic (x : Bicyclic) : SGrade := ⟨x.rise, dfin (isub x.rise x.fall), isub_dle x.rise x.fall⟩

theorem bic_one : bic ⟨0, 0⟩ = oneS := SGrade.ext' rfl rfl

theorem bic_mul (x y : Bicyclic) : bic (bmul x y) = mulS (bic x) (bic y) := by
  cases x with
  | mk a b => cases y with
    | mk c d =>
      apply SGrade.ext'
      · show a + (c - b) = dclamp (dmax (pkd a) (dfin (iadd (isub a b) (Int.ofNat c))))
        apply pkd_injective
        rw [pkd_clamp]
        show dfin (Int.ofNat (a + (c - b))) = dfin (imax (Int.ofNat a) (iadd (isub a b) (Int.ofNat c)))
        rw [iadd_sub_l, imax_sub_r]
        show dfin (isub (a + (c - b)) 0) = dfin (isub (rmax (a + (b + 0)) (a + c + 0)) (0 + (b + 0)))
        rw [Nat.zero_add]
        apply congrArg dfin
        apply isub_eq
        show a + (c - b) + b = rmax (a + b) (a + c)
        rw [← add_rmax_l, max_monus b c, Nat.add_assoc]
      · show dfin (isub (a + (c - b)) (d + (b - c))) = dfin (iadd (isub a b) (isub c d))
        rw [iadd_sub]
        apply congrArg dfin
        apply isub_eq
        show a + (c - b) + (b + d) = a + c + (d + (b - c))
        have h₁ : (c - b) + b = rmax b c := (max_monus b c).symm
        have h₂ : c + (b - c) = rmax b c := by
          rw [Nat.add_comm, ← max_monus c b, rmax_comm]
        rw [← Nat.add_assoc, Nat.add_assoc a (c - b) b, h₁, Nat.add_comm d (b - c),
            ← Nat.add_assoc (a + c), Nat.add_assoc a c (b - c), h₂, Nat.add_assoc]

theorem bic_injective {x y : Bicyclic} (e : bic x = bic y) : x = y := by
  cases x with
  | mk a b => cases y with
    | mk c d =>
      have h₁ : a = c := congrArg SGrade.peak e
      subst h₁
      have h₂ : dfin (isub a b) = dfin (isub a d) := congrArg SGrade.drift e
      have h₃ : b = d := isub_injr a (congrArg (fun | dfin z => z | ninf => Int.ofNat 0) h₂)
      subst h₃
      rfl

def Finite (g : SGrade) : Prop :=
  match g.drift with
  | ninf => False
  | dfin _ => True

def bic_onto : ∀ g : SGrade, Finite g → { x : Bicyclic // bic x = g }
  | ⟨_, ninf, _⟩, h => absurd h id
  | ⟨p, dfin (Int.ofNat n), b⟩, _ => ⟨⟨p, p - n⟩, SGrade.ext' rfl (congrArg dfin
      (isub_eq _ _ _ _ ((Nat.add_zero p).trans
        ((sub_add_cancel' b).symm.trans (Nat.add_comm (p - n) n)))))⟩
  | ⟨p, dfin (Int.negSucc n), _⟩, _ => ⟨⟨p, p + (n + 1)⟩, SGrade.ext' rfl (congrArg dfin
      ((congrArg (isub · (p + (n + 1))) (Nat.add_zero p).symm).trans (isub_cancel p 0 (n + 1))))⟩

theorem bic_HWM (a : HGrade) : bic ⟨a.peak, a.peak - a.drift⟩ = embed a :=
  SGrade.ext' rfl (congrArg dfin
    (isub_eq _ _ _ _ ((Nat.add_zero a.peak).trans
      ((sub_add_cancel' a.bounded).symm.trans (Nat.add_comm (a.peak - a.drift) a.drift)))))

def HWM_bic (a b : Nat) (q : b ≤ a) : { h : HGrade // embed h = bic ⟨a, b⟩ } :=
  ⟨⟨a, a - b, sub_le' a b⟩, SGrade.ext' rfl (congrArg dfin (isub_pos a b q).symm)⟩

end RA

/-! ## Axioms (PROOF-POLICY §8.4)

Each line below must read "does not depend on any axioms"; CI fails on any
other answer. -/
#print axioms RA.IsAltMonoid.unitr
#print axioms RA.ResourceAlgebra.le_refl
#print axioms RA.ResourceAlgebra.le_trans
#print axioms RA.ResourceAlgebra.le_antisym
#print axioms RA.ResourceAlgebra.zero_least
#print axioms RA.ResourceAlgebra.add_upperl
#print axioms RA.ResourceAlgebra.add_upperr
#print axioms RA.ResourceAlgebra.add_least
#print axioms RA.IsDioid.ordered
#print axioms RA.dioid_not_annihilating
#print axioms RA.Diamond
#print axioms RA.Diamond_ordered
#print axioms RA.Diamond_annihilating
#print axioms RA.Diamond_not_dioid
#print axioms RA.ordered_annihilating_not_dioid
#print axioms RA.Loss
#print axioms RA.Loss_dioid
#print axioms RA.Loss_annihilating
#print axioms RA.MaxPlus
#print axioms RA.MaxPlus_dioid
#print axioms RA.MaxPlus_annihilating
#print axioms RA.HWM
#print axioms RA.HWM_dioid
#print axioms RA.HWM_not_annihilating
#print axioms RA.MinMax
#print axioms RA.MinMax_dioid
#print axioms RA.MinMax_annihilating
#print axioms RA.lax
#print axioms RA.idHom
#print axioms RA.Hom.comp
#print axioms RA.idLax
#print axioms RA.LaxHom.comp
#print axioms RA.peakLax
#print axioms RA.peak_not_strict
#print axioms RA.no_strict_HWM_MaxPlus
#print axioms RA.no_strict_HWM_Loss
#print axioms RA.zeroTestHom
#print axioms RA.supportHom
#print axioms RA.maps_disagree_at_positive
#print axioms RA.Loss_to_MaxPlus
#print axioms RA.no_injective_Loss_to_MaxPlus
#print axioms RA.support'Hom
#print axioms RA.MaxPlus_to_Loss
#print axioms RA.lossBottleneck
#print axioms RA.occupancy_is_not_cost
#print axioms RA.alternatives_differ
#print axioms RA.maxplus_order
#print axioms RA.loss_order_reversed
#print axioms RA.bottleneck_is_not_sum
#print axioms RA.Questions
#print axioms RA.Questions_dioid
#print axioms RA.Questions_annihilating
#print axioms RA.same_amount_different_loss
#print axioms RA.both_lost
#print axioms RA.no_branch_achieves_meet
#print axioms RA.oneQuestionHom
#print axioms RA.one_question_needs
#print axioms RA.one_question_unique
#print axioms RA.firstQuestion
#print axioms RA.laterQuestions
#print axioms RA.count_not_add
#print axioms RA.Evidence
#print axioms RA.Evidence_dioid
#print axioms RA.Evidence_ordered
#print axioms RA.Evidence_annihilating
#print axioms RA.le_to_rank
#print axioms RA.rank_to_le
#print axioms RA.le_proven
#print axioms RA.eMeet_lowerl
#print axioms RA.eMeet_lowerr
#print axioms RA.eMeet_greatest
#print axioms RA.eff_le_own
#print axioms RA.eff_le_dep
#print axioms RA.eff_le_reach
#print axioms RA.eff_respects
#print axioms RA.restrict
#print axioms RA.eff_greatest
#print axioms RA.sequence_keeps_the_weaker
#print axioms RA.alternative_keeps_the_stronger
#print axioms RA.provenWithPostulates_below_proven
#print axioms RA.open_annihilates
#print axioms RA.row2_is_argued
#print axioms RA.row4_is_tested_only
#print axioms RA.row0_keeps_its_evidence
#print axioms RA.IsParallel.unitr
#print axioms RA.IsParallel.distribr
#print axioms RA.IsParallel.mono_l
#print axioms RA.IsParallel.mono_r
#print axioms RA.seq_parallel
#print axioms RA.seq_sync_below
#print axioms RA.seq_sync_above
#print axioms RA.Loss_parallel
#print axioms RA.Loss_sync_below
#print axioms RA.Loss_sync_above
#print axioms RA.MaxPlus_work
#print axioms RA.MaxPlus_work_sync_below
#print axioms RA.MaxPlus_work_sync_above
#print axioms RA.MaxPlus_span
#print axioms RA.MaxPlus_span_sync_above
#print axioms RA.MaxPlus_span_not_sync_below
#print axioms RA.HWM_parallel
#print axioms RA.HWM_sync_below
#print axioms RA.HWM_not_sync_above
#print axioms RA.IsStar.one_le
#print axioms RA.IsStar.step
#print axioms RA.unit_top_star
#print axioms RA.Loss_star
#print axioms RA.no_star
#print axioms RA.MaxPlus_no_star
#print axioms RA.HWM_no_star
#print axioms RA.MaxPlusTop
#print axioms RA.MaxPlusTop_dioid
#print axioms RA.MaxPlusTop_annihilating
#print axioms RA.liftHom
#print axioms RA.lift_injective
#print axioms RA.MaxPlusTop_star
#print axioms RA.Drift_dioid
#print axioms RA.SHWM
#print axioms RA.SHWM_dioid
#print axioms RA.SHWM_ordered
#print axioms RA.SHWM_zero_ne_one
#print axioms RA.SHWM_absorbl
#print axioms RA.SHWM_seq_zero
#print axioms RA.SHWM_not_annihilating
#print axioms RA.HWM_prefix_keeps_peak
#print axioms RA.prefix_lowers_peak
#print axioms RA.embedLax
#print axioms RA.embed_mul
#print axioms RA.embed_injective
#print axioms RA.embed_zero
#print axioms RA.no_strict_HWM_SHWM
#print axioms RA.clampLax
#print axioms RA.clamp_embed
#print axioms RA.clamp_not_strict
#print axioms RA.speakLax
#print axioms RA.speak_embed
#print axioms RA.SHWM_parallel
#print axioms RA.SHWM_sync_below
#print axioms RA.SHWM_not_sync_above
#print axioms RA.SHWM_no_fixpoint
#print axioms RA.SHWM_no_star
#print axioms RA.bic_one
#print axioms RA.bic_mul
#print axioms RA.bic_injective
#print axioms RA.bic_onto
#print axioms RA.bic_HWM
#print axioms RA.HWM_bic
