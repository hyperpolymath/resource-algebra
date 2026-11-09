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
#print axioms RA.IsDioid.ordered
#print axioms RA.dioid_not_annihilating
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
