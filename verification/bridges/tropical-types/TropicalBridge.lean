-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import ResourceAlgebra
import TropicalSessionTypes

/-!
# M-2: MaxPlus agrees with tropical-types' Tropical semiring

The bridge between this repository's `MaxPlus` (M-1) and the
`instance : CommSemiring Tropical` of `hyperpolymath/tropical-types`
(`TropicalSessionTypes.lean`, namespace `Hyperpolymath.Tropical`), read at the
commit `scripts/check-lean-bridge.sh` pins.

tropical-types builds that instance from four operations:
`add := tAdd`, `mul := tMul`, `zero := .bot`, `one := .val 0`. The bridge is
an isomorphism of carriers that carries ⊕, ⊗, 𝟘 and 𝟙 of `MaxPlus` to exactly
those four. The examples at the end confirm, by `rfl`, that the instance's
`+`, `*`, `0` and `1` are those operations.

The theorems depend on tropical-types' definitions of `Tropical`, `tAdd` and
`tMul` only, which use no axiom. They do not use tropical-types' proofs of the
semiring laws (those use `propext` and `Quot.sound`): both sides prove their
own laws, and the isomorphism carries one set to the other.

The only arithmetic difference is `max`: this repository's `rmax` is Agda's
three-equation recursion, tropical-types uses core `Nat.max`. `rmax_eq_max`
proves them equal.
-/
namespace RA.TropicalBridge

open Hyperpolymath.Tropical (CommSemiring)

abbrev HT := Hyperpolymath.Tropical.Tropical

theorem rmax_eq_max : ∀ m n : Nat, RA.rmax m n = Nat.max m n
  | 0, n => (ite_eq_left (Nat.zero_le n)).symm
  | m + 1, 0 => (ite_eq_right (Nat.not_succ_le_zero m)).symm
  | m + 1, n + 1 => by
    show RA.rmax m n + 1 = (if m + 1 ≤ n + 1 then n + 1 else m + 1)
    rw [rmax_eq_max m n]
    show (if m ≤ n then n else m) + 1 = (if m + 1 ≤ n + 1 then n + 1 else m + 1)
    match Nat.decLe m n with
    | isTrue h => rw [ite_eq_left h, ite_eq_left (Nat.succ_le_succ h)]
    | isFalse h => rw [ite_eq_right h, ite_eq_right (fun h' => h (Nat.le_of_succ_le_succ h'))]

/-- The carrier map, MaxPlus → tropical-types. -/
def toHT : RA.Tropical → HT
  | .val n => .val n
  | .bot => .bot

/-- Its inverse. -/
def ofHT : HT → RA.Tropical
  | .val n => .val n
  | .bot => .bot

theorem ofHT_toHT : ∀ x, ofHT (toHT x) = x
  | .val _ => rfl
  | .bot => rfl

theorem toHT_ofHT : ∀ y, toHT (ofHT y) = y
  | .val _ => rfl
  | .bot => rfl

theorem toHT_add : ∀ x y, toHT (RA.MaxPlus.add x y)
    = Hyperpolymath.Tropical.tAdd (toHT x) (toHT y)
  | .bot, .bot => rfl
  | .bot, .val _ => rfl
  | .val _, .bot => rfl
  | .val m, .val n => congrArg Hyperpolymath.Tropical.Tropical.val (rmax_eq_max m n)

theorem toHT_mul : ∀ x y, toHT (RA.MaxPlus.mul x y)
    = Hyperpolymath.Tropical.tMul (toHT x) (toHT y)
  | .bot, .bot => rfl
  | .bot, .val _ => rfl
  | .val _, .bot => rfl
  | .val _, .val _ => rfl

theorem toHT_zero : toHT RA.MaxPlus.zero = .bot := rfl

theorem toHT_one : toHT RA.MaxPlus.one = .val 0 := rfl

/-- M-2: `MaxPlus` and tropical-types' `Tropical` are isomorphic as
semirings. The isomorphism carries ⊕, ⊗, 𝟘 and 𝟙 to `tAdd`, `tMul`, `bot`
and `val 0`, the operations of `instance : CommSemiring Tropical`. -/
theorem maxplus_agrees_tropical :
    (∀ x, ofHT (toHT x) = x) ∧ (∀ y, toHT (ofHT y) = y) ∧
    (∀ x y, toHT (RA.MaxPlus.add x y) = Hyperpolymath.Tropical.tAdd (toHT x) (toHT y)) ∧
    (∀ x y, toHT (RA.MaxPlus.mul x y) = Hyperpolymath.Tropical.tMul (toHT x) (toHT y)) ∧
    toHT RA.MaxPlus.zero = .bot ∧ toHT RA.MaxPlus.one = .val 0 :=
  ⟨ofHT_toHT, toHT_ofHT, toHT_add, toHT_mul, toHT_zero, toHT_one⟩

/-! The instance's operations are the four the bridge targets. These refer to
the instance itself, whose law fields carry tropical-types' axioms, so they
are checked here but are not in the axiom-free count. -/
example : ∀ x y : HT, x + y = Hyperpolymath.Tropical.tAdd x y := fun _ _ => rfl
example : ∀ x y : HT, x * y = Hyperpolymath.Tropical.tMul x y := fun _ _ => rfl
example : (0 : HT) = .bot := rfl
example : (1 : HT) = .val 0 := rfl

end RA.TropicalBridge

/-! ## Axioms (PROOF-POLICY §8.4)

Each line below must read "does not depend on any axioms"; CI fails on any
other answer. -/
#print axioms RA.TropicalBridge.rmax_eq_max
#print axioms RA.TropicalBridge.ofHT_toHT
#print axioms RA.TropicalBridge.toHT_ofHT
#print axioms RA.TropicalBridge.toHT_add
#print axioms RA.TropicalBridge.toHT_mul
#print axioms RA.TropicalBridge.maxplus_agrees_tropical
