(* SPDX-License-Identifier: MPL-2.0
   SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

   Rocq recheck leg of the Agda theorems in src/ResourceAlgebra (standards
   PROOF-POLICY §2). The route and the reason for it are recorded per theorem
   in docs/status/PROOF-STATUS.adoc. The statement correspondence notes that
   hold throughout:

   - Agda's `≡` lives in `Set` (checked `--without-K`); Rocq's `=` lives in
     `Prop`. Every statement here is an equation, an order fact or a
     negation, so this changes no statement's strength.
   - The law records (`IsAltMonoid`, `IsDioid`, ...) are `Prop` records here
     and `Set` records in Agda, with the same fields.
   - `max`/`min` are defined by Agda's recursion (`rmax`, `rmin`); their
     agreement with `Nat.max`/`Nat.min` is proved (`rmax_eq`, `rmin_eq`)
     before any lemma uses `lia`.
   - HWM's bound is the standard library's `le` (Agda: its own `_≤_`). Both
     are the usual order on nat. Equality of HWM grades uses proof
     irrelevance of `le`, which the standard library proves (`Peano_dec.le_unique`)
     rather than assumes. *)

From Stdlib Require Import Arith Lia.

Set Implicit Arguments.


(** * Prelude: max and min by Agda's recursion *)

Fixpoint rmax (m n : nat) : nat :=
  match m, n with
  | 0, n => n
  | S m, 0 => S m
  | S m, S n => S (rmax m n)
  end.

Fixpoint rmin (m n : nat) : nat :=
  match m, n with
  | 0, _ => 0
  | S _, 0 => 0
  | S m, S n => S (rmin m n)
  end.

Lemma rmax_eq : forall m n, rmax m n = Nat.max m n.
Proof. induction m; destruct n; simpl; auto. Qed.

Lemma rmin_eq : forall m n, rmin m n = Nat.min m n.
Proof. induction m; destruct n; simpl; auto. Qed.

(** Replace every [rmax]/[rmin] in the goal by [Nat.max]/[Nat.min], one
    explicit instance at a time, so that [lia] can close what remains. *)
Ltac unfold_rmm :=
  repeat match goal with
         | |- context [rmin ?x ?y] => rewrite (rmin_eq x y)
         | |- context [rmax ?x ?y] => rewrite (rmax_eq x y)
         end.

(** * Core (C-1 .. C-3) *)

Record IsAltMonoid {G : Type} (op : G -> G -> G) (e : G) : Prop := {
  alt_assoc : forall a b c, op (op a b) c = op a (op b c);
  alt_comm  : forall a b, op a b = op b a;
  alt_idem  : forall a, op a a = a;
  alt_unitl : forall a, op e a = a
}.

(** C-1: the derived right unit. *)
Lemma alt_unitr {G} {op : G -> G -> G} {e} (m : IsAltMonoid op e) :
  forall a, op a e = a.
Proof. intro a. rewrite (alt_comm m). apply (alt_unitl m). Qed.

Record IsSeqMonoid {G : Type} (op : G -> G -> G) (e : G) : Prop := {
  seq_assoc : forall a b c, op (op a b) c = op a (op b c);
  seq_unitl : forall a, op e a = a;
  seq_unitr : forall a, op a e = a
}.

(** C-1: alternatives form an idempotent commutative monoid, sequence a monoid. *)
Record ResourceAlgebra : Type := {
  Grade : Type;
  radd  : Grade -> Grade -> Grade;   (* ⊕, alternatives *)
  rmul  : Grade -> Grade -> Grade;   (* ⊗, sequence *)
  rzero : Grade;                     (* 𝟘 *)
  rone  : Grade;                     (* 𝟙 *)
  ralt  : IsAltMonoid radd rzero;
  rseq  : IsSeqMonoid rmul rone
}.

(** The induced order: [a ≼ b] when [b] absorbs [a]. *)
Definition Le (R : ResourceAlgebra) (a b : Grade R) : Prop := radd R a b = b.

(** C-2: [≼] is a partial order, [𝟘] is least and [⊕] is its join. *)
Section Order.
  Variable R : ResourceAlgebra.

  Lemma le_refl : forall a, Le R a a.
  Proof. apply (alt_idem (ralt R)). Qed.

  Lemma le_trans : forall a b c, Le R a b -> Le R b c -> Le R a c.
  Proof.
    unfold Le; intros a b c p q.
    rewrite <- q at 1. rewrite <- (alt_assoc (ralt R)), p. exact q.
  Qed.

  Lemma le_antisym : forall a b, Le R a b -> Le R b a -> a = b.
  Proof.
    unfold Le; intros a b p q.
    rewrite <- q, (alt_comm (ralt R)). exact p.
  Qed.

  Lemma zero_least : forall a, Le R (rzero R) a.
  Proof. apply (alt_unitl (ralt R)). Qed.

  Lemma add_upperl : forall a b, Le R a (radd R a b).
  Proof.
    unfold Le; intros a b.
    rewrite <- (alt_assoc (ralt R)), (alt_idem (ralt R)). reflexivity.
  Qed.

  Lemma add_upperr : forall a b, Le R b (radd R a b).
  Proof.
    unfold Le; intros a b.
    rewrite (alt_comm (ralt R) a b), <- (alt_assoc (ralt R)), (alt_idem (ralt R)).
    reflexivity.
  Qed.

  (** Agda [⊕-least]: any common upper bound of [a] and [b] is above [a ⊕ b],
      so with [add_upperl]/[add_upperr] [⊕] is the join of [≼]. *)
  Lemma add_least : forall a b c, Le R a c -> Le R b c -> Le R (radd R a b) c.
  Proof.
    unfold Le; intros a b c p q.
    rewrite (alt_assoc (ralt R)), q. exact p.
  Qed.
End Order.

Record IsOrdered (R : ResourceAlgebra) : Prop := {
  mono_l : forall c a b, Le R a b -> Le R (rmul R c a) (rmul R c b);
  mono_r : forall c a b, Le R a b -> Le R (rmul R a c) (rmul R b c)
}.

Record IsDioid (R : ResourceAlgebra) : Prop := {
  distribl : forall a b c, rmul R a (radd R b c) = radd R (rmul R a b) (rmul R a c);
  distribr : forall a b c, rmul R (radd R a b) c = radd R (rmul R a c) (rmul R b c)
}.

(** C-3: every dioid is ordered. *)
Lemma dioid_ordered (R : ResourceAlgebra) : IsDioid R -> IsOrdered R.
Proof.
  intro d. split; unfold Le; intros c a b p.
  - rewrite <- (distribl d), p. reflexivity.
  - rewrite <- (distribr d), p. reflexivity.
Qed.

Record IsAnnihilating (R : ResourceAlgebra) : Prop := {
  annihill : forall a, rmul R (rzero R) a = rzero R;
  annihilr : forall a, rmul R a (rzero R) = rzero R
}.

(** * Loss (L-1) *)

Inductive LGrade : Type := fin : nat -> LGrade | inf : LGrade.

Definition lplus (a b : LGrade) : LGrade :=
  match a, b with
  | fin m, fin n => fin (m + n)
  | fin _, inf => inf
  | inf, _ => inf
  end.

Definition lmin (a b : LGrade) : LGrade :=
  match a, b with
  | fin m, fin n => fin (rmin m n)
  | fin m, inf => fin m
  | inf, g => g
  end.

Lemma fin_injective : forall m n, fin m = fin n -> m = n.
Proof. intros m n H. now injection H. Qed.

(** Case-split every grade argument, normalise, and close the arithmetic. *)
Ltac grades :=
  repeat match goal with
         | a : LGrade |- _ => destruct a
         end;
  simpl; unfold_rmm; try reflexivity;
  try (f_equal; lia).

Lemma Loss_alt : IsAltMonoid lmin inf.
Proof. split; intros; grades. Qed.

Lemma Loss_seq : IsSeqMonoid lplus (fin 0).
Proof. split; intros; grades. Qed.

Definition Loss : ResourceAlgebra :=
  {| Grade := LGrade; radd := lmin; rmul := lplus; rzero := inf; rone := fin 0;
     ralt := Loss_alt; rseq := Loss_seq |}.

Lemma Loss_dioid : IsDioid Loss.
Proof. split; simpl; intros; grades. Qed.

Lemma Loss_ordered : IsOrdered Loss.
Proof. exact (dioid_ordered Loss_dioid). Qed.

Lemma Loss_annihilating : IsAnnihilating Loss.
Proof. split; simpl; intros; grades. Qed.

(** * MaxPlus (M-1) *)

Inductive Tropical : Type := val : nat -> Tropical | bot : Tropical.

Definition tAdd (a b : Tropical) : Tropical :=
  match a, b with
  | bot, b => b
  | val m, bot => val m
  | val m, val n => val (rmax m n)
  end.

Definition tMul (a b : Tropical) : Tropical :=
  match a, b with
  | bot, _ => bot
  | val _, bot => bot
  | val m, val n => val (m + n)
  end.

Lemma val_injective : forall m n, val m = val n -> m = n.
Proof. intros m n H. now injection H. Qed.

Ltac trops :=
  repeat match goal with
         | a : Tropical |- _ => destruct a
         end;
  simpl; unfold_rmm; try reflexivity;
  try (f_equal; lia).

Lemma MaxPlus_alt : IsAltMonoid tAdd bot.
Proof. split; intros; trops. Qed.

Lemma MaxPlus_seq : IsSeqMonoid tMul (val 0).
Proof. split; intros; trops. Qed.

Definition MaxPlus : ResourceAlgebra :=
  {| Grade := Tropical; radd := tAdd; rmul := tMul; rzero := bot; rone := val 0;
     ralt := MaxPlus_alt; rseq := MaxPlus_seq |}.

Lemma MaxPlus_dioid : IsDioid MaxPlus.
Proof. split; simpl; intros; trops. Qed.

Lemma MaxPlus_ordered : IsOrdered MaxPlus.
Proof. exact (dioid_ordered MaxPlus_dioid). Qed.

Lemma MaxPlus_annihilating : IsAnnihilating MaxPlus.
Proof. split; simpl; intros; trops. Qed.

(** * HWM (H-1, H-3) *)

Record HGrade : Type := hwm {
  peak : nat;
  drift : nat;
  bounded : drift <= peak
}.

(* The constructor takes peak and drift explicitly, as Agda's [hwm] does. *)
Arguments hwm : clear implicits.

(** [hwm-≡]: grades are equal when peak and drift are. The bound is
    irrelevant by [Peano_dec.le_unique], a theorem of the standard library. *)
Lemma hwm_eq : forall a b : HGrade, peak a = peak b -> drift a = drift b -> a = b.
Proof.
  intros [p n bd] [p' n' bd'] e1 e2; simpl in *; subst.
  f_equal. apply Peano_dec.le_unique.
Qed.

Definition mulH (a b : HGrade) : HGrade.
Proof.
  refine (hwm (rmax (peak a) (drift a + peak b)) (drift a + drift b) _).
  destruct a, b; simpl; rewrite rmax_eq; lia.
Defined.

Definition addH (a b : HGrade) : HGrade.
Proof.
  refine (hwm (rmax (peak a) (peak b)) (rmax (drift a) (drift b)) _).
  destruct a, b; simpl; rewrite !rmax_eq; lia.
Defined.

Definition zeroH : HGrade := hwm 0 0 (le_n 0).

Ltac hwms :=
  repeat match goal with
         | a : HGrade |- _ => destruct a
         end;
  apply hwm_eq; simpl; unfold_rmm; lia.

(** H-1, with 𝟘 = 𝟙 by construction. *)
Lemma HWM_alt : IsAltMonoid addH zeroH.
Proof. split; intros; hwms. Qed.

Lemma HWM_seq : IsSeqMonoid mulH zeroH.
Proof. split; intros; hwms. Qed.

Definition HWM : ResourceAlgebra :=
  {| Grade := HGrade; radd := addH; rmul := mulH; rzero := zeroH; rone := zeroH;
     ralt := HWM_alt; rseq := HWM_seq |}.

Lemma HWM_zero_eq_one : rzero HWM = rone HWM.
Proof. reflexivity. Qed.

Lemma HWM_dioid : IsDioid HWM.
Proof. split; simpl; intros; hwms. Qed.

Lemma HWM_ordered : IsOrdered HWM.
Proof. exact (dioid_ordered HWM_dioid). Qed.

(** H-3: HWM has no annihilating zero. *)
Lemma HWM_not_annihilating : ~ IsAnnihilating HWM.
Proof.
  intro z.
  pose proof (f_equal peak (annihill z (hwm 1 0 (le_S 0 0 (le_n 0))))) as h.
  simpl in h. discriminate h.
Qed.

(** C-4a: a dioid need not be annihilating. *)
Lemma dioid_not_annihilating : IsDioid HWM /\ ~ IsAnnihilating HWM.
Proof. exact (conj HWM_dioid HWM_not_annihilating). Qed.

(** * MinMax (N-1) *)

Definition lmax (a b : LGrade) : LGrade :=
  match a, b with
  | inf, _ => inf
  | fin _, inf => inf
  | fin m, fin n => fin (rmax m n)
  end.

Lemma MinMax_seq : IsSeqMonoid lmax (fin 0).
Proof. split; intros; grades. Qed.

Definition MinMax : ResourceAlgebra :=
  {| Grade := LGrade; radd := lmin; rmul := lmax; rzero := inf; rone := fin 0;
     ralt := Loss_alt; rseq := MinMax_seq |}.

Lemma MinMax_dioid : IsDioid MinMax.
Proof. split; simpl; intros; grades. Qed.

Lemma MinMax_ordered : IsOrdered MinMax.
Proof. exact (dioid_ordered MinMax_dioid). Qed.

Lemma MinMax_annihilating : IsAnnihilating MinMax.
Proof. split; simpl; intros; grades. Qed.

(** * Morphisms (F-1 .. F-7) *)

Record Hom (A B : ResourceAlgebra) : Type := {
  hmap      : Grade A -> Grade B;
  hmap_zero : hmap (rzero A) = rzero B;
  hmap_one  : hmap (rone A) = rone B;
  hmap_add  : forall a b, hmap (radd A a b) = radd B (hmap a) (hmap b);
  hmap_mul  : forall a b, hmap (rmul A a b) = rmul B (hmap a) (hmap b)
}.

Record LaxHom (A B : ResourceAlgebra) : Type := {
  lmap     : Grade A -> Grade B;
  lmap_one : lmap (rone A) = rone B;
  lmap_add : forall a b, lmap (radd A a b) = radd B (lmap a) (lmap b);
  lmap_mul : forall a b, Le B (lmap (rmul A a b)) (rmul B (lmap a) (lmap b))
}.

Lemma lax_mono {A B} (f : LaxHom A B) :
  forall a b, Le A a b -> Le B (lmap f a) (lmap f b).
Proof. unfold Le; intros a b p. rewrite <- (lmap_add f), p. reflexivity. Qed.

(** F-1: every strict morphism is lax. *)
Definition lax {A B} (h : Hom A B) : LaxHom A B.
Proof.
  refine {| lmap := hmap h; lmap_one := hmap_one h; lmap_add := hmap_add h |}.
  intros a b. rewrite (hmap_mul h). apply le_refl.
Defined.

(** F-1: identities and composition. *)
Definition id_hom (A : ResourceAlgebra) : Hom A A :=
  {| hmap := fun a => a; hmap_zero := eq_refl; hmap_one := eq_refl;
     hmap_add := fun _ _ => eq_refl; hmap_mul := fun _ _ => eq_refl |}.

Definition comp_hom {A B C} (g : Hom B C) (f : Hom A B) : Hom A C.
Proof.
  refine {| hmap := fun a => hmap g (hmap f a) |}.
  - rewrite (hmap_zero f). apply (hmap_zero g).
  - rewrite (hmap_one f). apply (hmap_one g).
  - intros a b. rewrite (hmap_add f). apply (hmap_add g).
  - intros a b. rewrite (hmap_mul f). apply (hmap_mul g).
Defined.

Definition id_lax (A : ResourceAlgebra) : LaxHom A A := lax (id_hom A).

Definition comp_lax {A B C} (g : LaxHom B C) (f : LaxHom A B) : LaxHom A C.
Proof.
  refine {| lmap := fun a => lmap g (lmap f a) |}.
  - rewrite (lmap_one f). apply (lmap_one g).
  - intros a b. rewrite (lmap_add f). apply (lmap_add g).
  - intros a b. eapply le_trans.
    + apply (lax_mono g), (lmap_mul f).
    + apply (lmap_mul g).
Defined.

(** F-2: [peak : HWM → MaxPlus] is lax. *)
Definition peak_lax : LaxHom HWM MaxPlus.
Proof.
  refine (@Build_LaxHom HWM MaxPlus (fun g : HGrade => val (peak g)) _ _ _).
  - reflexivity.
  - intros [p n bd] [p' n' bd']; reflexivity.
  - intros [p n bd] [p' n' bd']; unfold Le; simpl.
    rewrite !rmax_eq. f_equal. lia.
Defined.

(** F-3: [peak] does not preserve ⊗. *)
Lemma peak_not_strict :
  ~ (forall a b : HGrade, val (peak (mulH a b)) = tMul (val (peak a)) (val (peak b))).
Proof.
  intro f.
  pose proof (f (hwm 2 0 (Nat.le_0_l 2)) (hwm 3 0 (Nat.le_0_l 3))) as h.
  simpl in h. discriminate h.
Qed.

(** F-4: no strict morphism leaves HWM for an algebra with 𝟘 ≠ 𝟙. *)
Lemma no_strict_from_HWM (B : ResourceAlgebra) :
  rzero B <> rone B -> Hom HWM B -> False.
Proof.
  intros hne h. apply hne.
  rewrite <- (hmap_zero h), <- (hmap_one h). reflexivity.
Qed.

Lemma no_strict_HWM_MaxPlus : Hom HWM MaxPlus -> False.
Proof. apply no_strict_from_HWM. discriminate. Qed.

Lemma no_strict_HWM_Loss : Hom HWM Loss -> False.
Proof. apply no_strict_from_HWM. discriminate. Qed.

(** F-5: exactly two strict morphisms Loss → MaxPlus. *)

Definition zero_test (a : LGrade) : Tropical :=
  match a with
  | fin 0 => val 0
  | fin (S _) => bot
  | inf => bot
  end.

Definition support (a : LGrade) : Tropical :=
  match a with
  | fin _ => val 0
  | inf => bot
  end.

Definition zero_test_hom : Hom Loss MaxPlus.
Proof.
  refine (@Build_Hom Loss MaxPlus zero_test eq_refl eq_refl _ _).
  - intros [[|m]|] [[|n]|]; reflexivity.
  - intros [[|m]|] [[|n]|]; reflexivity.
Defined.

Definition support_hom : Hom Loss MaxPlus.
Proof.
  refine (@Build_Hom Loss MaxPlus support eq_refl eq_refl _ _).
  - intros [m|] [n|]; reflexivity.
  - intros [m|] [n|]; reflexivity.
Defined.

(** The two maps differ (Agda: [maps-disagree-at-positive]). *)
Lemma maps_disagree_at_positive : forall n, zero_test (fin (S n)) <> support (fin (S n)).
Proof. discriminate. Qed.

(** Every strict morphism Loss → MaxPlus is one of the two, and the result
    says which. As Agda's [_⊎_], this is a sum a caller can branch on
    ([sumbool]), not a propositional [\/]. *)
Definition Loss_to_MaxPlus (h : Hom Loss MaxPlus) :
  {forall a, hmap h a = zero_test a} + {forall a, hmap h a = support a}.
Proof.
  assert (one : hmap h (fin 0) = val 0) by exact (hmap_one h).
  assert (step : forall n, hmap h (fin (S n)) = tMul (hmap h (fin n)) (hmap h (fin 1))).
  { intro n. rewrite <- Nat.add_1_r. exact (hmap_mul h (fin n) (fin 1)). }
  assert (pin : hmap h (fin 0) = tAdd (hmap h (fin 0)) (hmap h (fin 1)))
    by exact (hmap_add h (fin 0) (fin 1)).
  rewrite one in pin.
  destruct (hmap h (fin 1)) as [c|] eqn:e.
  - right.
    assert (c0 : c = 0).
    { try rewrite e in pin. simpl in pin. injection pin. lia. }
    subst c.
    assert (fv : forall n, hmap h (fin n) = val 0).
    { induction n as [|n ih]; [exact one|]. rewrite step, ih; try rewrite e; reflexivity. }
    intros [n|]; [apply fv | exact (hmap_zero h)].
  - left.
    intros [[|n]|].
    + exact one.
    + rewrite step; try rewrite e. destruct (hmap h (fin n)); reflexivity.
    + exact (hmap_zero h).
Defined.

Lemma Loss_to_MaxPlus_collapses (h : Hom Loss MaxPlus) :
  hmap h (fin 1) = hmap h (fin 2).
Proof.
  destruct (Loss_to_MaxPlus h) as [z|s].
  - rewrite (z (fin 1)), (z (fin 2)). reflexivity.
  - rewrite (s (fin 1)), (s (fin 2)). reflexivity.
Qed.

Lemma no_injective_Loss_to_MaxPlus (h : Hom Loss MaxPlus) :
  (forall a b, hmap h a = hmap h b -> a = b) -> False.
Proof.
  intro inj. pose proof (inj (fin 1) (fin 2) (Loss_to_MaxPlus_collapses h)) as H.
  discriminate H.
Qed.

(** F-6: exactly one strict morphism MaxPlus → Loss. *)

Definition support' (a : Tropical) : LGrade :=
  match a with
  | val _ => fin 0
  | bot => inf
  end.

Definition support'_hom : Hom MaxPlus Loss.
Proof.
  refine (@Build_Hom MaxPlus Loss support' eq_refl eq_refl _ _).
  - intros [m|] [n|]; reflexivity.
  - intros [m|] [n|]; reflexivity.
Defined.

Lemma MaxPlus_to_Loss (h : Hom MaxPlus Loss) : forall a, hmap h a = support' a.
Proof.
  assert (one : hmap h (val 0) = fin 0) by exact (hmap_one h).
  assert (absorb : hmap h (val 1) = lmin (hmap h (val 0)) (hmap h (val 1)))
    by exact (hmap_add h (val 0) (val 1)).
  rewrite one in absorb.
  assert (v1 : hmap h (val 1) = fin 0).
  { destruct (hmap h (val 1)) as [c|] eqn:e.
    - simpl in absorb. exact absorb.
    - discriminate absorb. }
  assert (fv : forall n, hmap h (val n) = fin 0).
  { induction n as [|n ih]; [exact one|].
    rewrite <- Nat.add_1_r.
    change (hmap h (val (n + 1))) with (hmap h (rmul MaxPlus (val n) (val 1))).
    rewrite (hmap_mul h), ih, v1. reflexivity. }
  intros [n|]; [apply fv | exact (hmap_zero h)].
Qed.

(** F-7: the identity is lax Loss → MinMax. *)
Definition loss_bottleneck : LaxHom Loss MinMax.
Proof.
  refine (@Build_LaxHom Loss MinMax (fun a : LGrade => a) eq_refl (fun _ _ => eq_refl) _).
  intros a b. destruct a as [m|], b as [n|]; unfold Le; simpl; unfold_rmm; try reflexivity. f_equal. lia.
Defined.

(** * Separation (S-1 .. S-4) *)

Definition two : HGrade := hwm 2 0 (Nat.le_0_l 2).
Definition three : HGrade := hwm 3 0 (Nat.le_0_l 3).

(** S-1 *)
Lemma occupancy_is_not_cost : peak (mulH two three) <> 5.
Proof. simpl. discriminate. Qed.

(** S-2 *)
Lemma alternatives_differ : lmin (fin 2) (fin 3) <> fin 3.
Proof. simpl. discriminate. Qed.

(** S-3 *)
Lemma maxplus_order : Le MaxPlus (val 1) (val 2).
Proof. reflexivity. Qed.
Lemma loss_order_reversed : Le Loss (fin 2) (fin 1).
Proof. reflexivity. Qed.

(** S-4 *)
Lemma bottleneck_is_not_sum : lmax (fin 2) (fin 3) <> lplus (fin 2) (fin 3).
Proof. simpl. discriminate. Qed.

(** * Questions (Q-1 .. Q-4) *)

(** [Q n]: n booleans, by recursion on n. [true] means the question is lost. *)
Fixpoint Q (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => (bool * Q n)%type
  end.

Fixpoint qrep (b : bool) (n : nat) : Q n :=
  match n with
  | 0 => tt
  | S n => (b, qrep b n)
  end.

Fixpoint qzip (f : bool -> bool -> bool) (n : nat) : Q n -> Q n -> Q n :=
  match n with
  | 0 => fun _ _ => tt
  | S n => fun x y => (f (fst x) (fst y), qzip f n (snd x) (snd y))
  end.

Arguments qrep : clear implicits.
Arguments qzip : clear implicits.

(** Induct on the number of questions, split every grade into its bits, and
    close each bit with the one-question law [p]. *)
Ltac questions p :=
  let n := fresh "n" in
  let IH := fresh "IH" in
  intro n; induction n as [|n IH]; simpl; intros;
  repeat match goal with
         | x : unit |- _ => destruct x
         | x : (bool * Q _)%type |- _ => destruct x
         end;
  simpl; [reflexivity | rewrite ?p, ?IH; reflexivity].

Section QLift.
  Variable f : bool -> bool -> bool.

  Lemma qzip_assoc : (forall a b c, f (f a b) c = f a (f b c)) ->
    forall n x y z, qzip f n (qzip f n x y) z = qzip f n x (qzip f n y z).
  Proof. intro p. questions p. Qed.

  Lemma qzip_comm : (forall a b, f a b = f b a) ->
    forall n x y, qzip f n x y = qzip f n y x.
  Proof.
    intros p n; induction n as [|n IH]; simpl; intros x y; [reflexivity|].
    rewrite (p (fst x)), (IH (snd x)). reflexivity.
  Qed.

  Lemma qzip_idem : (forall a, f a a = a) -> forall n x, qzip f n x x = x.
  Proof. intro p. questions p. Qed.

  Lemma qzip_unitl : forall e, (forall a, f e a = a) ->
    forall n x, qzip f n (qrep e n) x = x.
  Proof. intros e p. questions p. Qed.

  Lemma qzip_unitr : forall e, (forall a, f a e = a) ->
    forall n x, qzip f n x (qrep e n) = x.
  Proof. intros e p. questions p. Qed.

  Lemma qzip_zerol : forall z, (forall a, f z a = z) ->
    forall n x, qzip f n (qrep z n) x = qrep z n.
  Proof. intros z p. questions p. Qed.

  Lemma qzip_zeror : forall z, (forall a, f a z = z) ->
    forall n x, qzip f n x (qrep z n) = qrep z n.
  Proof. intros z p. questions p. Qed.
End QLift.

Lemma bor_band_l : forall a b c, orb a (andb b c) = andb (orb a b) (orb a c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma bor_band_r : forall a b c, orb (andb a b) c = andb (orb a c) (orb b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma Questions_alt (n : nat) : IsAltMonoid (qzip andb n) (qrep true n).
Proof.
  split.
  - apply qzip_assoc. intros [] [] []; reflexivity.
  - apply qzip_comm. intros [] []; reflexivity.
  - apply qzip_idem. intros []; reflexivity.
  - apply qzip_unitl. reflexivity.
Qed.

Lemma Questions_seq (n : nat) : IsSeqMonoid (qzip orb n) (qrep false n).
Proof.
  split.
  - apply qzip_assoc. intros [] [] []; reflexivity.
  - apply qzip_unitl. reflexivity.
  - apply qzip_unitr. intros []; reflexivity.
Qed.

(** Q-1: ⊕ = intersection ([andb]), ⊗ = union ([orb]), 𝟘 = all lost, 𝟙 = none lost. *)
Definition Questions (n : nat) : ResourceAlgebra :=
  {| Grade := Q n; radd := qzip andb n; rmul := qzip orb n;
     rzero := qrep true n; rone := qrep false n;
     ralt := Questions_alt n; rseq := Questions_seq n |}.

Lemma Questions_dioid (n : nat) : IsDioid (Questions n).
Proof.
  split; simpl.
  - revert n. questions bor_band_l.
  - revert n. questions bor_band_r.
Qed.

Lemma Questions_ordered (n : nat) : IsOrdered (Questions n).
Proof. exact (dioid_ordered (Questions_dioid n)). Qed.

Lemma Questions_annihilating (n : nat) : IsAnnihilating (Questions n).
Proof.
  split; simpl.
  - apply qzip_zerol. reflexivity.
  - apply qzip_zeror. intros []; reflexivity.
Qed.

(** Question 0: the order of the pieces. Question 1: do the two copies differ. *)
Definition collapse : Q 2 := (false, (true, tt)).
Definition shuffle : Q 2 := (true, (false, tt)).

(** Q-2 *)
Lemma same_amount_different_loss : collapse <> shuffle.
Proof. discriminate. Qed.

(** Q-3 *)
Lemma both_lost : rmul (Questions 2) collapse shuffle = qrep true 2.
Proof. reflexivity. Qed.

(** Q-4 *)
Lemma no_branch_achieves_meet : radd (Questions 2) collapse shuffle = qrep false 2.
Proof. reflexivity. Qed.

(** * Morphisms out of Questions (F-8 .. F-10) *)

(** Lost goes to 𝟘, kept goes to 𝟙. *)
Definition verdict (B : ResourceAlgebra) (b : bool) : Grade B :=
  if b then rzero B else rone B.

(** F-8: the one strict morphism out of one question. *)
Definition one_question_hom (B : ResourceAlgebra)
  (zz : rmul B (rzero B) (rzero B) = rzero B) : Hom (Questions 1) B.
Proof.
  refine (@Build_Hom (Questions 1) B (fun x => verdict B (fst x)) eq_refl eq_refl _ _).
  - intros [[] []] [[] []]; simpl; symmetry.
    + apply (alt_idem (ralt B)).
    + apply (alt_unitl (ralt B)).
    + apply (alt_unitr (ralt B)).
    + apply (alt_idem (ralt B)).
  - intros [[] []] [[] []]; simpl; symmetry.
    + exact zz.
    + apply (seq_unitr (rseq B)).
    + apply (seq_unitl (rseq B)).
    + apply (seq_unitl (rseq B)).
Defined.

(** F-8: the condition is necessary. *)
Lemma one_question_needs (B : ResourceAlgebra) (h : Hom (Questions 1) B) :
  rmul B (rzero B) (rzero B) = rzero B.
Proof.
  pose proof (hmap_mul h (qrep true 1) (qrep true 1)) as m.
  pose proof (hmap_zero h) as z.
  simpl in m, z. rewrite z in m. symmetry. exact m.
Qed.

(** F-8: every strict morphism out of one question is that map. *)
Lemma one_question_unique (B : ResourceAlgebra) (h : Hom (Questions 1) B) :
  forall x, hmap h x = verdict B (fst x).
Proof.
  intros [[] []]; simpl.
  - exact (hmap_zero h).
  - exact (hmap_one h).
Qed.

(** F-9: each question can be read alone. *)
Definition first_question (n : nat) : Hom (Questions (S n)) (Questions 1).
Proof.
  refine (@Build_Hom (Questions (S n)) (Questions 1) (fun x => (fst x, tt))
            eq_refl eq_refl _ _); intros; reflexivity.
Defined.

Definition later_questions (n : nat) : Hom (Questions (S n)) (Questions n).
Proof.
  refine (@Build_Hom (Questions (S n)) (Questions n) (fun x => snd x)
            eq_refl eq_refl _ _); intros; reflexivity.
Defined.

(** [count]: how many questions are lost. *)
Fixpoint qcount (n : nat) : Q n -> nat :=
  match n with
  | 0 => fun _ => 0
  | S n => fun x => if fst x then S (qcount n (snd x)) else qcount n (snd x)
  end.

Arguments qcount : clear implicits.

(** F-10: the number of lost questions does not preserve alternatives. *)
Lemma count_not_add :
  ~ (forall a b : Q 2, fin (qcount 2 (radd (Questions 2) a b))
                       = lmin (fin (qcount 2 a)) (fin (qcount 2 b))).
Proof.
  intro f. pose proof (f collapse shuffle) as h. simpl in h. discriminate h.
Qed.

(** * Assumptions (PROOF-POLICY §8.4): each must print "Closed under the
    global context". *)
Print Assumptions alt_unitr.
Print Assumptions le_trans.
Print Assumptions le_antisym.
Print Assumptions add_upperl.
Print Assumptions add_upperr.
Print Assumptions add_least.
Print Assumptions dioid_ordered.
Print Assumptions dioid_not_annihilating.
Print Assumptions Loss_dioid.
Print Assumptions Loss_annihilating.
Print Assumptions MaxPlus_dioid.
Print Assumptions MaxPlus_annihilating.
Print Assumptions HWM.
Print Assumptions HWM_dioid.
Print Assumptions MinMax_dioid.
Print Assumptions MinMax_annihilating.
Print Assumptions id_hom.
Print Assumptions comp_hom.
Print Assumptions id_lax.
Print Assumptions comp_lax.
Print Assumptions peak_lax.
Print Assumptions peak_not_strict.
Print Assumptions no_strict_HWM_MaxPlus.
Print Assumptions no_strict_HWM_Loss.
Print Assumptions zero_test_hom.
Print Assumptions support_hom.
Print Assumptions maps_disagree_at_positive.
Print Assumptions Loss_to_MaxPlus.
Print Assumptions no_injective_Loss_to_MaxPlus.
Print Assumptions support'_hom.
Print Assumptions MaxPlus_to_Loss.
Print Assumptions loss_bottleneck.
Print Assumptions occupancy_is_not_cost.
Print Assumptions alternatives_differ.
Print Assumptions maxplus_order.
Print Assumptions loss_order_reversed.
Print Assumptions bottleneck_is_not_sum.
Print Assumptions Questions_dioid.
Print Assumptions Questions_annihilating.
Print Assumptions same_amount_different_loss.
Print Assumptions both_lost.
Print Assumptions no_branch_achieves_meet.
Print Assumptions one_question_hom.
Print Assumptions one_question_needs.
Print Assumptions one_question_unique.
Print Assumptions first_question.
Print Assumptions later_questions.
Print Assumptions count_not_add.
