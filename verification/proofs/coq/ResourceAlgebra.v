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

From Stdlib Require Import Arith Lia ZArith.
From Stdlib Require Eqdep_dec Bool.

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

(** * Diamond (C-4b)

    The diamond lattice M3: join for alternatives, meet for sequence, the
    bottom for 𝟘 and the top for 𝟙. Meet is monotone and the bottom
    annihilates, but M3 is not distributive, so meet does not distribute
    over join. Every law is a closed statement over five constructors. *)

Inductive DGrade : Type := dbot | dtop | da | db | dc.

(** Agda [_⊔d_], the join. *)
Definition djoin (x y : DGrade) : DGrade :=
  match x, y with
  | dbot, y => y
  | dtop, _ => dtop
  | da, dbot => da | da, dtop => dtop | da, da => da | da, db => dtop | da, dc => dtop
  | db, dbot => db | db, dtop => dtop | db, da => dtop | db, db => db | db, dc => dtop
  | dc, dbot => dc | dc, dtop => dtop | dc, da => dtop | dc, db => dtop | dc, dc => dc
  end.

(** Agda [_⊓d_], the meet. *)
Definition dmeet (x y : DGrade) : DGrade :=
  match x, y with
  | dbot, _ => dbot
  | dtop, y => y
  | da, dbot => dbot | da, dtop => da | da, da => da | da, db => dbot | da, dc => dbot
  | db, dbot => dbot | db, dtop => db | db, da => dbot | db, db => db | db, dc => dbot
  | dc, dbot => dbot | dc, dtop => dc | dc, da => dbot | dc, db => dbot | dc, dc => dc
  end.

Lemma Diamond_alt : IsAltMonoid djoin dbot.
Proof. split; intros; repeat match goal with x : DGrade |- _ => destruct x end; reflexivity. Qed.

Lemma Diamond_seq : IsSeqMonoid dmeet dtop.
Proof. split; intros; repeat match goal with x : DGrade |- _ => destruct x end; reflexivity. Qed.

Definition Diamond : ResourceAlgebra :=
  {| Grade := DGrade; radd := djoin; rmul := dmeet; rzero := dbot; rone := dtop;
     ralt := Diamond_alt; rseq := Diamond_seq |}.

Lemma Diamond_ordered : IsOrdered Diamond.
Proof.
  split; unfold Le; simpl; intros z x y p;
    destruct z, x, y; simpl in *; try reflexivity; discriminate p.
Qed.

Lemma Diamond_annihilating : IsAnnihilating Diamond.
Proof. split; simpl; intros x; destruct x; reflexivity. Qed.

(** Not a dioid: [a ⊓ (b ⊔ c) = a], while [(a ⊓ b) ⊔ (a ⊓ c) = ⊥]. *)
Lemma Diamond_not_dioid : ~ IsDioid Diamond.
Proof.
  intro d. pose proof (distribl d da db dc) as h. simpl in h. discriminate h.
Qed.

(** C-4b: an annihilating ordered algebra need not be a dioid. *)
Lemma ordered_annihilating_not_dioid :
  IsOrdered Diamond /\ IsAnnihilating Diamond /\ ~ IsDioid Diamond.
Proof. exact (conj Diamond_ordered (conj Diamond_annihilating Diamond_not_dioid)). Qed.

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

(** * Evidence (E-1) *)

(** The status of a proof-ledger row, as a chain, weakest first:
    [openRow < testedOnly < argued < provenWithPostulates < proven].
    A status is coded by its rank (0 to 4); alternatives take the max of the
    ranks and sequence the min, as in Agda's [Instances/Evidence.agda]. *)

(** [min m n ≤ m] (Agda: [min-≤-left]). *)
Lemma rmin_le_left : forall m n, rmin m n <= m.
Proof. intros m n. rewrite rmin_eq. lia. Qed.

(** [min m n ≤ n] (Agda: [min-≤-right]). *)
Lemma rmin_le_right : forall m n, rmin m n <= n.
Proof. intros m n. rewrite rmin_eq. lia. Qed.

(** [k ≤ m → k ≤ n → k ≤ min m n] (Agda: [min-glb]). *)
Lemma rmin_glb : forall k m n, k <= m -> k <= n -> k <= rmin m n.
Proof. intros k m n p q. rewrite rmin_eq. lia. Qed.

(** [min a (max b c) = max (min a b) (min a c)] (Agda: [min-distribˡ-max]). *)
Lemma rmin_rmax_l : forall a b c, rmin a (rmax b c) = rmax (rmin a b) (rmin a c).
Proof. intros a b c. unfold_rmm. lia. Qed.

(** [max m n = n → m ≤ n] (Agda: [max-≡→≤]). *)
Lemma rmax_eq_le : forall m n, rmax m n = n -> m <= n.
Proof. intros m n p. rewrite rmax_eq in p. lia. Qed.

(** The closed status vocabulary of PROOF-POLICY §5, weakest first. *)
Inductive Status : Type :=
  | openRow | testedOnly | argued | provenWithPostulates | proven.

Definition rank (s : Status) : nat :=
  match s with
  | openRow => 0
  | testedOnly => 1
  | argued => 2
  | provenWithPostulates => 3
  | proven => 4
  end.

(** Every rank from 4 up names [proven]. *)
Definition from_rank (n : nat) : Status :=
  match n with
  | 0 => openRow
  | 1 => testedOnly
  | 2 => argued
  | 3 => provenWithPostulates
  | S (S (S (S _))) => proven
  end.

Lemma from_rank_rank : forall s, from_rank (rank s) = s.
Proof. intros []; reflexivity. Qed.

Lemma rank_le_4 : forall s, rank s <= 4.
Proof. intros []; simpl; lia. Qed.

Lemma rank_from_rank : forall n, n <= 4 -> rank (from_rank n) = n.
Proof.
  intros [|[|[|[|[|n]]]]] p; try reflexivity. lia.
Qed.

(** Two statuses with one rank are one status. *)
Lemma rank_injective : forall s t, rank s = rank t -> s = t.
Proof.
  intros s t p. rewrite <- (from_rank_rank s), <- (from_rank_rank t), p.
  reflexivity.
Qed.

(** [_⊔e_]: alternatives keep the stronger status. *)
Definition ejoin (s t : Status) : Status := from_rank (rmax (rank s) (rank t)).

(** [_⊓e_]: sequence keeps the weaker status. *)
Definition emeet (s t : Status) : Status := from_rank (rmin (rank s) (rank t)).

Lemma rank_ejoin : forall s t, rank (ejoin s t) = rmax (rank s) (rank t).
Proof.
  intros s t. apply rank_from_rank.
  pose proof (rank_le_4 s). pose proof (rank_le_4 t). rewrite rmax_eq. lia.
Qed.

Lemma rank_emeet : forall s t, rank (emeet s t) = rmin (rank s) (rank t).
Proof.
  intros s t. apply rank_from_rank.
  pose proof (rank_le_4 s). rewrite rmin_eq. lia.
Qed.

(** Rewrite both sides to ranks and close the arithmetic. *)
Ltac by_rank :=
  apply rank_injective;
  repeat (first [rewrite rank_ejoin | rewrite rank_emeet]);
  cbn [rank];
  unfold_rmm; lia.

Lemma Evidence_alt : IsAltMonoid ejoin openRow.
Proof.
  split.
  - intros a b c. by_rank.
  - intros a b. by_rank.
  - intros a. by_rank.
  - intros a. by_rank.
Qed.

Lemma Evidence_seq : IsSeqMonoid emeet proven.
Proof.
  split.
  - intros a b c. by_rank.
  - intros a. pose proof (rank_le_4 a). by_rank.
  - intros a. pose proof (rank_le_4 a). by_rank.
Qed.

(** E-1: ⊕ = the stronger, ⊗ = the weaker, 𝟘 = [openRow], 𝟙 = [proven]. *)
Definition Evidence : ResourceAlgebra :=
  {| Grade := Status; radd := ejoin; rmul := emeet; rzero := openRow; rone := proven;
     ralt := Evidence_alt; rseq := Evidence_seq |}.

Lemma Evidence_dioid : IsDioid Evidence.
Proof. split; cbn [rmul radd Evidence]; intros a b c; by_rank. Qed.

Lemma Evidence_ordered : IsOrdered Evidence.
Proof. exact (dioid_ordered Evidence_dioid). Qed.

Lemma Evidence_annihilating : IsAnnihilating Evidence.
Proof. split; cbn [rmul rzero Evidence]; intro a; by_rank. Qed.

(** E-1: the order is the rank order, and sequence is its meet. *)

(** Agda [≼→≤]. *)
Lemma le_to_rank : forall a b, Le Evidence a b -> rank a <= rank b.
Proof.
  unfold Le; simpl; intros a b p.
  apply rmax_eq_le. rewrite <- rank_ejoin, p. reflexivity.
Qed.

(** Agda [≤→≼]. *)
Lemma rank_to_le : forall a b, rank a <= rank b -> Le Evidence a b.
Proof.
  unfold Le; simpl; intros a b p.
  apply rank_injective. rewrite rank_ejoin, rmax_eq. lia.
Qed.

(** Agda [≼-proven]. *)
Lemma le_proven : forall a, Le Evidence a proven.
Proof. intro a. apply rank_to_le, rank_le_4. Qed.

(** Agda [⊓e-lowerˡ]. *)
Lemma emeet_lowerl : forall a b, Le Evidence (emeet a b) a.
Proof. intros a b. apply rank_to_le. rewrite rank_emeet. apply rmin_le_left. Qed.

(** Agda [⊓e-lowerʳ]. *)
Lemma emeet_lowerr : forall a b, Le Evidence (emeet a b) b.
Proof. intros a b. apply rank_to_le. rewrite rank_emeet. apply rmin_le_right. Qed.

(** Agda [⊓e-greatest]. *)
Lemma emeet_greatest : forall a b c,
  Le Evidence c a -> Le Evidence c b -> Le Evidence c (emeet a b).
Proof.
  intros a b c p q. apply rank_to_le. rewrite rank_emeet.
  apply rmin_glb; apply le_to_rank; assumption.
Qed.

(** * Evidence ledger (E-2, E-3) *)

(** A ledger is a list of rows, newest first. A row's dependencies index the
    rows after it, so no dependency cycle can be written.

    [mem], [Dep], [Reach] and [Respects] are [Prop] here, where Agda's are
    [Set] ([_⊎_] and [⊥] become [\/] and [False]). They occur only as
    hypotheses, or, for [Respects], as a record whose fields conclude in
    equations, so no statement changes strength. [Reach] takes its starting
    row as an index, not a parameter. *)

(** Agda's [map], by the same two equations. *)
Fixpoint map_list {A B : Type} (f : A -> B) (xs : list A) : list B :=
  match xs with
  | nil => nil
  | cons x xs => cons (f x) (map_list f xs)
  end.

(** [_∈_], by recursion on the list. *)
Fixpoint mem (j : nat) (ks : list nat) : Prop :=
  match ks with
  | nil => False
  | cons k ks => j = k \/ mem j ks
  end.

(** [⨅]: the meet of a list of statuses; the empty meet is [proven]. *)
Fixpoint meet_all (ss : list Status) : Status :=
  match ss with
  | nil => proven
  | cons s ss => emeet s (meet_all ss)
  end.

Lemma meet_all_lower : forall (f : nat -> Status) js j,
  mem j js -> Le Evidence (meet_all (map_list f js)) (f j).
Proof.
  intros f js; induction js as [|k ks IH]; intros j p; simpl in p.
  - destruct p.
  - destruct p as [e|p].
    + subst j. apply emeet_lowerl.
    + eapply le_trans; [apply emeet_lowerr | exact (IH j p)].
Qed.

Lemma meet_all_greatest : forall (f : nat -> Status) z js,
  (forall j, mem j js -> Le Evidence z (f j)) -> Le Evidence z (meet_all (map_list f js)).
Proof.
  intros f z js; induction js as [|k ks IH]; intro h; simpl.
  - apply le_proven.
  - apply emeet_greatest.
    + apply h. left. reflexivity.
    + apply IH. intros j p. apply h. right. exact p.
Qed.

Record Row : Type := row {
  own  : Status;      (* the §5 token of the row's own artefact *)
  deps : list nat     (* the rows it depends on, as indices into the rows after it *)
}.

Definition Ledger : Type := list Row.

Fixpoint own_of (L : Ledger) (i : nat) : Status :=
  match L, i with
  | nil, _ => proven
  | cons r _, 0 => own r
  | cons _ L, S i => own_of L i
  end.

(** [Dep L i j]: row [i] depends directly on row [j]. *)
Fixpoint Dep (L : Ledger) (i j : nat) : Prop :=
  match L, i, j with
  | nil, _, _ => False
  | cons _ _, 0, 0 => False
  | cons r _, 0, S j => mem j (deps r)
  | cons _ _, S _, 0 => False
  | cons _ L, S i, S j => Dep L i j
  end.

(** [Reach L i j]: row [i] depends on row [j] through zero or more steps. *)
Inductive Reach (L : Ledger) : nat -> nat -> Prop :=
  | stay : forall i, Reach L i i
  | step : forall i k j, Dep L i k -> Reach L k j -> Reach L i j.

(** The derived status. *)
Fixpoint eff (L : Ledger) (i : nat) {struct L} : Status :=
  match L, i with
  | nil, _ => proven
  | cons r L', 0 => emeet (own r) (meet_all (map_list (eff L') (deps r)))
  | cons _ L', S i => eff L' i
  end.

(** E-2: never stronger than the row's own evidence. *)
Lemma eff_le_own : forall L i, Le Evidence (eff L i) (own_of L i).
Proof.
  induction L as [|r L IH]; intros [|i]; simpl.
  - apply le_refl.
  - apply le_refl.
  - apply emeet_lowerl.
  - apply IH.
Qed.

(** E-2: nor than any row it depends on. *)
Lemma eff_le_dep : forall L i j, Dep L i j -> Le Evidence (eff L i) (eff L j).
Proof.
  induction L as [|r L IH]; intros [|i] [|j] d; simpl in d |- *; try contradiction.
  - eapply le_trans; [apply emeet_lowerr | exact (meet_all_lower (eff L) (deps r) j d)].
  - exact (IH i j d).
Qed.

(** E-2: a row is only as strong as the weakest step it depends on. *)
Lemma eff_le_reach : forall L i j, Reach L i j -> Le Evidence (eff L i) (own_of L j).
Proof.
  intros L i j r. induction r as [i|i k j d r IH].
  - apply eff_le_own.
  - eapply le_trans; [exact (eff_le_dep L i k d) | exact IH].
Qed.

(** An assignment respects a ledger when no row is stronger than its own
    evidence or than a row it depends on. *)
Record Respects (L : Ledger) (s : nat -> Status) : Prop := {
  below_own : forall i, Le Evidence (s i) (own_of L i);
  below_dep : forall i j, Dep L i j -> Le Evidence (s i) (s j)
}.

(** E-3 *)
Lemma eff_respects : forall L, Respects L (eff L).
Proof. intro L. split; [apply eff_le_own | apply eff_le_dep]. Qed.

(** Restricting an assignment of [r :: L] to [L] keeps it respectful. *)
Lemma restrict : forall r L s, Respects (cons r L) s -> Respects L (fun i => s (S i)).
Proof.
  intros r L s rho. split.
  - intro i. exact (below_own rho (S i)).
  - intros i j d. exact (below_dep rho (S i) (S j) d).
Qed.

(** E-3: every assignment that respects the ledger is below [eff]. *)
Lemma eff_greatest : forall L s, Respects L s -> forall i, Le Evidence (s i) (eff L i).
Proof.
  induction L as [|r L IH]; intros s rho [|i]; simpl.
  - apply le_proven.
  - apply le_proven.
  - apply emeet_greatest.
    + exact (below_own rho 0).
    + apply meet_all_greatest. intros j p.
      eapply le_trans.
      * exact (below_dep rho 0 (S j) p).
      * exact (IH (fun k => s (S k)) (restrict rho) j).
  - exact (IH (fun k => s (S k)) (restrict rho) i).
Qed.

(** The worked ledger of [tests/unit/EvidenceTest.agda], with its expected
    values. They pin the chain order, which the laws above cannot see. *)

Lemma sequence_keeps_the_weaker : rmul Evidence argued testedOnly = testedOnly.
Proof. reflexivity. Qed.

Lemma alternative_keeps_the_stronger : radd Evidence argued testedOnly = argued.
Proof. reflexivity. Qed.

Lemma provenWithPostulates_below_proven :
  rmul Evidence proven provenWithPostulates = provenWithPostulates.
Proof. reflexivity. Qed.

Lemma open_annihilates : rmul Evidence proven openRow = openRow.
Proof. reflexivity. Qed.

(** Newest first; indices count back from each row. *)
Definition example_ledger : Ledger :=
  cons (row proven (cons 0 (cons 1 nil)))       (* row 4: on row 3 and row 2 *)
  (cons (row testedOnly nil)                   (* row 3 *)
  (cons (row proven (cons 0 (cons 1 nil)))      (* row 2: on row 1 and row 0 *)
  (cons (row argued nil)                        (* row 1 *)
  (cons (row proven nil)                        (* row 0 *)
   nil)))).

Lemma row2_is_argued : eff example_ledger 2 = argued.
Proof. reflexivity. Qed.

Lemma row4_is_tested_only : eff example_ledger 0 = testedOnly.
Proof. reflexivity. Qed.

Lemma row0_keeps_its_evidence : eff example_ledger 4 = proven.
Proof. reflexivity. Qed.

(** * Parallel composition (P-1 .. P-4)

    A second, commutative product on the same unit, distributing over
    alternatives. Which way it exchanges with sequence depends on the
    resource, so the two exchange laws are stated apart. *)

Record IsParallel (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) : Prop := {
  par_assoc    : forall a b c, par (par a b) c = par a (par b c);
  par_comm     : forall a b, par a b = par b a;
  par_unitl    : forall a, par (rone R) a = a;
  par_distribl : forall a b c, par a (radd R b c) = radd R (par a b) (par a c)
}.

(** P-1: the derived right unit, right distributivity and monotonicity. *)
Lemma par_unitr (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) :
  IsParallel R par -> forall a, par a (rone R) = a.
Proof. intros P a. rewrite (par_comm P a (rone R)). apply (par_unitl P). Qed.

Lemma par_distribr (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) :
  IsParallel R par ->
  forall a b c, par (radd R a b) c = radd R (par a c) (par b c).
Proof.
  intros P a b c.
  rewrite (par_comm P (radd R a b) c), (par_distribl P c a b),
    (par_comm P c a), (par_comm P c b).
  reflexivity.
Qed.

Lemma par_mono_l (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) :
  IsParallel R par -> forall c a b, Le R a b -> Le R (par c a) (par c b).
Proof.
  unfold Le; intros P c a b p. rewrite <- (par_distribl P c a b), p. reflexivity.
Qed.

Lemma par_mono_r (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) :
  IsParallel R par -> forall c a b, Le R a b -> Le R (par a c) (par b c).
Proof.
  unfold Le; intros P c a b p. rewrite <- (@par_distribr R par P a b c), p. reflexivity.
Qed.

(** The two exchange laws. [SyncBelow]: threads that meet in the middle are
    graded at most as threads that run free. [SyncAbove]: at least. *)
Definition SyncBelow (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) : Prop :=
  forall a b c d, Le R (rmul R (par a b) (par c d)) (par (rmul R a c) (rmul R b d)).

Definition SyncAbove (R : ResourceAlgebra) (par : Grade R -> Grade R -> Grade R) : Prop :=
  forall a b c d, Le R (par (rmul R a c) (rmul R b d)) (rmul R (par a b) (par c d)).

(** P-1: a dioid with a commutative sequence is parallel with ∥ = ⊗, and
    has both exchange laws. *)
Lemma seq_parallel (R : ResourceAlgebra) :
  IsDioid R -> (forall a b, rmul R a b = rmul R b a) -> IsParallel R (rmul R).
Proof.
  intros D mc. split.
  - apply (seq_assoc (rseq R)).
  - exact mc.
  - apply (seq_unitl (rseq R)).
  - apply (distribl D).
Qed.

Lemma mul_interchange (R : ResourceAlgebra) :
  (forall a b, rmul R a b = rmul R b a) ->
  forall a b c d,
    rmul R (rmul R a b) (rmul R c d) = rmul R (rmul R a c) (rmul R b d).
Proof.
  intros mc a b c d.
  rewrite (seq_assoc (rseq R) a b (rmul R c d)),
    <- (seq_assoc (rseq R) b c d), (mc b c),
    (seq_assoc (rseq R) c b d), <- (seq_assoc (rseq R) a c (rmul R b d)).
  reflexivity.
Qed.

Lemma seq_sync_below (R : ResourceAlgebra) :
  (forall a b, rmul R a b = rmul R b a) -> SyncBelow R (rmul R).
Proof.
  intros mc a b c d. rewrite (@mul_interchange R mc a b c d). apply le_refl.
Qed.

Lemma seq_sync_above (R : ResourceAlgebra) :
  (forall a b, rmul R a b = rmul R b a) -> SyncAbove R (rmul R).
Proof.
  intros mc a b c d. rewrite (@mul_interchange R mc a b c d). apply le_refl.
Qed.

(** P-2: work. Loss and MaxPlus, parallel = sequence. *)
Lemma lplus_comm : forall a b, lplus a b = lplus b a.
Proof. intros; grades. Qed.

Lemma Loss_parallel : IsParallel Loss lplus.
Proof. exact (@seq_parallel Loss Loss_dioid lplus_comm). Qed.

Lemma Loss_sync_below : SyncBelow Loss lplus.
Proof. exact (@seq_sync_below Loss lplus_comm). Qed.

Lemma Loss_sync_above : SyncAbove Loss lplus.
Proof. exact (@seq_sync_above Loss lplus_comm). Qed.

Lemma tMul_comm : forall a b, tMul a b = tMul b a.
Proof. intros; trops. Qed.

Lemma MaxPlus_work : IsParallel MaxPlus tMul.
Proof. exact (@seq_parallel MaxPlus MaxPlus_dioid tMul_comm). Qed.

Lemma MaxPlus_work_sync_below : SyncBelow MaxPlus tMul.
Proof. exact (@seq_sync_below MaxPlus tMul_comm). Qed.

Lemma MaxPlus_work_sync_above : SyncAbove MaxPlus tMul.
Proof. exact (@seq_sync_above MaxPlus tMul_comm). Qed.

(** P-3: span. MaxPlus, parallel = max on finite costs. *)
Definition tPar (a b : Tropical) : Tropical :=
  match a, b with
  | bot, _ => bot
  | val _, bot => bot
  | val m, val n => val (rmax m n)
  end.

Lemma MaxPlus_span : IsParallel MaxPlus tPar.
Proof. split; simpl; intros; trops. Qed.

Lemma MaxPlus_span_sync_above : SyncAbove MaxPlus tPar.
Proof. unfold SyncAbove, Le; simpl; intros; trops. Qed.

Lemma MaxPlus_span_not_sync_below : ~ SyncBelow MaxPlus tPar.
Proof.
  intro f. pose proof (f (val 1) (val 0) (val 0) (val 1)) as h.
  unfold Le in h; simpl in h. discriminate h.
Qed.

(** P-4: occupancy. HWM, parallel = sum of peaks and sum of drifts. *)
Definition parH (a b : HGrade) : HGrade.
Proof.
  refine (hwm (peak a + peak b) (drift a + drift b) _).
  destruct a, b; simpl; lia.
Defined.

Lemma HWM_parallel : IsParallel HWM parH.
Proof. split; simpl; intros; hwms. Qed.

Lemma HWM_sync_below : SyncBelow HWM parH.
Proof. unfold SyncBelow, Le; simpl; intros; hwms. Qed.

Lemma HWM_not_sync_above : ~ SyncAbove HWM parH.
Proof.
  intro f.
  pose proof (f_equal peak
    (f (hwm 1 0 (le_S 0 0 (le_n 0))) zeroH zeroH (hwm 1 0 (le_S 0 0 (le_n 0)))))
    as h.
  simpl in h. discriminate h.
Qed.

(** * The loop grade (K-1 .. K-4)

    [star a] is the grade of "a, any number of times": a fixed point of
    x ↦ 𝟙 ⊕ (a ⊗ x), and the least one on both sides (Kozen's axioms). *)

Record IsStar (R : ResourceAlgebra) (star : Grade R -> Grade R) : Prop := {
  star_unfold : forall a, radd R (rone R) (rmul R a (star a)) = star a;
  star_leastl : forall a b x,
    Le R (radd R b (rmul R a x)) x -> Le R (rmul R (star a) b) x;
  star_leastr : forall a b x,
    Le R (radd R b (rmul R x a)) x -> Le R (rmul R b (star a)) x
}.

(** K-1: the loop grade bounds no turn and one more turn. *)
Lemma star_one (R : ResourceAlgebra) (star : Grade R -> Grade R) :
  IsStar R star -> forall a, Le R (rone R) (star a).
Proof.
  intros S a. pose proof (@add_upperl R (rone R) (rmul R a (star a))) as h.
  rewrite (star_unfold S a) in h. exact h.
Qed.

Lemma star_step (R : ResourceAlgebra) (star : Grade R -> Grade R) :
  IsStar R star -> forall a, Le R (rmul R a (star a)) (star a).
Proof.
  intros S a. pose proof (@add_upperr R (rone R) (rmul R a (star a))) as h.
  rewrite (star_unfold S a) in h. exact h.
Qed.

(** K-1: if 𝟙 is the greatest grade, every loop grades as 𝟙. *)
Lemma unit_top_star (R : ResourceAlgebra) :
  (forall a, Le R a (rone R)) -> IsStar R (fun _ => rone R).
Proof.
  intro greatest. split.
  - intro a. rewrite (alt_comm (ralt R)). apply greatest.
  - intros a b x h. rewrite (seq_unitl (rseq R)).
    exact (@le_trans R _ _ _ (@add_upperl R b (rmul R a x)) h).
  - intros a b x h. rewrite (seq_unitr (rseq R)).
    exact (@le_trans R _ _ _ (@add_upperl R b (rmul R x a)) h).
Qed.

Lemma Loss_unit_top : forall a, Le Loss a (rone Loss).
Proof. unfold Le; simpl; intros; grades. Qed.

Lemma Loss_star : IsStar Loss (fun _ => fin 0).
Proof. exact (@unit_top_star Loss Loss_unit_top). Qed.

(** K-2: a grade whose loop equation has no solution rules a star out. *)
Definition NoFixpoint (R : ResourceAlgebra) (a : Grade R) : Prop :=
  forall s, radd R (rone R) (rmul R a s) <> s.

Lemma no_star (R : ResourceAlgebra) (a : Grade R) :
  NoFixpoint R a -> forall star, ~ IsStar R star.
Proof. intros nf star st. exact (nf (star a) (star_unfold st a)). Qed.

Lemma MaxPlus_no_fixpoint : NoFixpoint MaxPlus (val 1).
Proof.
  unfold NoFixpoint; intros s h. destruct s as [n|]; simpl in h.
  - apply val_injective in h. lia.
  - discriminate h.
Qed.

Lemma MaxPlus_no_star : forall star, ~ IsStar MaxPlus star.
Proof. exact (@no_star MaxPlus (val 1) MaxPlus_no_fixpoint). Qed.

Lemma HWM_no_fixpoint : NoFixpoint HWM (hwm 1 1 (le_n 1)).
Proof.
  unfold NoFixpoint; intros s h. pose proof (f_equal drift h) as e.
  destruct s; simpl in e. rewrite ?rmax_eq in e. lia.
Qed.

Lemma HWM_no_star : forall star, ~ IsStar HWM star.
Proof. exact (@no_star HWM (hwm 1 1 (le_n 1)) HWM_no_fixpoint). Qed.

(** K-3: MaxPlus with a top, (ℕ ∪ {−∞, +∞}, max, +). *)
Inductive TGrade : Type := tbot : TGrade | tval : nat -> TGrade | ttop : TGrade.

Definition taddT (a b : TGrade) : TGrade :=
  match a, b with
  | tbot, y => y
  | tval m, tbot => tval m
  | tval m, tval n => tval (rmax m n)
  | tval _, ttop => ttop
  | ttop, _ => ttop
  end.

Definition tmulT (a b : TGrade) : TGrade :=
  match a, b with
  | tbot, _ => tbot
  | tval _, tbot => tbot
  | tval m, tval n => tval (m + n)
  | tval _, ttop => ttop
  | ttop, tbot => tbot
  | ttop, _ => ttop
  end.

Ltac tops :=
  repeat match goal with
         | a : TGrade |- _ => destruct a
         end;
  simpl; unfold_rmm; try reflexivity;
  try (f_equal; lia).

Lemma MaxPlusTop_alt : IsAltMonoid taddT tbot.
Proof. split; intros; tops. Qed.

Lemma MaxPlusTop_seq : IsSeqMonoid tmulT (tval 0).
Proof. split; intros; tops. Qed.

Definition MaxPlusTop : ResourceAlgebra :=
  {| Grade := TGrade; radd := taddT; rmul := tmulT; rzero := tbot; rone := tval 0;
     ralt := MaxPlusTop_alt; rseq := MaxPlusTop_seq |}.

Lemma MaxPlusTop_dioid : IsDioid MaxPlusTop.
Proof. split; simpl; intros; tops. Qed.

Lemma MaxPlusTop_ordered : IsOrdered MaxPlusTop.
Proof. exact (dioid_ordered MaxPlusTop_dioid). Qed.

Lemma MaxPlusTop_annihilating : IsAnnihilating MaxPlusTop.
Proof. split; simpl; intros; tops. Qed.

(** K-3: MaxPlus embeds in it by a strict, injective morphism. *)
Definition liftT (a : Tropical) : TGrade :=
  match a with
  | val n => tval n
  | bot => tbot
  end.

Definition lift_hom : Hom MaxPlus MaxPlusTop.
Proof.
  refine (@Build_Hom MaxPlus MaxPlusTop liftT _ _ _ _); simpl;
    try reflexivity; intros a b; destruct a, b; reflexivity.
Defined.

Lemma lift_injective : forall a b, liftT a = liftT b -> a = b.
Proof.
  intros [m|] [n|] h; simpl in h; try discriminate h; try reflexivity.
  injection h as h. now subst.
Qed.

(** K-4: its star. bot and val 0 loop for nothing; a dearer body loops to
    top. *)
Definition starT (a : TGrade) : TGrade :=
  match a with
  | tbot => tval 0
  | tval 0 => tval 0
  | tval (S _) => ttop
  | ttop => ttop
  end.

Ltac star_case h :=
  simpl in *; try reflexivity; try assumption; try discriminate h;
  try (injection h as h; rewrite ?rmax_eq in h;
       first [ f_equal; rewrite ?rmax_eq; lia | exfalso; lia ]).

Lemma MaxPlusTop_star : IsStar MaxPlusTop starT.
Proof.
  split; unfold Le; simpl.
  - intros [|[|n]|]; reflexivity.
  - intros a b x h.
    destruct a as [|[|n]|], b as [|m|], x as [|k|]; star_case h.
  - intros a b x h.
    destruct a as [|[|n]|], b as [|m|], x as [|k|]; star_case h.
Qed.

(** * Signed drift (D-1 .. D-8)

    The drift carrier is the integers with a bottom, [ninf], under max and
    + (Agda: Drift.agda). Agda builds its own integers as differences of
    naturals; here they are the standard library's [Z] and the arithmetic
    is [lia]. The carrier, its operations and the bound are the same
    definitions. The bound [drift ≤ peak] is a boolean here ([dleb]), so
    its proofs are unique by [Eqdep_dec.UIP_dec] (a theorem); Agda's is a
    relation defined by recursion, unique by recursion. *)

Inductive Drift : Type := ninf : Drift | dfin : Z -> Drift.

Definition dadd (a b : Drift) : Drift :=
  match a, b with
  | dfin x, dfin y => dfin (x + y)%Z
  | _, _ => ninf
  end.

Definition dmax (a b : Drift) : Drift :=
  match a, b with
  | ninf, b => b
  | a, ninf => a
  | dfin x, dfin y => dfin (Z.max x y)
  end.

Definition dzero : Drift := dfin 0%Z.

(** A natural as a drift, and the natural part of a drift (0 below zero). *)
Definition pkd (n : nat) : Drift := dfin (Z.of_nat n).

Definition dclamp (d : Drift) : nat :=
  match d with
  | ninf => 0
  | dfin z => Z.to_nat z
  end.

Ltac dcases :=
  repeat match goal with
         | d : Drift |- _ => destruct d
         end; simpl; try reflexivity; try (f_equal; lia).

Lemma dmax_comm : forall a b, dmax a b = dmax b a.
Proof. intros; dcases. Qed.

Lemma dadd_comm : forall a b, dadd a b = dadd b a.
Proof. intros; dcases. Qed.

Lemma Drift_alt : IsAltMonoid dmax ninf.
Proof. split; intros; dcases. Qed.

Lemma Drift_seq : IsSeqMonoid dadd dzero.
Proof. split; intros; dcases. Qed.

(** D-1: the drift carrier is the max-plus dioid on ℤ. *)
Definition Drift_RA : ResourceAlgebra :=
  {| Grade := Drift; radd := dmax; rmul := dadd; rzero := ninf; rone := dzero;
     ralt := Drift_alt; rseq := Drift_seq |}.

Lemma Drift_dioid : IsDioid Drift_RA.
Proof. split; simpl; intros; dcases. Qed.

(** The bound of a signed grade. *)
Definition dleb (d : Drift) (p : nat) : bool :=
  match d with
  | ninf => true
  | dfin z => Z.leb z (Z.of_nat p)
  end.

Record SGrade : Type := shwm {
  speak : nat;
  sdrift : Drift;
  sbounded : dleb sdrift speak = true
}.

Arguments shwm : clear implicits.

Lemma shwm_eq : forall a b : SGrade, speak a = speak b -> sdrift a = sdrift b -> a = b.
Proof.
  intros [p n bd] [p' n' bd'] e1 e2; simpl in *; subst.
  f_equal. apply Eqdep_dec.UIP_dec, Bool.bool_dec.
Qed.

(** Turn every bound into an inequality and every [Drift] into its cases,
    then [lia]. *)
Ltac sbounds :=
  repeat match goal with
         | a : SGrade |- _ => destruct a
         end;
  unfold pkd in *;
  repeat match goal with
         | d : Drift |- _ => destruct d
         end;
  simpl in *;
  repeat match goal with
         | h : Z.leb _ _ = true |- _ => apply Z.leb_le in h
         end;
  try apply Z.leb_le.

Ltac fin_goals :=
  unfold pkd in *; unfold_rmm; first [ reflexivity | lia | (f_equal; lia) ].

Ltac shwms := sbounds; apply shwm_eq; simpl; fin_goals.

Definition mulS (a b : SGrade) : SGrade.
Proof.
  refine (shwm (dclamp (dmax (pkd (speak a)) (dadd (sdrift a) (pkd (speak b)))))
               (dadd (sdrift a) (sdrift b)) _).
  sbounds; try reflexivity; lia.
Defined.

Definition addS (a b : SGrade) : SGrade.
Proof.
  refine (shwm (rmax (speak a) (speak b)) (dmax (sdrift a) (sdrift b)) _).
  sbounds; rewrite ?rmax_eq; try reflexivity; try lia.
Defined.

Definition zeroS : SGrade := shwm 0 ninf eq_refl.
Definition oneS : SGrade := shwm 0 dzero eq_refl.

(** D-1 *)
Lemma SHWM_alt : IsAltMonoid addS zeroS.
Proof. split; intros; shwms. Qed.

Lemma SHWM_seq : IsSeqMonoid mulS oneS.
Proof. split; intros; shwms. Qed.

Definition SHWM : ResourceAlgebra :=
  {| Grade := SGrade; radd := addS; rmul := mulS; rzero := zeroS; rone := oneS;
     ralt := SHWM_alt; rseq := SHWM_seq |}.

Lemma SHWM_dioid : IsDioid SHWM.
Proof. split; simpl; intros; shwms. Qed.

Lemma SHWM_ordered : IsOrdered SHWM.
Proof. exact (dioid_ordered SHWM_dioid). Qed.

(** D-2: 𝟘 is not 𝟙; 𝟘 absorbs on the left; on the right it keeps the
    peak, so SHWM is not annihilating. *)
Lemma SHWM_zero_ne_one : rzero SHWM <> rone SHWM.
Proof. intro h. pose proof (f_equal sdrift h) as e. discriminate e. Qed.

Lemma SHWM_absorbl : forall a, mulS zeroS a = zeroS.
Proof. intros; shwms. Qed.

Lemma SHWM_seq_zero : forall a, mulS a zeroS = shwm (speak a) ninf eq_refl.
Proof. intros; shwms. Qed.

Lemma SHWM_not_annihilating : ~ IsAnnihilating SHWM.
Proof.
  intro z. pose proof (f_equal speak (annihilr z (shwm 1 dzero eq_refl))) as h.
  simpl in h. discriminate h.
Qed.

(** D-4: in HWM a prefix keeps the peak; with consumption it can lower it. *)
Lemma HWM_prefix_keeps_peak : forall a b, peak b <= peak (mulH a b).
Proof. intros [p1 n1 b1] [p2 n2 b2]; simpl; rewrite rmax_eq; lia. Qed.

Definition free_one : SGrade := shwm 0 (dfin (-1)%Z) eq_refl.
Definition alloc_one : SGrade := shwm 1 (pkd 1) eq_refl.

Lemma prefix_lowers_peak : ~ (forall a b, speak b <= speak (mulS a b)).
Proof. intro f. pose proof (f free_one alloc_one) as h. simpl in h. lia. Qed.

(** D-3: HWM inside SHWM, and back. *)
Definition embed (a : HGrade) : SGrade.
Proof.
  refine (shwm (peak a) (pkd (drift a)) _).
  destruct a; simpl; apply Z.leb_le; lia.
Defined.

Definition clampG (a : SGrade) : HGrade.
Proof.
  refine (hwm (speak a) (dclamp (dmax (pkd 0) (sdrift a))) _).
  sbounds; lia.
Defined.

Lemma embed_mul : forall a b, embed (mulH a b) = mulS (embed a) (embed b).
Proof. intros [p1 n1 b1] [p2 n2 b2]; apply shwm_eq; simpl; fin_goals. Qed.

Lemma embed_add : forall a b, embed (addH a b) = addS (embed a) (embed b).
Proof. intros [p1 n1 b1] [p2 n2 b2]; apply shwm_eq; simpl; fin_goals. Qed.

Definition embed_lax : LaxHom HWM SHWM.
Proof.
  refine (@Build_LaxHom HWM SHWM embed _ embed_add _).
  - apply shwm_eq; reflexivity.
  - intros a b. simpl. rewrite embed_mul. apply le_refl.
Defined.

Lemma embed_injective : forall a b, embed a = embed b -> a = b.
Proof.
  intros [p n bd] [p' n' bd'] e. apply hwm_eq.
  - exact (f_equal speak e).
  - pose proof (f_equal sdrift e) as h. simpl in h. unfold pkd in h. injection h. simpl. lia.
Qed.

Lemma embed_zero : embed zeroH <> zeroS.
Proof. intro h. pose proof (f_equal sdrift h) as e. discriminate e. Qed.

Lemma no_strict_HWM_SHWM : Hom HWM SHWM -> False.
Proof. apply no_strict_from_HWM. exact SHWM_zero_ne_one. Qed.

Lemma clamp_embed : forall a, clampG (embed a) = a.
Proof. intros [p n bd]; apply hwm_eq; simpl; fin_goals. Qed.

Definition clamp_lax : LaxHom SHWM HWM.
Proof.
  refine (@Build_LaxHom SHWM HWM clampG _ _ _).
  - apply hwm_eq; reflexivity.
  - intros [p n bd] [p' n' bd']; apply hwm_eq; sbounds; fin_goals.
  - intros [p n bd] [p' n' bd']; unfold Le; simpl; apply hwm_eq; sbounds; fin_goals.
Defined.

Lemma clamp_not_strict :
  ~ (forall a b, clampG (mulS a b) = mulH (clampG a) (clampG b)).
Proof.
  intro f. pose proof (f_equal peak (f free_one alloc_one)) as h.
  simpl in h. discriminate h.
Qed.

(** D-7: the peak is lax into MaxPlus, and agrees with HWM's on HWM. *)
Definition speak_lax : LaxHom SHWM MaxPlus.
Proof.
  refine (@Build_LaxHom SHWM MaxPlus (fun g : SGrade => val (speak g)) _ _ _).
  - reflexivity.
  - intros [p n bd] [p' n' bd']; reflexivity.
  - intros [p n bd] [p' n' bd']; unfold Le; simpl; sbounds; fin_goals.
Defined.

Lemma speak_embed : forall a, speak (embed a) = peak a.
Proof. reflexivity. Qed.

(** D-5: parallel = sum of peaks and sum of drifts. *)
Definition parS (a b : SGrade) : SGrade.
Proof.
  refine (shwm (speak a + speak b) (dadd (sdrift a) (sdrift b)) _).
  sbounds; try reflexivity; lia.
Defined.

Lemma SHWM_parallel : IsParallel SHWM parS.
Proof. split; simpl; intros; shwms. Qed.

Lemma SHWM_sync_below : SyncBelow SHWM parS.
Proof. unfold SyncBelow, Le; simpl; intros; shwms. Qed.

Lemma SHWM_not_sync_above : ~ SyncAbove SHWM parS.
Proof.
  intro f.
  pose proof (f_equal speak (f (shwm 1 dzero eq_refl) oneS oneS (shwm 1 dzero eq_refl))) as h.
  simpl in h. discriminate h.
Qed.

(** D-6: no star. *)
Lemma SHWM_no_fixpoint : NoFixpoint SHWM (shwm 1 (pkd 1) eq_refl).
Proof.
  unfold NoFixpoint; intros s h. pose proof (f_equal speak h) as e.
  destruct s as [p n bd].
  change (rmax 0 (Z.to_nat (Z.max (Z.of_nat 1) (Z.of_nat 1 + Z.of_nat p))) = p) in e.
  rewrite rmax_eq in e. lia.
Qed.

Lemma SHWM_no_star : forall star, ~ IsStar SHWM star.
Proof. exact (@no_star SHWM (shwm 1 (pkd 1) eq_refl) SHWM_no_fixpoint). Qed.

(** D-8: the bicyclic monoid. [bic (a, b)] is the grade of peak [a] and
    drift [a − b]. *)
Definition bmul (x y : nat * nat) : nat * nat :=
  let (a, b) := x in let (c, d) := y in (a + (c - b), d + (b - c)).

Definition bic (x : nat * nat) : SGrade.
Proof.
  refine (shwm (fst x) (dfin (Z.of_nat (fst x) - Z.of_nat (snd x))) _).
  destruct x; simpl; apply Z.leb_le; lia.
Defined.

Lemma bic_one : bic (0, 0) = oneS.
Proof. apply shwm_eq; reflexivity. Qed.

Lemma bic_mul : forall x y, bic (bmul x y) = mulS (bic x) (bic y).
Proof.
  intros [a b] [c d]; apply shwm_eq; simpl; try (f_equal; lia); lia.
Qed.

Lemma bic_injective : forall x y, bic x = bic y -> x = y.
Proof.
  intros [a b] [c d] e.
  pose proof (f_equal speak e) as e1. pose proof (f_equal sdrift e) as e2.
  simpl in e1, e2. injection e2; intro. f_equal; lia.
Qed.

Definition Finite (g : SGrade) : Prop :=
  match sdrift g with ninf => False | dfin _ => True end.

Definition bic_onto : forall g, Finite g -> { x : nat * nat | bic x = g }.
Proof.
  intros [p [|z] bd] h; simpl in h; [contradiction|].
  simpl in bd. pose proof (proj1 (Z.leb_le _ _) bd) as q.
  exists (p, Z.to_nat (Z.of_nat p - z)). apply shwm_eq; simpl; try reflexivity.
  f_equal. lia.
Defined.

Lemma bic_HWM : forall a, bic (peak a, peak a - drift a) = embed a.
Proof. intros [p n bd]; apply shwm_eq; simpl; fin_goals. Qed.

Definition HWM_bic : forall a b, b <= a -> { h : HGrade | embed h = bic (a, b) }.
Proof.
  intros a b q. exists (hwm a (a - b) (Nat.le_sub_l a b)).
  apply shwm_eq; simpl; fin_goals.
Defined.

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
Print Assumptions Diamond_ordered.
Print Assumptions Diamond_annihilating.
Print Assumptions Diamond_not_dioid.
Print Assumptions ordered_annihilating_not_dioid.
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
Print Assumptions Evidence.
Print Assumptions Evidence_dioid.
Print Assumptions Evidence_ordered.
Print Assumptions Evidence_annihilating.
Print Assumptions le_to_rank.
Print Assumptions rank_to_le.
Print Assumptions le_proven.
Print Assumptions emeet_lowerl.
Print Assumptions emeet_lowerr.
Print Assumptions emeet_greatest.
Print Assumptions eff_le_own.
Print Assumptions eff_le_dep.
Print Assumptions eff_le_reach.
Print Assumptions eff_respects.
Print Assumptions restrict.
Print Assumptions eff_greatest.
Print Assumptions sequence_keeps_the_weaker.
Print Assumptions alternative_keeps_the_stronger.
Print Assumptions provenWithPostulates_below_proven.
Print Assumptions open_annihilates.
Print Assumptions row2_is_argued.
Print Assumptions row4_is_tested_only.
Print Assumptions row0_keeps_its_evidence.
Print Assumptions par_unitr.
Print Assumptions par_distribr.
Print Assumptions par_mono_l.
Print Assumptions par_mono_r.
Print Assumptions seq_parallel.
Print Assumptions seq_sync_below.
Print Assumptions seq_sync_above.
Print Assumptions Loss_parallel.
Print Assumptions Loss_sync_below.
Print Assumptions Loss_sync_above.
Print Assumptions MaxPlus_work.
Print Assumptions MaxPlus_work_sync_below.
Print Assumptions MaxPlus_work_sync_above.
Print Assumptions MaxPlus_span.
Print Assumptions MaxPlus_span_sync_above.
Print Assumptions MaxPlus_span_not_sync_below.
Print Assumptions HWM_parallel.
Print Assumptions HWM_sync_below.
Print Assumptions HWM_not_sync_above.
Print Assumptions star_one.
Print Assumptions star_step.
Print Assumptions unit_top_star.
Print Assumptions Loss_star.
Print Assumptions no_star.
Print Assumptions MaxPlus_no_star.
Print Assumptions HWM_no_star.
Print Assumptions MaxPlusTop_dioid.
Print Assumptions MaxPlusTop_annihilating.
Print Assumptions lift_hom.
Print Assumptions lift_injective.
Print Assumptions MaxPlusTop_star.
Print Assumptions Drift_dioid.
Print Assumptions SHWM.
Print Assumptions SHWM_dioid.
Print Assumptions SHWM_ordered.
Print Assumptions SHWM_zero_ne_one.
Print Assumptions SHWM_absorbl.
Print Assumptions SHWM_seq_zero.
Print Assumptions SHWM_not_annihilating.
Print Assumptions HWM_prefix_keeps_peak.
Print Assumptions prefix_lowers_peak.
Print Assumptions embed_lax.
Print Assumptions embed_mul.
Print Assumptions embed_injective.
Print Assumptions embed_zero.
Print Assumptions no_strict_HWM_SHWM.
Print Assumptions clamp_lax.
Print Assumptions clamp_embed.
Print Assumptions clamp_not_strict.
Print Assumptions speak_lax.
Print Assumptions speak_embed.
Print Assumptions SHWM_parallel.
Print Assumptions SHWM_sync_below.
Print Assumptions SHWM_not_sync_above.
Print Assumptions SHWM_no_fixpoint.
Print Assumptions SHWM_no_star.
Print Assumptions bic_one.
Print Assumptions bic_mul.
Print Assumptions bic_injective.
Print Assumptions bic_onto.
Print Assumptions bic_HWM.
Print Assumptions HWM_bic.
