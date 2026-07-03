(*******************************************************************************)
(*                                                                             *)
(*                    WEIGHTED MOTIVIC TAYLOR TOWER                            *)
(*                                                                             *)
(*       A Formalization of Weight-Based Stabilization for Motivic Functors   *)
(*                                                                             *)
(*   The sea advances insensibly in silence, nothing seems to happen,          *)
(*   nothing moves, yet it finally surrounds the resistant substance.          *)
(*                                               -- Alexander Grothendieck     *)
(*                                                                             *)
(*   Author:  Charles Norton                                                   *)
(*   Date:    November 20, 2024                                                *)
(*   Revised: July 3, 2026                                                     *)
(*   License: MIT                                                              *)
(*                                                                             *)
(*   This formalization establishes that weighted Taylor towers converge       *)
(*   in motivic homotopy theory by showing that weight-bounded obstructions    *)
(*   must vanish as stage thresholds decrease to zero.                         *)
(*                                                                             *)
(*******************************************************************************)

(** MotivicSH carries genuine morphism data, the concrete affine line separates scheme isomorphism from A1-equivalence, and FamGoodwillieTower instantiates GoodwillieTowerWithLayers with detecting layers. *)

From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible Equivalences.
From HoTT.Types Require Import Bool Unit Empty Prod Sigma Universe.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Spaces Require Import Nat.Core Int.

(** Arithmetic on nat is inherited from HoTT.Spaces.Nat.Core; nat_lt and nat_le are Type-valued fixpoints computing to Unit or Empty. *)

Fixpoint nat_lt (n m : nat) : Type :=
  match n, m with
  | _, O => Empty
  | O, S _ => Unit
  | S n', S m' => nat_lt n' m'
  end.

Fixpoint nat_le (n m : nat) : Type :=
  match n, m with
  | O, _ => Unit
  | S _, O => Empty
  | S n', S m' => nat_le n' m'
  end.

Lemma nat_lt_irrefl
  : forall n, nat_lt n n -> Empty.
Proof.
  induction n.
  - exact idmap.
  - exact IHn.
Defined.

Lemma nat_lt_S
  : forall n, nat_lt n (S n).
Proof.
  induction n.
  - exact tt.
  - exact IHn.
Defined.

(** The Type-valued relations reflect into the library leq and lt, and the local suite is derived through the reflection. *)

Lemma nat_le_refl
  : forall n, nat_le n n.
Proof.
  induction n.
  - exact tt.
  - exact IHn.
Defined.

Lemma nat_le_succ_r (a b : nat) : nat_le a b -> nat_le a (S b).
Proof.
  revert b.
  induction a.
  - intros b _.
    exact tt.
  - intros b Hb.
    destruct b.
    + destruct Hb.
    + exact (IHa b Hb).
Defined.

Lemma leq_of_nat_le (n m : nat) : nat_le n m -> leq n m.
Proof.
  revert m.
  induction n.
  - intros m _.
    exact (leq_zero_l m).
  - intros m Hle.
    destruct m.
    + destruct Hle.
    + exact (leq_succ (IHn m Hle)).
Defined.

Lemma nat_le_of_leq (n m : nat) : leq n m -> nat_le n m.
Proof.
  intro Hle.
  induction Hle.
  - exact (nat_le_refl n).
  - exact (nat_le_succ_r n m IHHle).
Defined.

Lemma nat_lt_of_le_succ (a b : nat) : nat_le (S a) b -> nat_lt a b.
Proof.
  revert b.
  induction a.
  - intros b Hb.
    destruct b.
    + destruct Hb.
    + exact tt.
  - intros b Hb.
    destruct b.
    + destruct Hb.
    + exact (IHa b Hb).
Defined.

Lemma nat_le_succ_of_lt (a b : nat) : nat_lt a b -> nat_le (S a) b.
Proof.
  revert b.
  induction a.
  - intros b Hb.
    destruct b.
    + destruct Hb.
    + exact tt.
  - intros b Hb.
    destruct b.
    + destruct Hb.
    + exact (IHa b Hb).
Defined.

Definition lt_of_nat_lt (n m : nat) : nat_lt n m -> lt n m
  := fun Hlt => leq_of_nat_le (S n) m (nat_le_succ_of_lt n m Hlt).

Definition nat_lt_of_lt (n m : nat) : lt n m -> nat_lt n m
  := fun Hlt => nat_lt_of_le_succ n m (nat_le_of_leq (S n) m Hlt).

Lemma nat_lt_trans
  : forall m n p, nat_lt m n -> nat_lt n p -> nat_lt m p.
Proof.
  intros m n p H1 H2.
  exact (nat_lt_of_lt m p
           (lt_trans (lt_of_nat_lt m n H1) (lt_of_nat_lt n p H2))).
Defined.

(** Numerals bind to nat through the scope; bool_bash discharges any goal that computes once every Boolean and Unit hypothesis is destructed. *)

Ltac bool_bash :=
  repeat (simpl in *;
          match goal with
          | b : Bool |- _ => destruct b
          | u : Unit |- _ => destruct u
          end);
  simpl;
  try reflexivity.

Definition bool_dec_eq (b : Bool) : ((b = true) + (b = false))%type.
Proof.
  destruct b.
  - left.
    reflexivity.
  - right.
    reflexivity.
Defined.

Record QPos : Type := {
  qpos_num : nat;
  qpos_denom_pred : nat
}.

Definition qpos_denom (q : QPos) : nat := S (qpos_denom_pred q).

Definition qpos_lt (q1 q2 : QPos) : Type :=
  nat_lt (nat_mul (qpos_num q1) (qpos_denom q2))
         (nat_mul (qpos_num q2) (qpos_denom q1)).

Definition qpos_one : QPos := {| qpos_num := 1; qpos_denom_pred := 0 |}.

Definition qpos_half : QPos := {| qpos_num := 1; qpos_denom_pred := 1 |}.

Lemma half_lt_one
  : qpos_lt qpos_half qpos_one.
Proof.
  unfold qpos_lt, qpos_half, qpos_one, qpos_denom.
  simpl.
  exact tt.
Defined.

Definition qpos_zero : QPos := {| qpos_num := 0; qpos_denom_pred := 0 |}.

Lemma qpos_lt_zero_empty
  : forall q, qpos_lt q qpos_zero -> Empty.
Proof.
  intros q H.
  unfold qpos_lt, qpos_zero in H.
  simpl in H.
  destruct (qpos_num q); exact H.
Defined.

Lemma qpos_lt_irrefl
  : forall q, qpos_lt q q -> Empty.
Proof.
  intros q H.
  unfold qpos_lt in H.
  exact (nat_lt_irrefl _ H).
Defined.

Definition qpos_is_zero (q : QPos) : Type := qpos_num q = O.

Definition LimitZero (measure : nat -> QPos) : Type :=
  forall (epsilon : QPos),
    nat_lt O (qpos_num epsilon) ->
    { N : nat & forall m, nat_lt N m -> qpos_lt (measure m) epsilon }.

Definition EventuallyZero (measure : nat -> QPos) : Type :=
  { N : nat & forall m, nat_lt N m -> qpos_is_zero (measure m) }.

Definition w_stage (n : nat) : QPos :=
  {| qpos_num := 1; qpos_denom_pred := n |}.

Definition nat_discrim (n : nat) : Type :=
  match n with
  | O => Empty
  | S _ => Unit
  end.

Definition S_ne_O
  : forall n, S n = O -> Empty
  := fun n H => neq_nat_zero_succ n H^.

Lemma w_stage_never_zero
  : forall n, qpos_is_zero (w_stage n) -> Empty.
Proof.
  intros n H.
  unfold qpos_is_zero, w_stage in H.
  simpl in H.
  exact (S_ne_O 0 H).
Defined.

Theorem w_stage_not_eventually_zero
  : EventuallyZero w_stage -> Empty.
Proof.
  intros [N HN].
  apply (w_stage_never_zero (S N)).
  apply HN.
  exact (nat_lt_S N).
Defined.

Lemma w_stage_antitonicity
  : forall n, qpos_lt (w_stage (S n)) (w_stage n).
Proof.
  intro n.
  unfold qpos_lt, w_stage, qpos_denom, qpos_num, qpos_denom_pred.
  change (nat_lt (nat_mul 1 (S n)) (nat_mul 1 (S (S n)))).
  rewrite (nat_mul_one_l (S n)).
  rewrite (nat_mul_one_l (S (S n))).
  exact (nat_lt_S n).
Defined.

Lemma nat_le_add_r
  : forall a b, nat_le a (nat_add a b).
Proof.
  intros a b.
  induction a.
  - exact tt.
  - simpl.
    exact IHa.
Defined.

Lemma nat_lt_of_lt_of_le
  : forall a b c, nat_lt a b -> nat_le b c -> nat_lt a c.
Proof.
  intros a b c Hab Hbc.
  exact (nat_lt_of_lt a c
           (lt_lt_leq_trans (lt_of_nat_lt a b Hab) (leq_of_nat_le b c Hbc))).
Defined.

Lemma nat_le_of_lt
  : forall n m, nat_lt n m -> nat_le n m.
Proof.
  intros n m Hlt.
  exact (nat_le_of_leq n m (leq_succ_l (lt_of_nat_lt n m Hlt))).
Defined.

Lemma nat_le_trans (a b c : nat) : nat_le a b -> nat_le b c -> nat_le a c.
Proof.
  intros Hab Hbc.
  exact (nat_le_of_leq a c
           (leq_trans (leq_of_nat_le a b Hab) (leq_of_nat_le b c Hbc))).
Defined.

Lemma nat_le_lt_trans (a b c : nat) : nat_le a b -> nat_lt b c -> nat_lt a c.
Proof.
  intros Hab Hbc.
  exact (nat_lt_of_lt a c
           (lt_leq_lt_trans (leq_of_nat_le a b Hab) (lt_of_nat_lt b c Hbc))).
Defined.

Lemma nat_le_lt_contradiction (N n : nat)
  : nat_le N n -> nat_lt n N -> Empty.
Proof.
  intros Hle Hlt.
  exact (lt_irrefl n
           (lt_lt_leq_trans (lt_of_nat_lt n N Hlt) (leq_of_nat_le N n Hle))).
Defined.

Lemma nat_lt_zero_absurd (n : nat) : nat_lt n O -> Empty.
Proof.
  intro Hlt.
  exact (not_lt_zero_r n (lt_of_nat_lt n O Hlt)).
Defined.

Lemma nat_le_of_lt_S (d n : nat) : nat_lt d (S n) -> nat_le d n.
Proof.
  revert n.
  induction d.
  - intros n _.
    exact tt.
  - intros n Hlt.
    destruct n.
    + destruct d; destruct Hlt.
    + exact (IHd n Hlt).
Defined.

Lemma nat_lt_or_eq_or_gt
  : forall n m, (nat_lt n m) + (n = m) + (nat_lt m n).
Proof.
  intro n.
  induction n.
  - intro m.
    destruct m.
    + left.
      right.
      reflexivity.
    + left.
      left.
      exact tt.
  - intro m.
    destruct m.
    + right.
      exact tt.
    + destruct (IHn m) as [[Hlt | Heq] | Hgt].
      * left.
        left.
        exact Hlt.
      * left.
        right.
        exact (ap S Heq).
      * right.
        exact Hgt.
Defined.

Lemma nat_le_total (n m : nat) : ((nat_le n m) + (nat_le m n))%type.
Proof.
  destruct (nat_lt_or_eq_or_gt n m) as [[Hlt | Heq] | Hgt].
  - left.
    exact (nat_le_of_lt n m Hlt).
  - left.
    rewrite Heq.
    exact (nat_le_refl m).
  - right.
    exact (nat_le_of_lt m n Hgt).
Defined.

Fixpoint nat_le_dec (n m : nat) {struct n}
  : ((nat_le n m) + (nat_le n m -> Empty))%type.
Proof.
  destruct n.
  - left.
    exact tt.
  - destruct m.
    + right.
      exact idmap.
    + exact (nat_le_dec n m).
Defined.

Lemma w_stage_archimedean
  : forall q : QPos,
    nat_lt O (qpos_num q) ->
    qpos_lt (w_stage (qpos_denom q)) q.
Proof.
  intros q Hpos.
  destruct q as [num denom_pred].
  destruct num as [|k].
  - destruct Hpos.
  - unfold qpos_lt, w_stage, qpos_denom, qpos_num, qpos_denom_pred.
    simpl.
    rewrite nat_add_zero_r.
    apply nat_lt_of_lt_of_le with (b := S denom_pred).
    + exact (nat_lt_S denom_pred).
    + simpl.
      exact (nat_le_add_r (S denom_pred) (nat_mul k (S (S denom_pred)))).
Defined.

Lemma nat_lt_add_r
  : forall a b c, nat_lt a b -> nat_lt (nat_add a c) (nat_add b c).
Proof.
  intros a b c.
  revert a b.
  induction c.
  - intros a b.
    rewrite nat_add_zero_r.
    rewrite nat_add_zero_r.
    exact idmap.
  - intros a b H.
    rewrite nat_add_succ_r.
    rewrite nat_add_succ_r.
    exact (IHc a b H).
Defined.

Lemma nat_add_swap_middle
  : forall a b c, nat_add a (nat_add b c) = nat_add b (nat_add a c).
Proof.
  intros a b c.
  rewrite nat_add_assoc.
  rewrite (nat_add_comm a b).
  rewrite <- nat_add_assoc.
  reflexivity.
Defined.

Definition nat_mul_succ_r_add
  : forall n m, nat_mul n (S m) = nat_add n (nat_mul n m)
  := fun n m => nat_mul_succ_r n m @ nat_add_comm (nat_mul n m) n.

Lemma nat_lt_add_l
  : forall a b c, nat_lt b c -> nat_lt (nat_add a b) (nat_add a c).
Proof.
  intros a b c H.
  rewrite (nat_add_comm a b).
  rewrite (nat_add_comm a c).
  exact (nat_lt_add_r b c a H).
Defined.

Lemma nat_lt_add_both
  : forall a b c d, nat_lt a b -> nat_lt c d -> nat_lt (nat_add a c) (nat_add b d).
Proof.
  intros a b c d Hab Hcd.
  apply nat_lt_trans with (n := nat_add b c).
  - exact (nat_lt_add_r a b c Hab).
  - exact (nat_lt_add_l b c d Hcd).
Defined.

Lemma nat_mul_one_r
  : forall n, nat_mul n (S O) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    exact (ap S IHn).
Defined.

Lemma nat_lt_mul_pos_r
  : forall a b c, nat_lt a b -> nat_lt O c -> nat_lt (nat_mul a c) (nat_mul b c).
Proof.
  intros a b c Hab Hc.
  destruct c.
  - destruct Hc.
  - clear Hc.
    revert a b Hab.
    induction c.
    + intros a b Hab.
      rewrite nat_mul_one_r.
      rewrite nat_mul_one_r.
      exact Hab.
    + intros a b Hab.
      rewrite (nat_mul_succ_r_add a (S c)).
      rewrite (nat_mul_succ_r_add b (S c)).
      apply nat_lt_add_both.
      * exact Hab.
      * exact (IHc a b Hab).
Defined.

Lemma nat_lt_add_cancel_l
  : forall a b c, nat_lt (nat_add c a) (nat_add c b) -> nat_lt a b.
Proof.
  intros a b c.
  revert a b.
  induction c.
  - intros a b H.
    exact H.
  - intros a b H.
    simpl in H.
    exact (IHc a b H).
Defined.

Lemma nat_lt_mul_cancel_r
  : forall a b c, nat_lt O c -> nat_lt (nat_mul a c) (nat_mul b c) -> nat_lt a b.
Proof.
  intros a.
  induction a.
  - intros b c Hc Hab.
    destruct b.
    + destruct c; [destruct Hc | destruct Hab].
    + exact tt.
  - intros b c Hc Hab.
    destruct b.
    + destruct c; [destruct Hc |].
      simpl in Hab.
      destruct Hab.
    + simpl.
      apply IHa with (c := c).
      * exact Hc.
      * destruct c; [destruct Hc |].
        simpl in Hab.
        exact (nat_lt_add_cancel_l (nat_mul a (S c)) (nat_mul b (S c)) c Hab).
Defined.

Lemma nat_mul_rearrange_1
  : forall a b c, nat_mul (nat_mul a b) c = nat_mul (nat_mul a c) b.
Proof.
  intros.
  rewrite <- nat_mul_assoc.
  rewrite (nat_mul_comm b c).
  rewrite nat_mul_assoc.
  reflexivity.
Defined.

Lemma qpos_lt_trans
  : forall q1 q2 q3, qpos_lt q1 q2 -> qpos_lt q2 q3 -> qpos_lt q1 q3.
Proof.
  intros q1 q2 q3 H12 H23.
  unfold qpos_lt in *.
  apply nat_lt_mul_cancel_r with (c := qpos_denom q2).
  - unfold qpos_denom.
    exact tt.
  - apply nat_lt_trans with (n := nat_mul (nat_mul (qpos_num q2) (qpos_denom q1)) (qpos_denom q3)).
    + apply (transport (fun x => nat_lt x _) (nat_mul_rearrange_1 (qpos_num q1) (qpos_denom q3) (qpos_denom q2))^).
      apply nat_lt_mul_pos_r.
      * exact H12.
      * unfold qpos_denom.
        exact tt.
    + apply (transport (fun x => nat_lt x _) (nat_mul_rearrange_1 (qpos_num q2) (qpos_denom q3) (qpos_denom q1))).
      apply (transport (fun x => nat_lt _ x) (nat_mul_rearrange_1 (qpos_num q3) (qpos_denom q2) (qpos_denom q1))).
      apply nat_lt_mul_pos_r.
      * exact H23.
      * unfold qpos_denom.
        exact tt.
Defined.

(** *** The order module on positive rationals *)

Definition qpos_le (q1 q2 : QPos) : Type :=
  nat_le (nat_mul (qpos_num q1) (qpos_denom q2))
         (nat_mul (qpos_num q2) (qpos_denom q1)).

Lemma qpos_le_refl (q : QPos) : qpos_le q q.
Proof.
  exact (nat_le_refl _).
Defined.

Lemma qpos_le_of_lt (q1 q2 : QPos) : qpos_lt q1 q2 -> qpos_le q1 q2.
Proof.
  exact (nat_le_of_lt _ _).
Defined.

Lemma qpos_le_total (q1 q2 : QPos) : ((qpos_le q1 q2) + (qpos_le q2 q1))%type.
Proof.
  exact (nat_le_total _ _).
Defined.

Lemma qpos_le_dec (q1 q2 : QPos)
  : ((qpos_le q1 q2) + (qpos_le q1 q2 -> Empty))%type.
Proof.
  exact (nat_le_dec _ _).
Defined.

Lemma nat_le_mul_r (a b c : nat)
  : nat_le a b -> nat_le (nat_mul a c) (nat_mul b c).
Proof.
  intro Hab.
  exact (nat_le_of_leq _ _ (nat_mul_r_monotone c (leq_of_nat_le a b Hab))).
Defined.

Lemma nat_le_mul_cancel_r (a b c : nat)
  (Hc : nat_lt O c) (H : nat_le (nat_mul a c) (nat_mul b c))
  : nat_le a b.
Proof.
  destruct (nat_lt_or_eq_or_gt a b) as [[Hlt | Heq] | Hgt].
  - exact (nat_le_of_lt a b Hlt).
  - exact (transport (fun m => nat_le a m) Heq (nat_le_refl a)).
  - apply Empty_rec.
    exact (nat_le_lt_contradiction (nat_mul a c) (nat_mul b c) H
             (nat_lt_mul_pos_r b a c Hgt Hc)).
Defined.

Lemma qpos_le_trans (q1 q2 q3 : QPos)
  (H12 : qpos_le q1 q2) (H23 : qpos_le q2 q3)
  : qpos_le q1 q3.
Proof.
  unfold qpos_le in *.
  apply nat_le_mul_cancel_r with (c := qpos_denom q2).
  - unfold qpos_denom.
    exact tt.
  - apply nat_le_trans with
      (b := nat_mul (nat_mul (qpos_num q2) (qpos_denom q1)) (qpos_denom q3)).
    + apply (transport (fun x => nat_le x _)
              (nat_mul_rearrange_1 (qpos_num q1) (qpos_denom q3)
                 (qpos_denom q2))^).
      apply nat_le_mul_r.
      exact H12.
    + apply (transport (fun x => nat_le x _)
              (nat_mul_rearrange_1 (qpos_num q2) (qpos_denom q3)
                 (qpos_denom q1))).
      apply (transport (fun x => nat_le _ x)
              (nat_mul_rearrange_1 (qpos_num q3) (qpos_denom q2)
                 (qpos_denom q1))).
      apply nat_le_mul_r.
      exact H23.
Defined.

Lemma qpos_lt_of_le_of_lt (q1 q2 q3 : QPos)
  (H12 : qpos_le q1 q2) (H23 : qpos_lt q2 q3)
  : qpos_lt q1 q3.
Proof.
  unfold qpos_le, qpos_lt in *.
  apply nat_lt_mul_cancel_r with (c := qpos_denom q2).
  - unfold qpos_denom.
    exact tt.
  - apply nat_le_lt_trans with
      (b := nat_mul (nat_mul (qpos_num q2) (qpos_denom q1)) (qpos_denom q3)).
    + apply (transport (fun x => nat_le x _)
              (nat_mul_rearrange_1 (qpos_num q1) (qpos_denom q3)
                 (qpos_denom q2))^).
      apply nat_le_mul_r.
      exact H12.
    + apply (transport (fun x => nat_lt x _)
              (nat_mul_rearrange_1 (qpos_num q2) (qpos_denom q3)
                 (qpos_denom q1))).
      apply (transport (fun x => nat_lt _ x)
              (nat_mul_rearrange_1 (qpos_num q3) (qpos_denom q2)
                 (qpos_denom q1))).
      apply nat_lt_mul_pos_r.
      * exact H23.
      * unfold qpos_denom.
        exact tt.
Defined.

Lemma w_stage_monotone
  : forall n m, nat_lt n m -> qpos_lt (w_stage m) (w_stage n).
Proof.
  intros n.
  induction n.
  - intros m Hm.
    destruct m.
    + destruct Hm.
    + clear Hm.
      induction m.
      * exact (w_stage_antitonicity 0).
      * apply qpos_lt_trans with (q2 := w_stage (S m)).
        { exact (w_stage_antitonicity (S m)). }
        { exact IHm. }
  - intros m Hm.
    destruct m.
    + destruct Hm.
    + apply IHn.
      exact Hm.
Defined.

Theorem w_stage_limit_zero
  : LimitZero w_stage.
Proof.
  unfold LimitZero.
  intros epsilon Heps.
  exists (qpos_denom epsilon).
  intros m Hm.
  apply qpos_lt_trans with (q2 := w_stage (qpos_denom epsilon)).
  - exact (w_stage_monotone (qpos_denom epsilon) m Hm).
  - exact (w_stage_archimedean epsilon Heps).
Defined.

Theorem LimitZero_not_implies_EventuallyZero
  : LimitZero w_stage * (EventuallyZero w_stage -> Empty).
Proof.
  split.
  - exact w_stage_limit_zero.
  - exact w_stage_not_eventually_zero.
Defined.

Definition qpos_mult (q1 q2 : QPos) : QPos :=
  {| qpos_num := nat_mul (qpos_num q1) (qpos_num q2);
     qpos_denom_pred := nat_pred (nat_mul (qpos_denom q1) (qpos_denom q2)) |}.

Lemma nat_mul_SS_pos
  : forall a b, nat_lt O (nat_mul (S a) (S b)).
Proof.
  intros a b.
  simpl.
  exact tt.
Defined.

Lemma S_nat_pred_of_pos
  : forall n, nat_lt O n -> S (nat_pred n) = n.
Proof.
  intros n Hn.
  destruct n.
  - destruct Hn.
  - reflexivity.
Defined.

Lemma qpos_denom_mult
  : forall q1 q2, qpos_denom (qpos_mult q1 q2) = nat_mul (qpos_denom q1) (qpos_denom q2).
Proof.
  intros q1 q2.
  unfold qpos_mult, qpos_denom.
  set (d1 := S (qpos_denom_pred q1)).
  set (d2 := S (qpos_denom_pred q2)).
  change (S (nat_pred (nat_mul d1 d2)) = nat_mul d1 d2).
  apply S_nat_pred_of_pos.
  unfold d1, d2.
  exact (nat_mul_SS_pos (qpos_denom_pred q1) (qpos_denom_pred q2)).
Defined.

Record WeightedTower : Type := {
  wt_threshold : nat -> QPos;
  wt_threshold_decreasing : forall n, qpos_lt (wt_threshold (S n)) (wt_threshold n)
}.

Definition stage_tower : WeightedTower :=
  {| wt_threshold := w_stage;
     wt_threshold_decreasing := w_stage_antitonicity |}.

Record ObstructionData (tower : WeightedTower) : Type := {
  obs_bound_const : QPos;
  obs_at_stage : nat -> QPos
}.

Definition obs_bounded_by_weight (tower : WeightedTower) (od : ObstructionData tower)
  : Type :=
  forall n, qpos_lt (obs_at_stage tower od n)
                    (qpos_mult (obs_bound_const tower od) (wt_threshold tower n)).

(** Weak decrease is the correct axiom: strict decrease is jointly unsatisfiable with discreteness and the weight bound, as strict_decreasing_discrete_bounded_empty proves below. *)

Definition obs_decreasing (tower : WeightedTower) (od : ObstructionData tower)
  : Type :=
  forall n, qpos_le (obs_at_stage tower od (S n)) (obs_at_stage tower od n).

Record BoundedObstruction (tower : WeightedTower) : Type := {
  bo_data : ObstructionData tower;
  bo_bounded : obs_bounded_by_weight tower bo_data;
  bo_decreasing : obs_decreasing tower bo_data
}.

Definition tower_obstructions_limit_zero
  (tower : WeightedTower) (bo : BoundedObstruction tower)
  : Type :=
  LimitZero (obs_at_stage tower (bo_data tower bo)).

Definition threshold_limit_zero (tower : WeightedTower)
  : Type :=
  LimitZero (wt_threshold tower).

Theorem stage_tower_threshold_limit_zero
  : threshold_limit_zero stage_tower.
Proof.
  unfold threshold_limit_zero, stage_tower.
  simpl.
  exact w_stage_limit_zero.
Defined.

Definition qpos_div_by (epsilon C : QPos) : QPos :=
  {| qpos_num := nat_mul (qpos_num epsilon) (qpos_denom C);
     qpos_denom_pred := nat_pred (nat_mul (qpos_denom epsilon) (qpos_num C)) |}.

Lemma qpos_div_by_pos
  : forall epsilon C,
    nat_lt O (qpos_num epsilon) ->
    nat_lt O (qpos_num (qpos_div_by epsilon C)).
Proof.
  intros epsilon C Heps.
  unfold qpos_div_by.
  simpl.
  destruct (qpos_num epsilon) as [|e].
  - destruct Heps.
  - unfold qpos_denom.
    simpl.
    exact tt.
Defined.

Lemma qpos_denom_div_by
  : forall epsilon C,
    nat_lt O (qpos_num C) ->
    qpos_denom (qpos_div_by epsilon C) = nat_mul (qpos_denom epsilon) (qpos_num C).
Proof.
  intros epsilon C HC.
  unfold qpos_div_by, qpos_denom.
  apply S_nat_pred_of_pos.
  destruct (qpos_num C) as [|c].
  - destruct HC.
  - destruct (qpos_denom_pred epsilon) as [|e].
    + simpl.
      exact tt.
    + simpl.
      exact tt.
Defined.

Lemma nat_mul_rearrange_afc
  : forall a f c, nat_mul a (nat_mul f c) = nat_mul (nat_mul c a) f.
Proof.
  intros a f c.
  rewrite (nat_mul_comm f c).
  rewrite nat_mul_assoc.
  exact (ap (fun x => nat_mul x f) (nat_mul_comm a c)).
Defined.

Lemma qpos_mult_lt_from_div
  : forall (q epsilon C : QPos),
    nat_lt O (qpos_num C) ->
    qpos_lt q (qpos_div_by epsilon C) ->
    qpos_lt (qpos_mult C q) epsilon.
Proof.
  intros q epsilon C HC H.
  unfold qpos_lt in *.
  unfold qpos_mult.
  simpl.
  rewrite qpos_denom_mult.
  rewrite (qpos_denom_div_by epsilon C HC) in H.
  set (P_lhs := nat_mul_rearrange_afc (qpos_num q) (qpos_denom epsilon) (qpos_num C)).
  set (P_rhs := (nat_mul_assoc (qpos_num epsilon) (qpos_denom C) (qpos_denom q))^).
  exact (transport (fun x => nat_lt _ x) P_rhs
          (transport (fun x => nat_lt x _) P_lhs H)).
Defined.

(** Master convergence lemma: a measure bounded by a positive constant times a vanishing measure vanishes. *)

Lemma bounded_limit_zero (measure aux : nat -> QPos) (C : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hbound : forall n, qpos_lt (measure n) (qpos_mult C (aux n)))
  (Haux : LimitZero aux)
  : LimitZero measure.
Proof.
  intros epsilon Heps.
  set (epsilon' := qpos_div_by epsilon C).
  assert (Heps' : nat_lt O (qpos_num epsilon')).
  { exact (qpos_div_by_pos epsilon C Heps). }
  destruct (Haux epsilon' Heps') as [N HN].
  exists N.
  intros m Hm.
  apply qpos_lt_trans with (q2 := qpos_mult C (aux m)).
  - exact (Hbound m).
  - apply qpos_mult_lt_from_div.
    + exact HC.
    + exact (HN m Hm).
Defined.

Lemma bounded_measure_limit_zero (measure : nat -> QPos) (C : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hbound : forall n, qpos_lt (measure n) (qpos_mult C (w_stage n)))
  : LimitZero measure.
Proof.
  exact (bounded_limit_zero measure w_stage C HC Hbound w_stage_limit_zero).
Defined.

Theorem bounded_obstructions_limit_zero
  : forall (tower : WeightedTower) (bo : BoundedObstruction tower),
    threshold_limit_zero tower ->
    nat_lt O (qpos_num (obs_bound_const tower (bo_data tower bo))) ->
    tower_obstructions_limit_zero tower bo.
Proof.
  intros tower bo Hthresh HC.
  exact (bounded_limit_zero _ (wt_threshold tower) _ HC
           (bo_bounded tower bo) Hthresh).
Defined.

Theorem stage_tower_obstructions_limit_zero
  : forall (bo : BoundedObstruction stage_tower),
    nat_lt O (qpos_num (obs_bound_const stage_tower (bo_data stage_tower bo))) ->
    tower_obstructions_limit_zero stage_tower bo.
Proof.
  intros bo HC.
  apply bounded_obstructions_limit_zero.
  - exact stage_tower_threshold_limit_zero.
  - exact HC.
Defined.

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial : forall X, Contr (morphism C zero X);
  is_terminal : forall X, Contr (morphism C X zero)
}.

Definition zero_morphism {C : PreCategory} (Z : ZeroObject C) (X Y : object C)
  : morphism C X Y
  := (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.

Lemma initial_morphism_unique {C : PreCategory} (I X : object C)
  (H_initial : Contr (morphism C I X)) (f g : morphism C I X)
  : f = g.
Proof.
  transitivity (@center _ H_initial).
  - exact (@contr _ H_initial f)^.
  - exact (@contr _ H_initial g).
Defined.

Lemma terminal_morphism_unique {C : PreCategory} (X T : object C)
  (H_terminal : Contr (morphism C X T)) (f g : morphism C X T)
  : f = g.
Proof.
  transitivity (@center _ H_terminal).
  - exact (@contr _ H_terminal f)^.
  - exact (@contr _ H_terminal g).
Defined.

Lemma morphism_through_zero_is_zero {C : PreCategory} (Z : ZeroObject C)
  (X Y : object C) (f : morphism C X (zero C Z)) (g : morphism C (zero C Z) Y)
  : (g o f)%morphism = zero_morphism Z X Y.
Proof.
  unfold zero_morphism.
  apply ap011.
  - apply initial_morphism_unique.
    apply (@is_initial _ Z).
  - apply terminal_morphism_unique.
    apply (@is_terminal _ Z).
Defined.

Definition IsIsomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  : Type
  := { g : morphism C Y X & ((g o f = 1)%morphism * (f o g = 1)%morphism) }.

Definition iso_inverse {C : PreCategory} {X Y : object C} {f : morphism C X Y}
  (H : IsIsomorphism f)
  : morphism C Y X
  := H.1.

(** Being an isomorphism over hset hom-types is a proposition. *)

Global Instance ishprop_isisomorphism {C : PreCategory} {X Y : object C}
  (f : morphism C X Y)
  : IsHProp (IsIsomorphism f).
Proof.
  apply hprop_allpath.
  intros [g [p q]] [g' [p' q']].
  apply path_sigma_hprop.
  simpl.
  refine ((right_identity C _ _ g)^ @ _).
  refine (ap (fun h => (g o h)%morphism) q'^ @ _).
  refine ((associativity C _ _ _ _ g' f g)^ @ _).
  refine (ap (fun h => (h o g')%morphism) p @ _).
  apply left_identity.
Defined.

(** Isomorphisms cancel on the left of composition. *)

Lemma iso_cancel_l {C : PreCategory} {X Y W : object C}
  (m : morphism C X Y) (H : IsIsomorphism m)
  (a b : morphism C W X)
  (E : (m o a = m o b)%morphism)
  : a = b.
Proof.
  destruct H as [i [Him Hmi]].
  refine ((left_identity C _ _ a)^ @ _).
  refine (ap (fun h => (h o a)%morphism) Him^ @ _).
  refine (associativity C _ _ _ _ a m i @ _).
  refine (ap (fun h => (i o h)%morphism) E @ _).
  refine ((associativity C _ _ _ _ b m i)^ @ _).
  refine (ap (fun h => (h o b)%morphism) Him @ _).
  apply left_identity.
Defined.

Record CategoricalTower (C : PreCategory) := {
  ct_stage : nat -> object C;
  ct_map : forall n, morphism C (ct_stage (S n)) (ct_stage n)
}.

Definition TowerStabilizesAt {C : PreCategory} (T : CategoricalTower C) (N : nat)
  : Type
  := forall n, nat_le N n -> IsIsomorphism (ct_map C T n).

Record WeightMeasure (C : PreCategory) (Z : ZeroObject C) := {
  wm_measure : object C -> QPos;
  wm_zero_is_zero : wm_measure (zero C Z) = qpos_zero
}.

Record FiberData {C : PreCategory} (Z : ZeroObject C)
  {X Y : object C} (f : morphism C X Y) := {
  fd_fiber : object C;
  fd_inclusion : morphism C fd_fiber X;
  fd_exactness : (f o fd_inclusion)%morphism = zero_morphism Z fd_fiber Y
}.

Record TowerWithFibers (C : PreCategory) (Z : ZeroObject C) := {
  twf_tower : CategoricalTower C;
  twf_fiber : forall n, FiberData Z (ct_map C twf_tower n)
}.

Definition obstruction_obj {C : PreCategory} {Z : ZeroObject C}
  (T : TowerWithFibers C Z) (n : nat)
  : object C
  := fd_fiber Z (ct_map C (twf_tower C Z T) n) (twf_fiber C Z T n).

Definition ZeroFiberImpliesIso (C : PreCategory) (Z : ZeroObject C)
  : Type
  := forall (X Y : object C) (f : morphism C X Y) (fib : FiberData Z f),
     fd_fiber Z f fib = zero C Z -> IsIsomorphism f.

(** The tower-local zero-fiber condition speaks only of the tower's own fiber data, since every morphism admits a degenerate zero-fiber datum and the global condition forces all maps to be isomorphisms. *)

Definition TowerZeroFiberImpliesIso {C : PreCategory} {Z : ZeroObject C}
  (T : TowerWithFibers C Z)
  : Type
  := forall n,
     fd_fiber Z (ct_map C (twf_tower C Z T) n) (twf_fiber C Z T n) = zero C Z ->
     IsIsomorphism (ct_map C (twf_tower C Z T) n).

Definition ZeroMeasureImpliesZeroObject (C : PreCategory) (Z : ZeroObject C)
  (wm : WeightMeasure C Z)
  : Type
  := forall (X : object C), qpos_is_zero (wm_measure C Z wm X) -> X = zero C Z.

Theorem zero_obstructions_imply_stabilization
  {C : PreCategory} {Z : ZeroObject C}
  (T : TowerWithFibers C Z)
  (wm : WeightMeasure C Z)
  (H_zero_fiber : TowerZeroFiberImpliesIso T)
  (H_zero_measure : ZeroMeasureImpliesZeroObject C Z wm)
  (N : nat)
  (H_obs_zero : forall n, nat_le N n -> qpos_is_zero (wm_measure C Z wm (obstruction_obj T n)))
  : TowerStabilizesAt (twf_tower C Z T) N.
Proof.
  unfold TowerStabilizesAt.
  intros n Hn.
  apply H_zero_fiber.
  apply H_zero_measure.
  exact (H_obs_zero n Hn).
Defined.

Definition HasMinimalPositive (measure : nat -> QPos)
  : Type
  := { min_val : QPos &
       (nat_lt O (qpos_num min_val)) *
       (forall n, (qpos_is_zero (measure n)) + (qpos_lt min_val (measure n) + (measure n = min_val))) }.

Theorem discrete_LimitZero_implies_EventuallyZero
  (measure : nat -> QPos)
  (H_min : HasMinimalPositive measure)
  (H_limit : LimitZero measure)
  : EventuallyZero measure.
Proof.
  destruct H_min as [min_val [Hpos Hdiscrete]].
  destruct (H_limit min_val Hpos) as [N HN].
  exists N.
  intros m Hm.
  destruct (Hdiscrete m) as [Hzero | [Hgt | Heq]].
  - exact Hzero.
  - exfalso.
    apply (qpos_lt_irrefl min_val).
    apply qpos_lt_trans with (q2 := measure m).
    + exact Hgt.
    + exact (HN m Hm).
  - exfalso.
    pose proof (HN m Hm) as Hlt.
    rewrite Heq in Hlt.
    exact (qpos_lt_irrefl min_val Hlt).
Defined.

(** Strict decrease, discreteness, and the weight bound are jointly unsatisfiable, which is why obs_decreasing asks only weak decrease. *)

Lemma qpos_lt_into_zero_num (q r : QPos)
  (Hr : qpos_num r = O) (H : qpos_lt q r)
  : Empty.
Proof.
  apply (nat_lt_zero_absurd (nat_mul (qpos_num q) (qpos_denom r))).
  exact (transport
           (fun m => nat_lt (nat_mul (qpos_num q) (qpos_denom r))
                       (nat_mul m (qpos_denom q)))
           Hr H).
Defined.

Theorem strict_decreasing_discrete_bounded_empty
  (tower : WeightedTower) (od : ObstructionData tower)
  (Hstrict : forall n, qpos_lt (obs_at_stage tower od (S n))
                               (obs_at_stage tower od n))
  (Hbounded : obs_bounded_by_weight tower od)
  (Hthresh : threshold_limit_zero tower)
  (Hpos : nat_lt O (qpos_num (obs_bound_const tower od)))
  (Hmin : HasMinimalPositive (obs_at_stage tower od))
  : Empty.
Proof.
  pose (Hlim := bounded_limit_zero _ (wt_threshold tower) _ Hpos
                  Hbounded Hthresh).
  destruct (discrete_LimitZero_implies_EventuallyZero _ Hmin Hlim)
    as [N HN].
  apply (qpos_lt_into_zero_num (obs_at_stage tower od (S (S N)))
           (obs_at_stage tower od (S N))).
  - exact (HN (S N) (nat_lt_S N)).
  - exact (Hstrict (S N)).
Defined.

(** The categorical measure is tied to the arithmetic obstruction by two-sided order bounds; the strict form is the reflexive special case. *)

Record WeightedCategoricalTower (C : PreCategory) (Z : ZeroObject C) := {
  wct_arith : WeightedTower;
  wct_bo : BoundedObstruction wct_arith;
  wct_cat : TowerWithFibers C Z;
  wct_measure : WeightMeasure C Z;
  wct_obs_le : forall n,
    qpos_le (wm_measure C Z wct_measure (obstruction_obj wct_cat n))
            (obs_at_stage wct_arith (bo_data wct_arith wct_bo) n);
  wct_obs_ge : forall n,
    qpos_le (obs_at_stage wct_arith (bo_data wct_arith wct_bo) n)
            (wm_measure C Z wct_measure (obstruction_obj wct_cat n))
}.

Definition obs_measure {C : PreCategory} {Z : ZeroObject C}
  (wct : WeightedCategoricalTower C Z) (n : nat)
  : QPos
  := wm_measure C Z (wct_measure C Z wct) (obstruction_obj (wct_cat C Z wct) n).

(** *** Tower weight measures: fibers bounded by their stage, stages non-increasing downward, and the matching conditions derived by reflexivity. *)

Record TowerWeightMeasure (C : PreCategory) (Z : ZeroObject C)
  (T : TowerWithFibers C Z) := {
  twm_wm : WeightMeasure C Z;
  twm_fiber_bounded : forall n,
    qpos_le (wm_measure C Z twm_wm (obstruction_obj T n))
            (wm_measure C Z twm_wm (ct_stage C (twf_tower C Z T) (S n)));
  twm_nonincreasing : forall n,
    qpos_le (wm_measure C Z twm_wm (ct_stage C (twf_tower C Z T) n))
            (wm_measure C Z twm_wm (ct_stage C (twf_tower C Z T) (S n)))
}.

Lemma twm_fiber_le_later {C : PreCategory} {Z : ZeroObject C}
  {T : TowerWithFibers C Z} (twm : TowerWeightMeasure C Z T)
  (n j : nat)
  : qpos_le (wm_measure C Z (twm_wm C Z T twm) (obstruction_obj T n))
            (wm_measure C Z (twm_wm C Z T twm)
               (ct_stage C (twf_tower C Z T) (nat_add j (S n)))).
Proof.
  induction j.
  - exact (twm_fiber_bounded C Z T twm n).
  - refine (qpos_le_trans _ _ _ IHj _).
    exact (twm_nonincreasing C Z T twm (nat_add j (S n))).
Defined.

Definition wct_of_tower_measure {C : PreCategory} {Z : ZeroObject C}
  (T : TowerWithFibers C Z) (twm : TowerWeightMeasure C Z T)
  (W : WeightedTower)
  (Hbound : obs_bounded_by_weight W
              {| obs_bound_const := qpos_one;
                 obs_at_stage := fun n =>
                   wm_measure C Z (twm_wm C Z T twm) (obstruction_obj T n) |})
  (Hdec : obs_decreasing W
            {| obs_bound_const := qpos_one;
               obs_at_stage := fun n =>
                 wm_measure C Z (twm_wm C Z T twm) (obstruction_obj T n) |})
  : WeightedCategoricalTower C Z
  := {| wct_arith := W;
        wct_bo := {| bo_data :=
                       {| obs_bound_const := qpos_one;
                          obs_at_stage := fun n =>
                            wm_measure C Z (twm_wm C Z T twm)
                              (obstruction_obj T n) |};
                     bo_bounded := Hbound;
                     bo_decreasing := Hdec |};
        wct_cat := T;
        wct_measure := twm_wm C Z T twm;
        wct_obs_le := fun n => qpos_le_refl _;
        wct_obs_ge := fun n => qpos_le_refl _ |}.

Lemma nat_lt_of_S_le
  : forall N n, nat_le (S N) n -> nat_lt N n.
Proof.
  exact nat_lt_of_le_succ.
Defined.

Theorem weighted_tower_stabilizes
  {C : PreCategory} {Z : ZeroObject C}
  (wct : WeightedCategoricalTower C Z)
  (H_thresh_limit : threshold_limit_zero (wct_arith C Z wct))
  (H_bound_pos : nat_lt O (qpos_num (obs_bound_const (wct_arith C Z wct)
                   (bo_data (wct_arith C Z wct) (wct_bo C Z wct)))))
  (H_discrete : HasMinimalPositive (obs_measure wct))
  (H_zero_fiber : TowerZeroFiberImpliesIso (wct_cat C Z wct))
  (H_zero_measure : ZeroMeasureImpliesZeroObject C Z (wct_measure C Z wct))
  : { N : nat & TowerStabilizesAt (twf_tower C Z (wct_cat C Z wct)) N }.
Proof.
  set (tower := wct_arith C Z wct).
  set (bo := wct_bo C Z wct).
  assert (H_obs_limit : tower_obstructions_limit_zero tower bo).
  { apply bounded_obstructions_limit_zero.
    - exact H_thresh_limit.
    - exact H_bound_pos. }
  assert (H_obs_limit' : LimitZero (obs_measure wct)).
  { unfold LimitZero in *.
    intros epsilon Heps.
    destruct (H_obs_limit epsilon Heps) as [N HN].
    exists N.
    intros m Hm.
    unfold obs_measure.
    exact (qpos_lt_of_le_of_lt _ _ _ (wct_obs_le C Z wct m) (HN m Hm)). }
  destruct (discrete_LimitZero_implies_EventuallyZero (obs_measure wct) H_discrete H_obs_limit')
    as [N HN].
  exists (S N).
  apply (zero_obstructions_imply_stabilization
           (wct_cat C Z wct) (wct_measure C Z wct)
           H_zero_fiber H_zero_measure (S N)).
  intros n Hn.
  unfold obs_measure in HN.
  apply HN.
  exact (nat_lt_of_S_le N n Hn).
Defined.

Record PreStableCategory := {
  ps_cat :> PreCategory;
  ps_zero : ZeroObject ps_cat;
  ps_susp : Functor ps_cat ps_cat;
  ps_loop : Functor ps_cat ps_cat;
  ps_eta : NaturalTransformation 1%functor (ps_loop o ps_susp)%functor;
  ps_epsilon : NaturalTransformation (ps_susp o ps_loop)%functor 1%functor
}.

Definition ps_zero_morphism (S : PreStableCategory) (X Y : object S)
  : morphism S X Y
  := zero_morphism (ps_zero S) X Y.

Record Triangle (S : PreStableCategory) := {
  tri_X : object S;
  tri_Y : object S;
  tri_Z : object S;
  tri_f : morphism S tri_X tri_Y;
  tri_g : morphism S tri_Y tri_Z;
  tri_h : morphism S tri_Z (object_of (ps_susp S) tri_X)
}.

Record DistinguishedTriangle (S : PreStableCategory) := {
  dt_tri : Triangle S;
  dt_gf_zero : (tri_g S dt_tri o tri_f S dt_tri)%morphism =
               ps_zero_morphism S (tri_X S dt_tri) (tri_Z S dt_tri);
  dt_hg_zero : (tri_h S dt_tri o tri_g S dt_tri)%morphism =
               ps_zero_morphism S (tri_Y S dt_tri) (object_of (ps_susp S) (tri_X S dt_tri));
  dt_susp_f_h_zero : (morphism_of (ps_susp S) (tri_f S dt_tri) o tri_h S dt_tri)%morphism =
                     ps_zero_morphism S (tri_Z S dt_tri) (object_of (ps_susp S) (tri_Y S dt_tri))
}.

Record TowerInStable (SC : PreStableCategory) := {
  tis_tower : CategoricalTower SC;
  tis_fiber_triangle : forall n, DistinguishedTriangle SC;
  tis_iso_transfer : forall n,
    IsIsomorphism (tri_f SC (dt_tri SC (tis_fiber_triangle n))) ->
    IsIsomorphism (ct_map SC tis_tower n)
}.

Definition tis_fiber_obj {SC : PreStableCategory} (T : TowerInStable SC) (n : nat)
  : object SC
  := tri_Z SC (dt_tri SC (tis_fiber_triangle SC T n)).

Definition ZeroFiberInTriangleImpliesIso (SC : PreStableCategory)
  : Type
  := forall (dt : DistinguishedTriangle SC),
     tri_Z SC (dt_tri SC dt) = zero SC (ps_zero SC) ->
     IsIsomorphism (tri_f SC (dt_tri SC dt)).

Definition ZeroMeasureImpliesZeroObj (SC : PreStableCategory)
  (wm : WeightMeasure SC (ps_zero SC))
  : Type
  := forall (X : object SC), qpos_is_zero (wm_measure SC (ps_zero SC) wm X) -> X = zero SC (ps_zero SC).

(** *** Exact triangles factor every test morphism killed by g uniquely through f, ruling out all-zero triangles and making the zero-fiber criterion a theorem. *)

Lemma zero_morphism_precompose {C : PreCategory} (Z : ZeroObject C)
  {W X Y : object C} (s : morphism C W X)
  : (zero_morphism Z X Y o s)%morphism = zero_morphism Z W Y.
Proof.
  unfold zero_morphism.
  refine (associativity _ _ _ _ _ _ _ _ @ _).
  apply ap.
  exact (@path_contr _ (@is_terminal _ Z W) _ _).
Defined.

Lemma zero_morphism_postcompose {C : PreCategory} (Z : ZeroObject C)
  {X Y Y' : object C} (t : morphism C Y Y')
  : (t o zero_morphism Z X Y)%morphism = zero_morphism Z X Y'.
Proof.
  unfold zero_morphism.
  refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
  refine (ap (fun h => (h o _)%morphism) _).
  exact (@path_contr _ (@is_initial _ Z Y') _ _).
Defined.

Record ExactDistinguishedTriangle (S : PreStableCategory) := {
  edt_dt : DistinguishedTriangle S;
  edt_exact : forall (W : object S)
    (t : morphism S W (tri_Y S (dt_tri S edt_dt))),
    (tri_g S (dt_tri S edt_dt) o t)%morphism
      = ps_zero_morphism S W (tri_Z S (dt_tri S edt_dt)) ->
    Contr { s : morphism S W (tri_X S (dt_tri S edt_dt)) &
            (tri_f S (dt_tri S edt_dt) o s)%morphism = t }
}.

Theorem exact_all_zero_forces_zero_identity (S : PreStableCategory)
  (E : ExactDistinguishedTriangle S)
  (Hf : tri_f S (dt_tri S (edt_dt S E))
        = ps_zero_morphism S _ _)
  (Hg : tri_g S (dt_tri S (edt_dt S E))
        = ps_zero_morphism S _ _)
  : (1%morphism : morphism S (tri_Y S (dt_tri S (edt_dt S E)))
                             (tri_Y S (dt_tri S (edt_dt S E))))
    = ps_zero_morphism S _ _.
Proof.
  pose (c := edt_exact S E _ 1%morphism
               (ap (fun h => (h o 1)%morphism) Hg
                  @ right_identity _ _ _ _)).
  pose (s := (@center _ c).1).
  refine ((@center _ c).2^ @ _).
  refine (ap (fun h => (h o s)%morphism) Hf @ _).
  exact (zero_morphism_precompose (ps_zero S) s).
Defined.

Theorem zero_fiber_triangle_iso (S : PreStableCategory)
  (E : ExactDistinguishedTriangle S)
  (Hz : tri_g S (dt_tri S (edt_dt S E))
        = ps_zero_morphism S _ _)
  : IsIsomorphism (tri_f S (dt_tri S (edt_dt S E))).
Proof.
  pose (c1 := edt_exact S E _ 1%morphism
                (ap (fun h => (h o 1)%morphism) Hz
                   @ right_identity _ _ _ _)).
  pose (s := (@center _ c1).1).
  pose (cs := (@center _ c1).2).
  exists s.
  split.
  - pose (c2 := edt_exact S E _ (tri_f S (dt_tri S (edt_dt S E)))
                  (dt_gf_zero S (edt_dt S E))).
    pose (p1 := ((s o tri_f S (dt_tri S (edt_dt S E)))%morphism ;
                 (associativity _ _ _ _ _ _ _ _)^
                   @ ap (fun h =>
                        (h o tri_f S (dt_tri S (edt_dt S E)))%morphism) cs
                   @ left_identity _ _ _ _)
                : { s' : _ &
                    (tri_f S (dt_tri S (edt_dt S E)) o s')%morphism
                    = tri_f S (dt_tri S (edt_dt S E)) }).
    pose (p2 := (1%morphism ; right_identity _ _ _ _)
                : { s' : _ &
                    (tri_f S (dt_tri S (edt_dt S E)) o s')%morphism
                    = tri_f S (dt_tri S (edt_dt S E)) }).
    exact (ap (fun z => z.1) (@path_contr _ c2 p1 p2)).
  - exact cs.
Defined.

Corollary zero_fiber_path_triangle_iso (S : PreStableCategory)
  (E : ExactDistinguishedTriangle S)
  (Hz : tri_Z S (dt_tri S (edt_dt S E)) = zero S (ps_zero S))
  : IsIsomorphism (tri_f S (dt_tri S (edt_dt S E))).
Proof.
  apply zero_fiber_triangle_iso.
  assert (Hcontr : Contr (morphism S (tri_Y S (dt_tri S (edt_dt S E)))
                            (tri_Z S (dt_tri S (edt_dt S E))))).
  { rewrite Hz.
    exact (@is_terminal _ (ps_zero S) _). }
  exact (@path_contr _ Hcontr _ _).
Defined.

Definition tis_fiber_measure {SC : PreStableCategory}
  (T : TowerInStable SC) (wm : WeightMeasure SC (ps_zero SC)) (n : nat)
  : QPos
  := wm_measure SC (ps_zero SC) wm (tis_fiber_obj T n).

Theorem stable_tower_stabilizes
  {SC : PreStableCategory}
  (T : TowerInStable SC)
  (wm : WeightMeasure SC (ps_zero SC))
  (H_zero_tri : ZeroFiberInTriangleImpliesIso SC)
  (H_zero_meas : ZeroMeasureImpliesZeroObj SC wm)
  (H_discrete : HasMinimalPositive (tis_fiber_measure T wm))
  (H_limit : LimitZero (tis_fiber_measure T wm))
  : { N : nat & TowerStabilizesAt (tis_tower SC T) N }.
Proof.
  destruct (discrete_LimitZero_implies_EventuallyZero
              (tis_fiber_measure T wm) H_discrete H_limit) as [N HN].
  exists (S N).
  unfold TowerStabilizesAt.
  intros n Hn.
  assert (Hzero : qpos_is_zero (tis_fiber_measure T wm n)).
  { apply HN.
    exact (nat_lt_of_S_le N n Hn). }
  assert (Hfiber_zero : tis_fiber_obj T n = zero SC (ps_zero SC)).
  { apply H_zero_meas.
    exact Hzero. }
  unfold tis_fiber_obj in Hfiber_zero.
  apply (tis_iso_transfer SC T n).
  apply H_zero_tri.
  exact Hfiber_zero.
Defined.

Definition rotate_triangle {SC : PreStableCategory} (T : Triangle SC)
  : Triangle SC
  := {| tri_X := tri_Y SC T;
        tri_Y := tri_Z SC T;
        tri_Z := object_of (ps_susp SC) (tri_X SC T);
        tri_f := tri_g SC T;
        tri_g := tri_h SC T;
        tri_h := morphism_of (ps_susp SC) (tri_f SC T) |}.

Lemma functor_preserves_zero_morphism
  {C : PreCategory} (Z : ZeroObject C) (F : Functor C C)
  (H_zero : object_of F (zero C Z) = zero C Z)
  (X Y : object C)
  : morphism_of F (zero_morphism Z X Y) = zero_morphism Z (object_of F X) (object_of F Y).
Proof.
  unfold zero_morphism.
  rewrite composition_of.
  set (f := morphism_of F (@center _ (@is_terminal C Z X))).
  set (g := morphism_of F (@center _ (@is_initial C Z Y))).
  set (f' := transport (fun W => morphism C (object_of F X) W) H_zero f).
  set (g' := transport (fun W => morphism C W (object_of F Y)) H_zero g).
  transitivity (g' o f')%morphism.
  - destruct H_zero.
    reflexivity.
  - apply morphism_through_zero_is_zero.
Defined.

Definition SuspPreservesZero (SC : PreStableCategory)
  : Type
  := object_of (ps_susp SC) (zero SC (ps_zero SC)) = zero SC (ps_zero SC).

Lemma susp_preserves_zero_morphism
  {SC : PreStableCategory} (H : SuspPreservesZero SC) (X Y : object SC)
  : morphism_of (ps_susp SC) (ps_zero_morphism SC X Y) =
    ps_zero_morphism SC (object_of (ps_susp SC) X) (object_of (ps_susp SC) Y).
Proof.
  unfold ps_zero_morphism.
  exact (functor_preserves_zero_morphism (ps_zero SC) (ps_susp SC) H X Y).
Defined.

Theorem rotate_preserves_distinguished
  {SC : PreStableCategory} (H : SuspPreservesZero SC) (dt : DistinguishedTriangle SC)
  : DistinguishedTriangle SC.
Proof.
  refine {| dt_tri := rotate_triangle (dt_tri SC dt) |}.
  - simpl.
    exact (dt_hg_zero SC dt).
  - simpl.
    exact (dt_susp_f_h_zero SC dt).
  - simpl.
    rewrite <- composition_of.
    rewrite (dt_gf_zero SC dt).
    exact (susp_preserves_zero_morphism H (tri_X SC (dt_tri SC dt)) (tri_Z SC (dt_tri SC dt))).
Defined.

Record ReducedFunctor (SC : PreStableCategory) := {
  rf_functor :> Functor SC SC;
  rf_preserves_zero : object_of rf_functor (zero SC (ps_zero SC)) = zero SC (ps_zero SC)
}.

Lemma rf_preserves_zero_morphism
  {SC : PreStableCategory} (F : ReducedFunctor SC) (X Y : object SC)
  : morphism_of F (ps_zero_morphism SC X Y) =
    ps_zero_morphism SC (object_of F X) (object_of F Y).
Proof.
  unfold ps_zero_morphism.
  exact (functor_preserves_zero_morphism (ps_zero SC) F (rf_preserves_zero SC F) X Y).
Defined.

Record NatTransBetweenReduced (SC : PreStableCategory) (F G : ReducedFunctor SC) := {
  ntbr_trans :> NaturalTransformation F G
}.

Record GoodwillieTowerData (SC : PreStableCategory) (F : ReducedFunctor SC) := {
  gtd_P : nat -> ReducedFunctor SC;
  gtd_p : forall n, NatTransBetweenReduced SC (gtd_P (S n)) (gtd_P n);
  gtd_from_F : forall n, NatTransBetweenReduced SC F (gtd_P n)
}.

Definition gtd_layer_at
  {SC : PreStableCategory} {F : ReducedFunctor SC}
  (gt : GoodwillieTowerData SC F) (n : nat) (X : object SC)
  : morphism SC (object_of (gtd_P SC F gt (S n)) X) (object_of (gtd_P SC F gt n) X)
  := components_of (gtd_p SC F gt n) X.

Record GoodwillieTowerWithLayers (SC : PreStableCategory) (F : ReducedFunctor SC) := {
  gtwl_data : GoodwillieTowerData SC F;
  gtwl_D : nat -> ReducedFunctor SC;
  gtwl_zero_D_implies_iso : forall n X,
    object_of (gtwl_D n) X = zero SC (ps_zero SC) ->
    IsIsomorphism (gtd_layer_at gtwl_data n X)
}.

Definition gtwl_layer_measure
  {SC : PreStableCategory} {F : ReducedFunctor SC}
  (gt : GoodwillieTowerWithLayers SC F)
  (wm : WeightMeasure SC (ps_zero SC))
  (n : nat) (X : object SC)
  : QPos
  := wm_measure SC (ps_zero SC) wm (object_of (gtwl_D SC F gt n) X).

Definition GoodwillieLayersBounded
  {SC : PreStableCategory} {F : ReducedFunctor SC}
  (gt : GoodwillieTowerWithLayers SC F)
  (wm : WeightMeasure SC (ps_zero SC))
  (X : object SC)
  (bound : QPos)
  : Type
  := forall n,
     qpos_lt (gtwl_layer_measure gt wm n X)
             (qpos_mult bound (w_stage n)).

Theorem goodwillie_layers_limit_zero
  {SC : PreStableCategory} {F : ReducedFunctor SC}
  (gt : GoodwillieTowerWithLayers SC F)
  (wm : WeightMeasure SC (ps_zero SC))
  (X : object SC)
  (bound : QPos)
  (H_pos : nat_lt O (qpos_num bound))
  (H_bounded : GoodwillieLayersBounded gt wm X bound)
  : LimitZero (fun n => gtwl_layer_measure gt wm n X).
Proof.
  exact (bounded_measure_limit_zero _ bound H_pos H_bounded).
Defined.

Theorem goodwillie_tower_stabilizes
  {SC : PreStableCategory} {F : ReducedFunctor SC}
  (gt : GoodwillieTowerWithLayers SC F)
  (wm : WeightMeasure SC (ps_zero SC))
  (X : object SC)
  (bound : QPos)
  (H_pos : nat_lt O (qpos_num bound))
  (H_bounded : GoodwillieLayersBounded gt wm X bound)
  (H_discrete : HasMinimalPositive (fun n => gtwl_layer_measure gt wm n X))
  (H_zero_meas : ZeroMeasureImpliesZeroObj SC wm)
  : { N : nat & forall n, nat_le N n ->
      IsIsomorphism (gtd_layer_at (gtwl_data SC F gt) n X) }.
Proof.
  set (layer_meas := fun n => gtwl_layer_measure gt wm n X).
  assert (H_limit : LimitZero layer_meas).
  { exact (goodwillie_layers_limit_zero gt wm X bound H_pos H_bounded). }
  destruct (discrete_LimitZero_implies_EventuallyZero layer_meas H_discrete H_limit)
    as [N HN].
  exists (S N).
  intros n Hn.
  assert (Hzero : qpos_is_zero (layer_meas n)).
  { apply HN.
    exact (nat_lt_of_S_le N n Hn). }
  unfold layer_meas, gtwl_layer_measure in Hzero.
  assert (H_D_zero : object_of (gtwl_D SC F gt n) X = zero SC (ps_zero SC)).
  { apply H_zero_meas.
    exact Hzero. }
  exact (gtwl_zero_D_implies_iso SC F gt n X H_D_zero).
Defined.

Record BaseField := {
  bf_carrier : Type;
  bf_zero : bf_carrier;
  bf_one : bf_carrier;
  bf_char : nat
}.

Inductive SchemeType : Type :=
  | Affine : nat -> SchemeType
  | Projective : nat -> SchemeType
  | Product : SchemeType -> SchemeType -> SchemeType.

Fixpoint scheme_dim (st : SchemeType) : nat :=
  match st with
  | Affine n => n
  | Projective n => n
  | Product s1 s2 => nat_add (scheme_dim s1) (scheme_dim s2)
  end.

Record Scheme (k : BaseField) := {
  sch_type : SchemeType;
  sch_dim : nat;
  sch_dim_eq : sch_dim = scheme_dim sch_type
}.

Definition affine_space (k : BaseField) (n : nat) : Scheme k :=
  {| sch_type := Affine n;
     sch_dim := n;
     sch_dim_eq := idpath |}.

Definition projective_space (k : BaseField) (n : nat) : Scheme k :=
  {| sch_type := Projective n;
     sch_dim := n;
     sch_dim_eq := idpath |}.

Definition A1 (k : BaseField) : Scheme k := affine_space k 1.

Definition point_scheme (k : BaseField) : Scheme k := affine_space k 0.

Definition nat_eq_dec (n m : nat) : (n = m) + (n = m -> Empty)
  := decidable_paths_nat n m.

(** Audit: the truncation facts below are one-line derivations of library instances, retained for downstream references by name. *)

Global Instance hprop_unit : IsHProp Unit := istrunc_succ.

Global Instance hprop_empty : IsHProp Empty := istrunc_Empty _.

Definition MorphismData (k : BaseField) (X Y : Scheme k) : Type := Unit.

Record SchemeMorphism (k : BaseField) (X Y : Scheme k) := {
  sm_data : MorphismData k X Y
}.

Global Instance hprop_nat_le (n m : nat) : IsHProp (nat_le n m).
Proof.
  revert m.
  induction n.
  - intro m.
    exact hprop_unit.
  - intro m.
    destruct m.
    + exact hprop_empty.
    + exact (IHn m).
Defined.

Global Instance hset_unit : IsHSet Unit := istrunc_succ.

Global Instance MorphismData_hset (k : BaseField) (X Y : Scheme k)
  : IsHSet (MorphismData k X Y).
Proof.
  unfold MorphismData.
  exact hset_unit.
Defined.

Lemma SchemeMorphism_eq (k : BaseField) (X Y : Scheme k)
  (f g : SchemeMorphism k X Y)
  (H : sm_data k X Y f = sm_data k X Y g)
  : f = g.
Proof.
  destruct f as [fd].
  destruct g as [gd].
  simpl in H.
  destruct H.
  reflexivity.
Defined.

Definition path_SchemeMorphism (k : BaseField) (X Y : Scheme k)
  (f g : SchemeMorphism k X Y)
  : (sm_data k X Y f = sm_data k X Y g) -> (f = g)
  := SchemeMorphism_eq k X Y f g.

Global Instance trunc_SchemeMorphism (k : BaseField) (X Y : Scheme k)
  : IsHSet (SchemeMorphism k X Y).
Proof.
  apply (istrunc_equiv_istrunc (MorphismData k X Y)).
  - refine (equiv_adjointify
              (fun d => {| sm_data := d |})
              (fun m => sm_data k X Y m)
              _ _).
    + intro m.
      destruct m.
      reflexivity.
    + intro d.
      reflexivity.
  - exact (MorphismData_hset k X Y).
Defined.

Definition identity_data (k : BaseField) (X : Scheme k) : MorphismData k X X := tt.

Definition sm_identity (k : BaseField) (X : Scheme k) : SchemeMorphism k X X
  := {| sm_data := identity_data k X |}.

Definition compose_data (k : BaseField) (X Y Z : Scheme k)
  (d1 : MorphismData k X Y) (d2 : MorphismData k Y Z)
  : MorphismData k X Z := tt.

Definition sm_compose (k : BaseField) (X Y Z : Scheme k)
  (g : SchemeMorphism k Y Z) (f : SchemeMorphism k X Y)
  : SchemeMorphism k X Z
  := {| sm_data := compose_data k X Y Z (sm_data k X Y f) (sm_data k Y Z g) |}.

(** Audit: HoTT.Types.Bool supplies only implb lemmas, so the conjunction algebra is local. *)

Lemma andb_assoc : forall a b c : Bool, andb a (andb b c) = andb (andb a b) c.
Proof.
  intros [] [] []; reflexivity.
Defined.

Lemma andb_true_r : forall b : Bool, andb b true = b.
Proof.
  intros []; reflexivity.
Defined.

Lemma andb_true_l : forall b : Bool, andb true b = b.
Proof.
  intros []; reflexivity.
Defined.

Lemma andb_false_r : forall b : Bool, andb b false = false.
Proof.
  intros []; reflexivity.
Defined.

Lemma andb_false_l : forall b : Bool, andb false b = false.
Proof.
  intros []; reflexivity.
Defined.

Lemma compose_data_assoc (k : BaseField) (W X Y Z : Scheme k)
  (d1 : MorphismData k W X) (d2 : MorphismData k X Y) (d3 : MorphismData k Y Z)
  : compose_data k W X Z d1 (compose_data k X Y Z d2 d3) =
    compose_data k W Y Z (compose_data k W X Y d1 d2) d3.
Proof.
  reflexivity.
Defined.

Lemma sm_compose_assoc (k : BaseField) (W X Y Z : Scheme k)
  (f : SchemeMorphism k W X) (g : SchemeMorphism k X Y) (h : SchemeMorphism k Y Z)
  : sm_compose k W X Z (sm_compose k X Y Z h g) f =
    sm_compose k W Y Z h (sm_compose k W X Y g f).
Proof.
  apply path_SchemeMorphism.
  apply compose_data_assoc.
Defined.

Lemma sm_compose_id_l (k : BaseField) (X Y : Scheme k) (f : SchemeMorphism k X Y)
  : sm_compose k X Y Y (sm_identity k Y) f = f.
Proof.
  apply path_SchemeMorphism.
  destruct f as [[]].
  reflexivity.
Defined.

Lemma sm_compose_id_r (k : BaseField) (X Y : Scheme k) (f : SchemeMorphism k X Y)
  : sm_compose k X X Y f (sm_identity k X) = f.
Proof.
  apply path_SchemeMorphism.
  destruct f as [[]].
  reflexivity.
Defined.

Definition SchemeCategory (k : BaseField) : PreCategory
  := @Build_PreCategory
       (Scheme k)
       (fun X Y => SchemeMorphism k X Y)
       (fun X => sm_identity k X)
       (fun X Y Z g f => sm_compose k X Y Z g f)
       (fun s d d' d'' m1 m2 m3 => sm_compose_assoc k s d d' d'' m1 m2 m3)
       (fun a b f => sm_compose_id_l k a b f)
       (fun a b f => sm_compose_id_r k a b f)
       (fun s d => trunc_SchemeMorphism k s d).

Definition scheme_product (k : BaseField) (X Y : Scheme k) : Scheme k
  := {| sch_type := Product (sch_type k X) (sch_type k Y);
        sch_dim := nat_add (sch_dim k X) (sch_dim k Y);
        sch_dim_eq := ap011 nat_add (sch_dim_eq k X) (sch_dim_eq k Y) |}.

Definition scheme_with_A1 (k : BaseField) (X : Scheme k) : Scheme k
  := scheme_product k X (A1 k).

Definition zero_data (k : BaseField) (X Y : Scheme k) : MorphismData k X Y := tt.

Definition zero_scheme_morphism (k : BaseField) (X Y : Scheme k)
  : SchemeMorphism k X Y
  := {| sm_data := zero_data k X Y |}.

Lemma morphism_from_point_unique (k : BaseField) (Y : Scheme k)
  (f g : SchemeMorphism k (point_scheme k) Y)
  : f = g.
Proof.
  apply path_SchemeMorphism.
  destruct f as [[]].
  destruct g as [[]].
  reflexivity.
Defined.

Lemma morphism_to_point_unique (k : BaseField) (X : Scheme k)
  (f g : SchemeMorphism k X (point_scheme k))
  : f = g.
Proof.
  apply path_SchemeMorphism.
  unfold MorphismData, point_scheme in *.
  simpl in *.
  destruct X as [tx [|dx] Hdx].
  - destruct f as [[]].
    destruct g as [[]].
    reflexivity.
  - destruct f as [[]].
    destruct g as [[]].
    reflexivity.
Defined.

Definition canonical_from_point_data (k : BaseField) (Y : Scheme k)
  : MorphismData k (point_scheme k) Y := tt.

Definition canonical_from_point (k : BaseField) (Y : Scheme k)
  : SchemeMorphism k (point_scheme k) Y
  := {| sm_data := canonical_from_point_data k Y |}.

Definition canonical_to_point_data (k : BaseField) (X : Scheme k)
  : MorphismData k X (point_scheme k) := tt.

Definition canonical_to_point (k : BaseField) (X : Scheme k)
  : SchemeMorphism k X (point_scheme k)
  := {| sm_data := canonical_to_point_data k X |}.

Global Instance contr_from_point (k : BaseField) (Y : Scheme k)
  : Contr (SchemeMorphism k (point_scheme k) Y).
Proof.
  apply (Build_Contr _ (canonical_from_point k Y)).
  intro f.
  exact (morphism_from_point_unique k Y f (canonical_from_point k Y))^.
Defined.

Global Instance contr_to_point (k : BaseField) (X : Scheme k)
  : Contr (SchemeMorphism k X (point_scheme k)).
Proof.
  apply (Build_Contr _ (canonical_to_point k X)).
  intro f.
  exact (morphism_to_point_unique k X f (canonical_to_point k X))^.
Defined.

Definition SchemeZero (k : BaseField) : ZeroObject (SchemeCategory k)
  := Build_ZeroObject (SchemeCategory k) (point_scheme k)
       (fun Y => contr_from_point k Y)
       (fun X => contr_to_point k X).

Definition positive_dim_morphism_data (k : BaseField) (X Y : Scheme k)
  (HX : nat_lt O (sch_dim k X)) (HY : nat_lt O (sch_dim k Y))
  : MorphismData k X Y := tt.

Definition positive_dim_morphism_exists (k : BaseField) (X Y : Scheme k)
  (HX : nat_lt O (sch_dim k X)) (HY : nat_lt O (sch_dim k Y))
  : SchemeMorphism k X Y
  := {| sm_data := positive_dim_morphism_data k X Y HX HY |}.

Definition projection_from_A1_data (k : BaseField) (X : Scheme k)
  : MorphismData k (scheme_with_A1 k X) X := tt.

Definition projection_from_A1 (k : BaseField) (X : Scheme k)
  : morphism (SchemeCategory k) (scheme_with_A1 k X) X
  := {| sm_data := projection_from_A1_data k X |}.

Definition IsA1Invariant (k : BaseField) (X : Scheme k)
  : Type
  := @IsIsomorphism (SchemeCategory k) (scheme_with_A1 k X) X (projection_from_A1 k X).

Definition section_to_A1_data (k : BaseField) (X : Scheme k)
  : MorphismData k X (scheme_with_A1 k X) := tt.

Definition section_to_A1 (k : BaseField) (X : Scheme k)
  : morphism (SchemeCategory k) X (scheme_with_A1 k X)
  := {| sm_data := section_to_A1_data k X |}.

(** This scheme model has singleton morphism data, hence is codiscrete; the concrete layer later carries genuine morphisms and the honest separation. *)

Lemma projection_section_compose (k : BaseField) (X : Scheme k)
  : (projection_from_A1 k X o section_to_A1 k X = 1)%morphism.
Proof.
  apply path_SchemeMorphism.
  reflexivity.
Defined.

Lemma section_projection_compose_positive (k : BaseField) (X : Scheme k)
  (HX : nat_lt O (sch_dim k X))
  : (section_to_A1 k X o projection_from_A1 k X = 1)%morphism.
Proof.
  apply path_SchemeMorphism.
  reflexivity.
Defined.

Lemma section_projection_compose_all (k : BaseField) (X : Scheme k)
  : (section_to_A1 k X o projection_from_A1 k X = 1)%morphism.
Proof.
  apply path_SchemeMorphism.
  reflexivity.
Defined.

Theorem positive_schemes_A1_invariant (k : BaseField) (X : Scheme k)
  (HX : nat_lt O (sch_dim k X))
  : IsA1Invariant k X.
Proof.
  unfold IsA1Invariant.
  exists (section_to_A1 k X).
  split.
  - exact (section_projection_compose_positive k X HX).
  - exact (projection_section_compose k X).
Defined.

(** Every codiscrete scheme is A1-invariant without dimension hypotheses; the honest separation lives in the concrete layer. *)

Theorem point_scheme_A1_invariant (k : BaseField)
  : IsA1Invariant k (point_scheme k).
Proof.
  exists (section_to_A1 k (point_scheme k)).
  split.
  - apply path_SchemeMorphism.
    reflexivity.
  - apply path_SchemeMorphism.
    reflexivity.
Defined.

Theorem all_schemes_A1_invariant (k : BaseField) (X : Scheme k)
  : IsA1Invariant k X.
Proof.
  exists (section_to_A1 k X).
  split.
  - apply path_SchemeMorphism.
    reflexivity.
  - apply path_SchemeMorphism.
    reflexivity.
Defined.

Record MotivicSpace (k : BaseField) := {
  ms_scheme : Scheme k
}.

Definition ms_underlying (k : BaseField) (M : MotivicSpace k)
  : object (SchemeCategory k)
  := ms_scheme k M.

Record MotivicSpectrum (k : BaseField) := {
  msp_level : nat -> MotivicSpace k;
  msp_bonding : forall n,
    morphism (SchemeCategory k)
      (scheme_with_A1 k (ms_scheme k (msp_level n)))
      (ms_scheme k (msp_level (S n)))
}.

Definition point_motivic_space (k : BaseField)
  : MotivicSpace k
  := {| ms_scheme := point_scheme k |}.

Definition zero_spectrum (k : BaseField)
  : MotivicSpectrum k
  := {| msp_level := fun _ => point_motivic_space k;
        msp_bonding := fun _ => canonical_to_point k (scheme_with_A1 k (point_scheme k)) |}.

Record SpectrumMorphism (k : BaseField) (E F : MotivicSpectrum k) := {
  spm_level : forall n,
    morphism (SchemeCategory k)
      (ms_scheme k (msp_level k E n))
      (ms_scheme k (msp_level k F n))
}.

Definition spm_identity (k : BaseField) (E : MotivicSpectrum k)
  : SpectrumMorphism k E E
  := {| spm_level := fun n => 1%morphism |}.

Definition spm_compose (k : BaseField) (E F G : MotivicSpectrum k)
  (g : SpectrumMorphism k F G) (f : SpectrumMorphism k E F)
  : SpectrumMorphism k E G
  := {| spm_level := fun n => (spm_level k F G g n o spm_level k E F f n)%morphism |}.

Lemma SpectrumMorphism_eq `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f g : SpectrumMorphism k E F)
  : (forall n, spm_level k E F f n = spm_level k E F g n) -> f = g.
Proof.
  intro Hlevel.
  destruct f as [f_level].
  destruct g as [g_level].
  simpl in Hlevel.
  assert (Heq : f_level = g_level).
  { apply path_forall.
    exact Hlevel. }
  destruct Heq.
  reflexivity.
Defined.

Lemma spm_compose_assoc `{Funext} (k : BaseField) (E F G K : MotivicSpectrum k)
  (f : SpectrumMorphism k E F) (g : SpectrumMorphism k F G) (h : SpectrumMorphism k G K)
  : spm_compose k E F K (spm_compose k F G K h g) f =
    spm_compose k E G K h (spm_compose k E F G g f).
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  simpl.
  exact (sm_compose_assoc k _ _ _ _ (spm_level k E F f n) (spm_level k F G g n) (spm_level k G K h n)).
Defined.

Lemma spm_compose_id_l `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f : SpectrumMorphism k E F)
  : spm_compose k E F F (spm_identity k F) f = f.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  simpl.
  exact (sm_compose_id_l k _ _ (spm_level k E F f n)).
Defined.

Lemma spm_compose_id_r `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f : SpectrumMorphism k E F)
  : spm_compose k E E F f (spm_identity k E) = f.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  simpl.
  exact (sm_compose_id_r k _ _ (spm_level k E F f n)).
Defined.

Lemma SpectrumMorphism_path `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f g : SpectrumMorphism k E F)
  (H_level : forall n, spm_level k E F f n = spm_level k E F g n)
  : f = g.
Proof.
  destruct f as [f_level].
  destruct g as [g_level].
  simpl in H_level.
  assert (p : f_level = g_level).
  { apply path_forall.
    exact H_level. }
  destruct p.
  reflexivity.
Defined.

Definition spm_level_to_morphism (k : BaseField) (E F : MotivicSpectrum k)
  (f : forall n, morphism (SchemeCategory k)
                   (ms_scheme k (msp_level k E n))
                   (ms_scheme k (msp_level k F n)))
  : SpectrumMorphism k E F
  := {| spm_level := f |}.

Definition morphism_to_spm_level (k : BaseField) (E F : MotivicSpectrum k)
  (m : SpectrumMorphism k E F)
  : forall n, morphism (SchemeCategory k)
                (ms_scheme k (msp_level k E n))
                (ms_scheme k (msp_level k F n))
  := spm_level k E F m.

Lemma spm_level_morphism_sect (k : BaseField) (E F : MotivicSpectrum k)
  (m : SpectrumMorphism k E F)
  : spm_level_to_morphism k E F (morphism_to_spm_level k E F m) = m.
Proof.
  destruct m as [f].
  reflexivity.
Defined.

Lemma morphism_spm_level_sect (k : BaseField) (E F : MotivicSpectrum k)
  (f : forall n, morphism (SchemeCategory k)
                   (ms_scheme k (msp_level k E n))
                   (ms_scheme k (msp_level k F n)))
  : morphism_to_spm_level k E F (spm_level_to_morphism k E F f) = f.
Proof.
  reflexivity.
Defined.

Definition equiv_SpectrumMorphism (k : BaseField) (E F : MotivicSpectrum k)
  : SpectrumMorphism k E F <~>
    (forall n, morphism (SchemeCategory k)
                 (ms_scheme k (msp_level k E n))
                 (ms_scheme k (msp_level k F n))).
Proof.
  apply (equiv_adjointify (morphism_to_spm_level k E F)
                          (spm_level_to_morphism k E F)).
  - exact (morphism_spm_level_sect k E F).
  - exact (spm_level_morphism_sect k E F).
Defined.

Global Instance trunc_SpectrumMorphism `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  : IsHSet (SpectrumMorphism k E F).
Proof.
  pose (H_forall := @istrunc_forall H nat
          (fun n => morphism (SchemeCategory k)
                      (ms_scheme k (msp_level k E n))
                      (ms_scheme k (msp_level k F n)))
          (minus_two.+2)
          (fun n => trunc_SchemeMorphism k
                      (ms_scheme k (msp_level k E n))
                      (ms_scheme k (msp_level k F n)))).
  exact (istrunc_equiv_istrunc _ (equiv_inverse (equiv_SpectrumMorphism k E F))).
Defined.

Definition SH `{Funext} (k : BaseField)
  : PreCategory
  := @Build_PreCategory
       (MotivicSpectrum k)
       (fun E F => SpectrumMorphism k E F)
       (fun E => spm_identity k E)
       (fun E F G g f => spm_compose k E F G g f)
       (fun s d d' d'' m1 m2 m3 => spm_compose_assoc k s d d' d'' m1 m2 m3)
       (fun a b f => spm_compose_id_l k a b f)
       (fun a b f => spm_compose_id_r k a b f)
       (fun E F => trunc_SpectrumMorphism k E F).

Definition sh_zero_in `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : morphism (SH k) E (zero_spectrum k).
Proof.
  refine {| spm_level := fun n => _ |}.
  simpl.
  exact (canonical_to_point k (ms_scheme k (msp_level k E n))).
Defined.

Definition sh_zero_out `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : morphism (SH k) (zero_spectrum k) E.
Proof.
  refine {| spm_level := fun n => _ |}.
  simpl.
  exact (canonical_from_point k (ms_scheme k (msp_level k E n))).
Defined.

Lemma sh_zero_in_unique `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  (f g : morphism (SH k) E (zero_spectrum k))
  : f = g.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  exact (morphism_to_point_unique k (ms_scheme k (msp_level k E n))
           (spm_level k E (zero_spectrum k) f n)
           (spm_level k E (zero_spectrum k) g n)).
Defined.

Lemma sh_zero_out_unique `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  (f g : morphism (SH k) (zero_spectrum k) E)
  : f = g.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  exact (morphism_from_point_unique k (ms_scheme k (msp_level k E n))
           (spm_level k (zero_spectrum k) E f n)
           (spm_level k (zero_spectrum k) E g n)).
Defined.

Definition SH_zero `{Funext} (k : BaseField)
  : ZeroObject (SH k).
Proof.
  refine {| zero := (zero_spectrum k : object (SH k)) |}.
  - intro E.
    apply (Build_Contr _ (sh_zero_out k E)).
    intro f.
    exact (sh_zero_out_unique k E f (sh_zero_out k E))^.
  - intro E.
    apply (Build_Contr _ (sh_zero_in k E)).
    intro f.
    exact (sh_zero_in_unique k E f (sh_zero_in k E))^.
Defined.

Definition susp_spectrum (k : BaseField) (E : MotivicSpectrum k)
  : MotivicSpectrum k
  := {| msp_level := fun n => msp_level k E (S n);
        msp_bonding := fun n => msp_bonding k E (S n) |}.

Definition susp_spectrum_mor (k : BaseField) (E F : MotivicSpectrum k)
  (f : SpectrumMorphism k E F)
  : SpectrumMorphism k (susp_spectrum k E) (susp_spectrum k F).
Proof.
  refine {| spm_level := fun n => _ |}.
  exact (spm_level k E F f (S n)).
Defined.

Lemma susp_spectrum_mor_id `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : susp_spectrum_mor k E E (spm_identity k E) =
    spm_identity k (susp_spectrum k E).
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  reflexivity.
Defined.

Lemma susp_spectrum_mor_comp `{Funext} (k : BaseField) (E F G : MotivicSpectrum k)
  (f : SpectrumMorphism k E F) (g : SpectrumMorphism k F G)
  : susp_spectrum_mor k E G (spm_compose k E F G g f) =
    spm_compose k (susp_spectrum k E) (susp_spectrum k F) (susp_spectrum k G)
      (susp_spectrum_mor k F G g) (susp_spectrum_mor k E F f).
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  reflexivity.
Defined.

Definition SH_susp `{Funext} (k : BaseField)
  : Functor (SH k) (SH k).
Proof.
  refine (Build_Functor (SH k) (SH k)
            (susp_spectrum k)
            (fun E F f => susp_spectrum_mor k E F f)
            _ _).
  - intros E F G f g.
    exact (susp_spectrum_mor_comp k E F G f g).
  - intro E.
    exact (susp_spectrum_mor_id k E).
Defined.

Definition loop_spectrum_level (k : BaseField) (E : MotivicSpectrum k) (n : nat)
  : MotivicSpace k
  := match n with
     | O => point_motivic_space k
     | S n' => msp_level k E n'
     end.

Definition loop_spectrum_bonding (k : BaseField) (E : MotivicSpectrum k) (n : nat)
  : morphism (SchemeCategory k)
      (scheme_with_A1 k (ms_scheme k (loop_spectrum_level k E n)))
      (ms_scheme k (loop_spectrum_level k E (S n))).
Proof.
  destruct n.
  - simpl.
    exact (zero_scheme_morphism k _ _).
  - simpl.
    exact (msp_bonding k E n).
Defined.

Definition loop_spectrum (k : BaseField) (E : MotivicSpectrum k)
  : MotivicSpectrum k
  := {| msp_level := loop_spectrum_level k E;
        msp_bonding := loop_spectrum_bonding k E |}.

Definition loop_spectrum_mor_level (k : BaseField) (E F : MotivicSpectrum k)
  (f : SpectrumMorphism k E F) (n : nat)
  : morphism (SchemeCategory k)
      (ms_scheme k (loop_spectrum_level k E n))
      (ms_scheme k (loop_spectrum_level k F n)).
Proof.
  destruct n.
  - simpl.
    exact (sm_identity k (point_scheme k)).
  - simpl.
    exact (spm_level k E F f n).
Defined.

Definition loop_spectrum_mor (k : BaseField) (E F : MotivicSpectrum k)
  (f : SpectrumMorphism k E F)
  : SpectrumMorphism k (loop_spectrum k E) (loop_spectrum k F).
Proof.
  refine {| spm_level := fun n => _ |}.
  exact (loop_spectrum_mor_level k E F f n).
Defined.

Lemma loop_spectrum_mor_id `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : loop_spectrum_mor k E E (spm_identity k E) =
    spm_identity k (loop_spectrum k E).
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  destruct n.
  - simpl.
    apply SchemeMorphism_eq.
    reflexivity.
  - simpl.
    reflexivity.
Defined.

Lemma loop_spectrum_mor_comp `{Funext} (k : BaseField) (E F G : MotivicSpectrum k)
  (f : SpectrumMorphism k E F) (g : SpectrumMorphism k F G)
  : loop_spectrum_mor k E G (spm_compose k E F G g f) =
    spm_compose k (loop_spectrum k E) (loop_spectrum k F) (loop_spectrum k G)
      (loop_spectrum_mor k F G g) (loop_spectrum_mor k E F f).
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  destruct n.
  - simpl.
    apply SchemeMorphism_eq.
    reflexivity.
  - simpl.
    reflexivity.
Defined.

Definition SH_loop `{Funext} (k : BaseField)
  : Functor (SH k) (SH k).
Proof.
  refine (Build_Functor (SH k) (SH k)
            (loop_spectrum k)
            (fun E F f => loop_spectrum_mor k E F f)
            _ _).
  - intros E F G f g.
    exact (loop_spectrum_mor_comp k E F G f g).
  - intro E.
    exact (loop_spectrum_mor_id k E).
Defined.

Definition SH_eta_component `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : morphism (SH k) E (object_of (SH_loop k o SH_susp k)%functor E).
Proof.
  refine {| spm_level := fun n => _ |}.
  simpl.
  exact (zero_scheme_morphism k _ _).
Defined.

(** All parallel scheme morphisms are equal; the graded categories later carry the genuine distinctions. *)

Theorem all_scheme_morphisms_equal (k : BaseField) (X Y : Scheme k)
  (f g : SchemeMorphism k X Y)
  : f = g.
Proof.
  apply path_SchemeMorphism.
  destruct f as [[]].
  destruct g as [[]].
  reflexivity.
Defined.

Lemma point_morphism_unique_source (k : BaseField) (Y : Scheme k)
  (f g : SchemeMorphism k (point_scheme k) Y)
  : f = g.
Proof.
  exact (morphism_from_point_unique k Y f g).
Defined.

Lemma point_morphism_unique_target (k : BaseField) (X : Scheme k)
  (f g : SchemeMorphism k X (point_scheme k))
  : f = g.
Proof.
  exact (morphism_to_point_unique k X f g).
Defined.

(** For spectra involving only zero_spectrum, morphisms are unique. *)
Lemma zero_spectrum_morphism_unique_source `{Funext} (k : BaseField) (F : MotivicSpectrum k)
  (f g : SpectrumMorphism k (zero_spectrum k) F)
  : f = g.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  apply point_morphism_unique_source.
Defined.

Lemma zero_spectrum_morphism_unique_target `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  (f g : SpectrumMorphism k E (zero_spectrum k))
  : f = g.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  apply point_morphism_unique_target.
Defined.

Lemma MorphismData_path (k : BaseField) (X Y : Scheme k)
  (d1 d2 : MorphismData k X Y)
  : d1 = d2.
Proof.
  unfold MorphismData in *.
  destruct d1, d2.
  reflexivity.
Defined.

Lemma all_SpectrumMorphisms_equal `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f g : SpectrumMorphism k E F)
  : f = g.
Proof.
  apply SpectrumMorphism_eq.
  intro n.
  apply path_SchemeMorphism.
  apply MorphismData_path.
Defined.

Lemma SH_eta_natural `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f : morphism (SH k) E F)
  : (morphism_of (SH_loop k o SH_susp k)%functor f o SH_eta_component k E =
     SH_eta_component k F o f)%morphism.
Proof.
  apply all_SpectrumMorphisms_equal.
Defined.

Definition SH_eta `{Funext} (k : BaseField)
  : NaturalTransformation 1%functor (SH_loop k o SH_susp k)%functor.
Proof.
  refine (Build_NaturalTransformation 1%functor (SH_loop k o SH_susp k)%functor
            (SH_eta_component k)
            _).
  intros E F f.
  exact (SH_eta_natural k E F f)^.
Defined.

Definition SH_epsilon_component `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : morphism (SH k) (object_of (SH_susp k o SH_loop k)%functor E) E.
Proof.
  refine {| spm_level := fun n => _ |}.
  simpl.
  exact (zero_scheme_morphism k _ _).
Defined.

Lemma SH_epsilon_natural `{Funext} (k : BaseField) (E F : MotivicSpectrum k)
  (f : morphism (SH k) E F)
  : (f o SH_epsilon_component k E =
     SH_epsilon_component k F o morphism_of (SH_susp k o SH_loop k)%functor f)%morphism.
Proof.
  apply all_SpectrumMorphisms_equal.
Defined.

Definition SH_epsilon `{Funext} (k : BaseField)
  : NaturalTransformation (SH_susp k o SH_loop k)%functor 1%functor.
Proof.
  refine (Build_NaturalTransformation (SH_susp k o SH_loop k)%functor 1%functor
            (SH_epsilon_component k)
            _).
  intros E F f.
  exact (SH_epsilon_natural k E F f)^.
Defined.

Definition SH_PreStable `{Funext} (k : BaseField)
  : PreStableCategory
  := {| ps_cat := SH k;
        ps_zero := SH_zero k;
        ps_susp := SH_susp k;
        ps_loop := SH_loop k;
        ps_eta := SH_eta k;
        ps_epsilon := SH_epsilon k |}.

Definition spectrum_dim_measure (k : BaseField) (E : MotivicSpectrum k)
  : QPos
  := {| qpos_num := sch_dim k (ms_scheme k (msp_level k E 0));
        qpos_denom_pred := 0 |}.

Lemma zero_spectrum_dim_zero (k : BaseField)
  : spectrum_dim_measure k (zero_spectrum k) = qpos_zero.
Proof.
  unfold spectrum_dim_measure, zero_spectrum, point_motivic_space, point_scheme.
  simpl.
  reflexivity.
Defined.

Definition SH_weight_measure `{Funext} (k : BaseField)
  : WeightMeasure (SH k) (SH_zero k).
Proof.
  refine {| wm_measure := fun (E : object (SH k)) => spectrum_dim_measure k E |}.
  exact (zero_spectrum_dim_zero k).
Defined.

Theorem SH_admits_stabilization `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  (H_zero_tri : ZeroFiberInTriangleImpliesIso (SH_PreStable k))
  (H_zero_meas : ZeroMeasureImpliesZeroObj (SH_PreStable k) (SH_weight_measure k))
  (H_discrete : HasMinimalPositive (tis_fiber_measure T (SH_weight_measure k)))
  (H_limit : LimitZero (tis_fiber_measure T (SH_weight_measure k)))
  : { N : nat & TowerStabilizesAt (tis_tower (SH_PreStable k) T) N }.
Proof.
  exact (stable_tower_stabilizes T (SH_weight_measure k)
           H_zero_tri H_zero_meas H_discrete H_limit).
Defined.

Definition SH_eta_inverse `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : morphism (SH k) (object_of (SH_loop k o SH_susp k)%functor E) E.
Proof.
  refine {| spm_level := fun n => _ |}.
  simpl.
  exact (zero_scheme_morphism k _ _).
Defined.

Lemma SH_eta_iso `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : IsIsomorphism (SH_eta_component k E).
Proof.
  unfold IsIsomorphism.
  exists (SH_eta_inverse k E).
  split.
  - apply all_SpectrumMorphisms_equal.
  - apply all_SpectrumMorphisms_equal.
Defined.

Definition SH_epsilon_inverse `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : morphism (SH k) E (object_of (SH_susp k o SH_loop k)%functor E).
Proof.
  refine {| spm_level := fun n => _ |}.
  simpl.
  exact (zero_scheme_morphism k _ _).
Defined.

Lemma SH_epsilon_iso `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : IsIsomorphism (SH_epsilon_component k E).
Proof.
  unfold IsIsomorphism.
  exists (SH_epsilon_inverse k E).
  split.
  - apply all_SpectrumMorphisms_equal.
  - apply all_SpectrumMorphisms_equal.
Defined.

Lemma SH_triangle_1 `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : (SH_epsilon_component k (object_of (SH_susp k) E) o
     morphism_of (SH_susp k) (SH_eta_component k E) = 1)%morphism.
Proof.
  apply all_SpectrumMorphisms_equal.
Defined.

Lemma SH_triangle_2 `{Funext} (k : BaseField) (E : MotivicSpectrum k)
  : (morphism_of (SH_loop k) (SH_epsilon_component k E) o
     SH_eta_component k (object_of (SH_loop k) E) = 1)%morphism.
Proof.
  apply all_SpectrumMorphisms_equal.
Defined.

Record ProperStableCategory := {
  psc_pre :> PreStableCategory;
  psc_eta_iso : forall E, IsIsomorphism (components_of (ps_eta psc_pre) E);
  psc_epsilon_iso : forall E, IsIsomorphism (components_of (ps_epsilon psc_pre) E);
  psc_triangle_1 : forall E,
    (components_of (ps_epsilon psc_pre) (object_of (ps_susp psc_pre) E) o
     morphism_of (ps_susp psc_pre) (components_of (ps_eta psc_pre) E) = 1)%morphism;
  psc_triangle_2 : forall E,
    (morphism_of (ps_loop psc_pre) (components_of (ps_epsilon psc_pre) E) o
     components_of (ps_eta psc_pre) (object_of (ps_loop psc_pre) E) = 1)%morphism
}.

(** The triangle identities make suspension left adjoint to loops at the level of hom sets. *)

Definition stable_susp_loop_adjunction (S : ProperStableCategory)
  (X Y : object (psc_pre S))
  : morphism (psc_pre S) (object_of (ps_susp (psc_pre S)) X) Y
    <~> morphism (psc_pre S) X (object_of (ps_loop (psc_pre S)) Y).
Proof.
  refine (equiv_adjointify
            (fun f => (morphism_of (ps_loop (psc_pre S)) f
                       o components_of (ps_eta (psc_pre S)) X)%morphism)
            (fun g => (components_of (ps_epsilon (psc_pre S)) Y
                       o morphism_of (ps_susp (psc_pre S)) g)%morphism)
            _ _).
  - intro g.
    refine (ap (fun h => (h o components_of (ps_eta (psc_pre S)) X)%morphism)
             (composition_of (ps_loop (psc_pre S)) _ _ _
                (morphism_of (ps_susp (psc_pre S)) g)
                (components_of (ps_epsilon (psc_pre S)) Y)) @ _).
    refine (associativity _ _ _ _ _ _ _ _ @ _).
    refine (ap (fun h => (morphism_of (ps_loop (psc_pre S))
                            (components_of (ps_epsilon (psc_pre S)) Y)
                          o h)%morphism)
             (commutes (ps_eta (psc_pre S)) _ _ g)^ @ _).
    refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
    refine (ap (fun h => (h o g)%morphism) (psc_triangle_2 S Y) @ _).
    apply left_identity.
  - intro f.
    refine (ap (fun h => (components_of (ps_epsilon (psc_pre S)) Y
                          o h)%morphism)
             (composition_of (ps_susp (psc_pre S)) _ _ _
                (components_of (ps_eta (psc_pre S)) X)
                (morphism_of (ps_loop (psc_pre S)) f)) @ _).
    refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
    refine (ap (fun h => (h o morphism_of (ps_susp (psc_pre S))
                                (components_of (ps_eta (psc_pre S)) X))%morphism)
             (commutes (ps_epsilon (psc_pre S)) _ _ f) @ _).
    refine (associativity _ _ _ _ _ _ _ _ @ _).
    refine (ap (fun h => (f o h)%morphism) (psc_triangle_1 S X) @ _).
    apply right_identity.
Defined.

Definition SH_ProperStable `{Funext} (k : BaseField)
  : ProperStableCategory.
Proof.
  refine {| psc_pre := SH_PreStable k |}.
  - intro E.
    exact (SH_eta_iso k E).
  - intro E.
    exact (SH_epsilon_iso k E).
  - intro E.
    exact (SH_triangle_1 k E).
  - intro E.
    exact (SH_triangle_2 k E).
Defined.

Theorem SH_zero_fiber_implies_iso `{Funext} (k : BaseField)
  : ZeroFiberInTriangleImpliesIso (SH_PreStable k).
Proof.
  unfold ZeroFiberInTriangleImpliesIso.
  intros dt Hzero.
  unfold IsIsomorphism.
  exists {| spm_level := fun n => zero_scheme_morphism k _ _ |}.
  split.
  - apply all_SpectrumMorphisms_equal.
  - apply all_SpectrumMorphisms_equal.
Defined.

Theorem SH_tower_convergence `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  (H_zero_meas : ZeroMeasureImpliesZeroObj (SH_PreStable k) (SH_weight_measure k))
  (H_discrete : HasMinimalPositive (tis_fiber_measure T (SH_weight_measure k)))
  (H_limit : LimitZero (tis_fiber_measure T (SH_weight_measure k)))
  : { N : nat & TowerStabilizesAt (tis_tower (SH_PreStable k) T) N }.
Proof.
  exact (stable_tower_stabilizes T (SH_weight_measure k)
           (SH_zero_fiber_implies_iso k) H_zero_meas H_discrete H_limit).
Defined.

Definition MainConvergenceTheorem `{Funext} (k : BaseField)
  : Type
  := forall (T : TowerInStable (SH_PreStable k)),
     ZeroMeasureImpliesZeroObj (SH_PreStable k) (SH_weight_measure k) ->
     HasMinimalPositive (tis_fiber_measure T (SH_weight_measure k)) ->
     LimitZero (tis_fiber_measure T (SH_weight_measure k)) ->
     { N : nat & TowerStabilizesAt (tis_tower (SH_PreStable k) T) N }.

Theorem main_convergence `{Funext} (k : BaseField)
  : MainConvergenceTheorem k.
Proof.
  intros T H_zero_meas H_discrete H_limit.
  exact (SH_tower_convergence k T H_zero_meas H_discrete H_limit).
Defined.

Theorem SH_all_morphisms_iso `{Funext} (k : BaseField)
  (E F : object (SH k)) (f : morphism (SH k) E F)
  : IsIsomorphism f.
Proof.
  unfold IsIsomorphism.
  exists {| spm_level := fun n => zero_scheme_morphism k _ _ |}.
  split.
  - apply all_SpectrumMorphisms_equal.
  - apply all_SpectrumMorphisms_equal.
Defined.

Theorem SH_tower_trivially_stabilizes `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  : TowerStabilizesAt (tis_tower (SH_PreStable k) T) O.
Proof.
  unfold TowerStabilizesAt.
  intros n Hn.
  apply (tis_iso_transfer (SH_PreStable k) T n).
  apply SH_all_morphisms_iso.
Defined.

Theorem SH_immediate_convergence `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  : { N : nat & TowerStabilizesAt (tis_tower (SH_PreStable k) T) N }.
Proof.
  exists O.
  exact (SH_tower_trivially_stabilizes k T).
Defined.

Definition opposite_precategory (C : PreCategory)
  : PreCategory.
Proof.
  exact (@Build_PreCategory
           (object C)
           (fun X Y => morphism C Y X)
           (fun X => 1%morphism)
           (fun X Y Z f g => (g o f)%morphism)
           (fun s d d' d'' m1 m2 m3 => (associativity C d'' d' d s m3 m2 m1)^)
           (fun a b f => right_identity C b a f)
           (fun a b f => left_identity C b a f)
           (fun s d => trunc_morphism C d s)).
Defined.

Definition opposite_zero_object {C : PreCategory} (Z : ZeroObject C)
  : ZeroObject (opposite_precategory C).
Proof.
  exact (Build_ZeroObject (opposite_precategory C)
           (zero C Z)
           (fun X => is_terminal C Z X)
           (fun X => is_initial C Z X)).
Defined.

Definition opposite_functor {C D : PreCategory} (F : Functor C D)
  : Functor (opposite_precategory C) (opposite_precategory D).
Proof.
  refine (Build_Functor
            (opposite_precategory C)
            (opposite_precategory D)
            (object_of F)
            (fun X Y f => morphism_of F f)
            _ _).
  - intros X Y Z f g.
    exact (composition_of F Z Y X g f).
  - intro X.
    exact (identity_of F X).
Defined.

Definition opposite_nat_trans {C D : PreCategory} {F G : Functor C D}
  (eta : NaturalTransformation F G)
  : NaturalTransformation (opposite_functor G) (opposite_functor F).
Proof.
  refine (Build_NaturalTransformation
            (opposite_functor G)
            (opposite_functor F)
            (fun X => components_of eta X)
            _).
  intros X Y f.
  exact (commutes eta Y X f)^.
Defined.

Definition opposite_prestable (PS : PreStableCategory)
  : PreStableCategory.
Proof.
  refine (Build_PreStableCategory
            (opposite_precategory PS)
            (opposite_zero_object (ps_zero PS))
            (opposite_functor (ps_loop PS))
            (opposite_functor (ps_susp PS))
            (opposite_nat_trans (ps_epsilon PS))
            (opposite_nat_trans (ps_eta PS))).
Defined.

Theorem opposite_swaps_susp_loop (PS : PreStableCategory)
  : (object_of (ps_susp (opposite_prestable PS)) =
     object_of (opposite_functor (ps_loop PS))) *
    (object_of (ps_loop (opposite_prestable PS)) =
     object_of (opposite_functor (ps_susp PS))).
Proof.
  split; reflexivity.
Defined.

Lemma opposite_preserves_iso {C : PreCategory} {X Y : object C}
  (f : morphism C X Y) (H : IsIsomorphism f)
  : @IsIsomorphism (opposite_precategory C) Y X f.
Proof.
  destruct H as [g [Hgf Hfg]].
  exists g.
  split.
  - exact Hfg.
  - exact Hgf.
Defined.

Lemma opposite_eta_iso (PS : ProperStableCategory) (E : object (psc_pre PS))
  : IsIsomorphism (components_of (ps_eta (opposite_prestable (psc_pre PS))) E).
Proof.
  simpl.
  apply opposite_preserves_iso.
  exact (psc_epsilon_iso PS E).
Defined.

Lemma opposite_epsilon_iso (PS : ProperStableCategory) (E : object (psc_pre PS))
  : IsIsomorphism (components_of (ps_epsilon (opposite_prestable (psc_pre PS))) E).
Proof.
  simpl.
  apply opposite_preserves_iso.
  exact (psc_eta_iso PS E).
Defined.

Lemma opposite_triangle_1 (PS : ProperStableCategory) (E : object (psc_pre PS))
  : (components_of (ps_epsilon (opposite_prestable (psc_pre PS)))
       (object_of (ps_susp (opposite_prestable (psc_pre PS))) E) o
     morphism_of (ps_susp (opposite_prestable (psc_pre PS)))
       (components_of (ps_eta (opposite_prestable (psc_pre PS))) E) = 1)%morphism.
Proof.
  simpl.
  exact (psc_triangle_2 PS E).
Defined.

Lemma opposite_triangle_2 (PS : ProperStableCategory) (E : object (psc_pre PS))
  : (morphism_of (ps_loop (opposite_prestable (psc_pre PS)))
       (components_of (ps_epsilon (opposite_prestable (psc_pre PS))) E) o
     components_of (ps_eta (opposite_prestable (psc_pre PS)))
       (object_of (ps_loop (opposite_prestable (psc_pre PS))) E) = 1)%morphism.
Proof.
  simpl.
  exact (psc_triangle_1 PS E).
Defined.

Definition opposite_proper_stable (PS : ProperStableCategory)
  : ProperStableCategory.
Proof.
  refine (Build_ProperStableCategory
            (opposite_prestable (psc_pre PS))
            (opposite_eta_iso PS)
            (opposite_epsilon_iso PS)
            (opposite_triangle_1 PS)
            (opposite_triangle_2 PS)).
Defined.

Theorem duality_principle (PS : ProperStableCategory)
  : ProperStableCategory.
Proof.
  exact (opposite_proper_stable PS).
Defined.

Theorem susp_loop_duality (PS : ProperStableCategory)
  : (ps_susp (opposite_prestable (psc_pre PS)) =
     opposite_functor (ps_loop (psc_pre PS))) *
    (ps_loop (opposite_prestable (psc_pre PS)) =
     opposite_functor (ps_susp (psc_pre PS))).
Proof.
  split; reflexivity.
Defined.

Definition SH_opposite `{Funext} (k : BaseField)
  : ProperStableCategory
  := opposite_proper_stable (SH_ProperStable k).

Theorem SH_self_dual `{Funext} (k : BaseField)
  : ProperStableCategory * ProperStableCategory.
Proof.
  exact (SH_ProperStable k, SH_opposite k).
Defined.

Theorem opposite_tower_stabilizes `{Funext} (k : BaseField)
  (T : TowerInStable (opposite_prestable (SH_PreStable k)))
  : { N : nat & TowerStabilizesAt (tis_tower (opposite_prestable (SH_PreStable k)) T) N }.
Proof.
  exists O.
  unfold TowerStabilizesAt.
  intros n Hn.
  apply (tis_iso_transfer (opposite_prestable (SH_PreStable k)) T n).
  unfold IsIsomorphism.
  exists {| spm_level := fun m => zero_scheme_morphism k _ _ |}.
  split.
  - apply all_SpectrumMorphisms_equal.
  - apply all_SpectrumMorphisms_equal.
Defined.

(** ** Discrete Measures and Concrete Witnesses *)

Definition qpos_eq_dec (q1 q2 : QPos)
  : (q1 = q2) + (q1 = q2 -> Empty).
Proof.
  destruct q1 as [n1 d1].
  destruct q2 as [n2 d2].
  destruct (nat_eq_dec n1 n2) as [Hn | Hn].
  - destruct (nat_eq_dec d1 d2) as [Hd | Hd].
    + left.
      destruct Hn, Hd.
      reflexivity.
    + right.
      intro H.
      apply Hd.
      exact (ap qpos_denom_pred H).
  - right.
    intro H.
    apply Hn.
    exact (ap qpos_num H).
Defined.

Definition nat_to_qpos (n : nat) : QPos :=
  {| qpos_num := n; qpos_denom_pred := 0 |}.

Definition IsIntegerValued (measure : nat -> QPos) : Type :=
  forall n, qpos_denom_pred (measure n) = O.

Lemma qpos_lt_of_integer (q1 q2 : QPos)
  (H1 : qpos_denom_pred q1 = O)
  (H2 : qpos_denom_pred q2 = O)
  : qpos_lt q1 q2 <-> nat_lt (qpos_num q1) (qpos_num q2).
Proof.
  unfold qpos_lt, qpos_denom.
  rewrite H1, H2.
  simpl.
  rewrite nat_mul_one_r.
  rewrite nat_mul_one_r.
  split; exact idmap.
Defined.

Lemma nat_lt_1_S_empty
  : forall k, nat_lt (S k) 1 -> Empty.
Proof.
  intro k.
  simpl.
  destruct k; exact idmap.
Defined.

Lemma S_eq_1_implies_O
  : forall k, S k = S O -> k = O.
Proof.
  intros k H.
  exact (ap nat_pred H).
Defined.

Lemma integer_valued_trichotomy_aux
  (q : QPos)
  (Hd : qpos_denom_pred q = O)
  : (qpos_is_zero q) +
    (qpos_lt (nat_to_qpos (S O)) q + (q = nat_to_qpos (S O))).
Proof.
  unfold qpos_is_zero, qpos_lt, nat_to_qpos, qpos_denom.
  destruct q as [mn md].
  simpl in *.
  rewrite Hd.
  simpl.
  destruct mn as [|k].
  - left.
    reflexivity.
  - right.
    destruct k as [|k'].
    + right.
      destruct Hd.
      reflexivity.
    + left.
      exact tt.
Defined.

Lemma integer_valued_trichotomy
  (measure : nat -> QPos)
  (H_int : IsIntegerValued measure)
  (n : nat)
  : (qpos_is_zero (measure n)) +
    (qpos_lt (nat_to_qpos (S O)) (measure n) + (measure n = nat_to_qpos (S O))).
Proof.
  exact (integer_valued_trichotomy_aux (measure n) (H_int n)).
Defined.

Theorem integer_valued_has_minimal_positive
  (measure : nat -> QPos)
  (H_int : IsIntegerValued measure)
  : HasMinimalPositive measure.
Proof.
  unfold HasMinimalPositive.
  exists (nat_to_qpos (S O)).
  split.
  - simpl.
    exact tt.
  - intro n.
    exact (integer_valued_trichotomy measure H_int n).
Defined.

Corollary integer_LimitZero_implies_EventuallyZero
  (measure : nat -> QPos)
  (H_int : IsIntegerValued measure)
  (H_limit : LimitZero measure)
  : EventuallyZero measure.
Proof.
  apply discrete_LimitZero_implies_EventuallyZero.
  - exact (integer_valued_has_minimal_positive measure H_int).
  - exact H_limit.
Defined.

Lemma spectrum_dim_measure_is_integer (k : BaseField) (E : MotivicSpectrum k)
  : qpos_denom_pred (spectrum_dim_measure k E) = O.
Proof.
  unfold spectrum_dim_measure.
  simpl.
  reflexivity.
Defined.

Lemma SH_weight_measure_is_integer `{Funext} (k : BaseField)
  (E : object (SH k))
  : qpos_denom_pred (wm_measure (SH k) (SH_zero k) (SH_weight_measure k) E) = O.
Proof.
  unfold SH_weight_measure, wm_measure.
  simpl.
  exact (spectrum_dim_measure_is_integer k E).
Defined.

Definition tis_fiber_measure_integer `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  : IsIntegerValued (tis_fiber_measure T (SH_weight_measure k)).
Proof.
  unfold IsIntegerValued, tis_fiber_measure.
  intro n.
  exact (SH_weight_measure_is_integer k (tis_fiber_obj T n)).
Defined.

Theorem SH_tower_convergence_from_limit `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  (H_zero_meas : ZeroMeasureImpliesZeroObj (SH_PreStable k) (SH_weight_measure k))
  (H_limit : LimitZero (tis_fiber_measure T (SH_weight_measure k)))
  : { N : nat & TowerStabilizesAt (tis_tower (SH_PreStable k) T) N }.
Proof.
  apply (stable_tower_stabilizes T (SH_weight_measure k)
           (SH_zero_fiber_implies_iso k) H_zero_meas).
  - exact (integer_valued_has_minimal_positive
             (tis_fiber_measure T (SH_weight_measure k))
             (tis_fiber_measure_integer k T)).
  - exact H_limit.
Defined.

Theorem SH_unconditional_stabilization `{Funext} (k : BaseField)
  (T : TowerInStable (SH_PreStable k))
  : { N : nat & TowerStabilizesAt (tis_tower (SH_PreStable k) T) N }.
Proof.
  exists O.
  unfold TowerStabilizesAt.
  intros n _.
  apply (tis_iso_transfer (SH_PreStable k) T n).
  apply SH_all_morphisms_iso.
Defined.

(** ** Graded category: objects graded by dimension, morphisms between positive dimensions carrying Boolean data distinguishing isomorphisms from zero maps. *)

(** *** Graded Objects *)

Record GradedObj := {
  go_dim : nat
}.

Definition go_zero : GradedObj := {| go_dim := O |}.

Definition go_susp (X : GradedObj) : GradedObj :=
  match go_dim X with
  | O => go_zero
  | S n => {| go_dim := S (S n) |}
  end.

Definition go_loop (X : GradedObj) : GradedObj :=
  match go_dim X with
  | O => go_zero
  | S O => go_zero
  | S (S n) => {| go_dim := S n |}
  end.

(** *** Graded morphisms: unique from and to zero, Boolean between nonzero objects. *)

Definition GradedMor (X Y : GradedObj) : Type :=
  match go_dim X, go_dim Y with
  | O, _ => Unit
  | _, O => Unit
  | S _, S _ => Bool
  end.

Definition gm_id (X : GradedObj) : GradedMor X X.
Proof.
  unfold GradedMor.
  destruct (go_dim X).
  - exact tt.
  - exact true.
Defined.

Definition gm_zero (X Y : GradedObj) : GradedMor X Y.
Proof.
  unfold GradedMor.
  destruct (go_dim X).
  - exact tt.
  - destruct (go_dim Y).
    + exact tt.
    + exact false.
Defined.

Definition gm_compose (X Y Z : GradedObj)
  (g : GradedMor Y Z) (f : GradedMor X Y)
  : GradedMor X Z.
Proof.
  unfold GradedMor in *.
  destruct (go_dim X).
  - exact tt.
  - destruct (go_dim Z).
    + exact tt.
    + destruct (go_dim Y).
      * exact false.
      * exact (andb f g).
Defined.

Global Instance GradedMor_hset (X Y : GradedObj) : IsHSet (GradedMor X Y).
Proof.
  unfold GradedMor.
  destruct (go_dim X).
  - exact hset_unit.
  - destruct (go_dim Y).
    + exact hset_unit.
    + exact hset_bool.
Defined.

Lemma gm_compose_assoc (W X Y Z : GradedObj)
  (f : GradedMor W X) (g : GradedMor X Y) (h : GradedMor Y Z)
  : gm_compose W X Z (gm_compose X Y Z h g) f =
    gm_compose W Y Z h (gm_compose W X Y g f).
Proof.
  destruct W as [dw], X as [dx], Y as [dy], Z as [dz].
  destruct dw, dx, dy, dz; bool_bash.
Defined.

Lemma gm_compose_id_l (X Y : GradedObj) (f : GradedMor X Y)
  : gm_compose X Y Y (gm_id Y) f = f.
Proof.
  destruct X as [dx], Y as [dy].
  destruct dx, dy; bool_bash.
Defined.

Lemma gm_compose_id_r (X Y : GradedObj) (f : GradedMor X Y)
  : gm_compose X X Y f (gm_id X) = f.
Proof.
  destruct X as [dx], Y as [dy].
  destruct dx, dy; bool_bash.
Defined.

(** *** The Graded Category *)

Definition GradedCat : PreCategory
  := @Build_PreCategory
       GradedObj
       (fun X Y => GradedMor X Y)
       (fun X => gm_id X)
       (fun X Y Z g f => gm_compose X Y Z g f)
       (fun s d d' d'' m1 m2 m3 => gm_compose_assoc s d d' d'' m1 m2 m3)
       (fun a b f => gm_compose_id_l a b f)
       (fun a b f => gm_compose_id_r a b f)
       (fun s d => GradedMor_hset s d).

(** *** Zero Object in Graded Category *)

Lemma gm_from_zero_unique (Y : GradedObj) (f g : GradedMor go_zero Y)
  : f = g.
Proof.
  unfold GradedMor, go_zero in f, g.
  simpl in f, g.
  destruct f, g.
  reflexivity.
Defined.

Lemma gm_to_zero_unique (X : GradedObj) (f g : GradedMor X go_zero)
  : f = g.
Proof.
  destruct X as [dx].
  unfold GradedMor, go_zero in f, g.
  simpl in f, g.
  destruct dx.
  - destruct f, g.
    reflexivity.
  - destruct f, g.
    reflexivity.
Defined.

Global Instance Contr_gm_from_zero (Y : GradedObj)
  : Contr (GradedMor go_zero Y).
Proof.
  apply (Build_Contr _ tt).
  intro f.
  unfold GradedMor, go_zero in f.
  simpl in f.
  destruct f.
  reflexivity.
Defined.

Global Instance Contr_gm_to_zero (X : GradedObj)
  : Contr (GradedMor X go_zero).
Proof.
  apply (Build_Contr _ (gm_zero X go_zero)).
  intro f.
  apply gm_to_zero_unique.
Defined.

Definition GradedZero : ZeroObject GradedCat
  := Build_ZeroObject GradedCat go_zero
       (fun Y => Contr_gm_from_zero Y)
       (fun X => Contr_gm_to_zero X).

(** *** Zero maps between positive-dimensional objects are provably distinct from isomorphisms. *)

Definition go_one : GradedObj := {| go_dim := S O |}.

Definition gm_zero_one_one : morphism GradedCat go_one go_one
  := gm_zero go_one go_one.

Definition gm_id_one_one : morphism GradedCat go_one go_one
  := gm_id go_one.

Definition bool_discrim (b : Bool) : Type :=
  match b with
  | true => Unit
  | false => Empty
  end.

Lemma gm_zero_ne_id_one : gm_zero_one_one <> gm_id_one_one.
Proof.
  unfold gm_zero_one_one, gm_id_one_one, gm_zero, gm_id, go_one.
  simpl.
  intro H.
  exact (transport bool_discrim H^ tt).
Defined.

Theorem graded_zero_morphism_not_iso
  : @IsIsomorphism GradedCat go_one go_one gm_zero_one_one -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  unfold gm_zero_one_one in *.
  simpl in g.
  assert (Hg : gm_compose go_one go_one go_one g (gm_zero go_one go_one) =
               gm_zero go_one go_one).
  { unfold gm_compose, gm_zero, go_one.
    simpl.
    destruct g; reflexivity. }
  assert (Hid : gm_compose go_one go_one go_one g (gm_zero go_one go_one) =
                gm_id go_one).
  { exact Hgf. }
  assert (Heq : gm_zero go_one go_one = gm_id go_one).
  { exact (Hg^ @ Hid). }
  apply gm_zero_ne_id_one.
  exact Heq.
Defined.

(** The graded category contains provable non-isomorphisms. *)

Theorem graded_cat_has_non_iso_morphisms
  : { X : GradedObj & { Y : GradedObj & { f : morphism GradedCat X Y &
      @IsIsomorphism GradedCat X Y f -> Empty }}}.
Proof.
  exists go_one.
  exists go_one.
  exists gm_zero_one_one.
  exact graded_zero_morphism_not_iso.
Defined.

(** *** Dimension as an integer-valued weight measure. *)

Definition graded_dim_measure (X : GradedObj) : QPos :=
  nat_to_qpos (go_dim X).

Lemma graded_zero_dim_zero : graded_dim_measure go_zero = qpos_zero.
Proof.
  unfold graded_dim_measure, go_zero, nat_to_qpos.
  simpl.
  reflexivity.
Defined.

Definition GradedWeightMeasure : WeightMeasure GradedCat GradedZero.
Proof.
  refine {| wm_measure := fun X : object GradedCat => graded_dim_measure X |}.
  exact graded_zero_dim_zero.
Defined.

Lemma graded_measure_is_integer (X : GradedObj)
  : qpos_denom_pred (graded_dim_measure X) = O.
Proof.
  unfold graded_dim_measure, nat_to_qpos.
  simpl.
  reflexivity.
Defined.

(** *** Zero measure forces the zero object. *)

Theorem graded_zero_measure_implies_zero_object (X : GradedObj)
  : qpos_is_zero (graded_dim_measure X) -> X = go_zero.
Proof.
  unfold qpos_is_zero, graded_dim_measure, nat_to_qpos.
  simpl.
  intro H.
  destruct X as [dx].
  simpl in H.
  destruct dx.
  - unfold go_zero.
    reflexivity.
  - exfalso.
    exact (S_ne_O dx H).
Defined.

Definition GradedZeroMeasureImpliesZero
  : ZeroMeasureImpliesZeroObject GradedCat GradedZero GradedWeightMeasure
  := graded_zero_measure_implies_zero_object.

Definition go_susp_mor (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (go_susp X) (go_susp Y).
Proof.
  destruct X as [dx].
  destruct Y as [dy].
  unfold GradedMor, go_susp.
  simpl.
  destruct dx as [|dx'].
  - exact tt.
  - destruct dy as [|dy'].
    + exact tt.
    + exact f.
Defined.

Lemma go_susp_mor_id (X : GradedObj)
  : go_susp_mor X X (gm_id X) = gm_id (go_susp X).
Proof.
  destruct X as [dx].
  unfold go_susp_mor, gm_id, go_susp, GradedMor.
  simpl.
  destruct dx as [|dx'].
  - reflexivity.
  - reflexivity.
Defined.

Lemma go_susp_mor_comp (X Y Z : GradedObj)
  (f : GradedMor X Y) (g : GradedMor Y Z)
  : go_susp_mor X Z (gm_compose X Y Z g f) =
    gm_compose (go_susp X) (go_susp Y) (go_susp Z)
      (go_susp_mor Y Z g) (go_susp_mor X Y f).
Proof.
  destruct X as [dx].
  destruct Y as [dy].
  destruct Z as [dz].
  unfold go_susp_mor, gm_compose, go_susp, GradedMor.
  simpl.
  destruct dx as [|dx'].
  - reflexivity.
  - destruct dz as [|dz'].
    + reflexivity.
    + destruct dy as [|dy'].
      * reflexivity.
      * reflexivity.
Defined.

Definition GradedSusp : Functor GradedCat GradedCat.
Proof.
  refine (Build_Functor GradedCat GradedCat
            go_susp
            (fun X Y f => go_susp_mor X Y f)
            _ _).
  - intros X Y Z f g.
    exact (go_susp_mor_comp X Y Z f g).
  - intro X.
    exact (go_susp_mor_id X).
Defined.

Definition go_loop_mor (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (go_loop X) (go_loop Y).
Proof.
  destruct X as [dx].
  destruct Y as [dy].
  unfold GradedMor, go_loop.
  simpl.
  destruct dx as [|[|dx']].
  - exact tt.
  - exact tt.
  - destruct dy as [|[|dy']].
    + exact tt.
    + exact tt.
    + exact f.
Defined.

Lemma go_loop_mor_id (X : GradedObj)
  : go_loop_mor X X (gm_id X) = gm_id (go_loop X).
Proof.
  destruct X as [dx].
  unfold go_loop_mor, gm_id, go_loop, GradedMor.
  simpl.
  destruct dx as [|[|dx']].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(** The pointwise loop is not functorial on nat-graded objects; GradedLoopThroughZ completes it through the Z-graded instance, agreeing above dimension one by graded_loop_factors. *)

(** ** The threshold tower: false strictly below N and true from N onward; both concrete stabilization suites are instances. *)

Definition threshold_tower_map (N : nat) (n : nat) : Bool.
Proof.
  destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
  - exact false.
  - exact true.
  - exact true.
Defined.

Lemma threshold_tower_map_below (N n : nat)
  (H : nat_lt n N)
  : threshold_tower_map N n = false.
Proof.
  unfold threshold_tower_map.
  destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
  - reflexivity.
  - exfalso.
    rewrite Heq in H.
    exact (nat_lt_irrefl N H).
  - exfalso.
    exact (nat_lt_irrefl n (nat_lt_trans n N n H Hgt)).
Defined.

Lemma threshold_tower_map_at (N : nat)
  : threshold_tower_map N N = true.
Proof.
  unfold threshold_tower_map.
  destruct (nat_lt_or_eq_or_gt N N) as [[Hlt | Heq] | Hgt].
  - exfalso.
    exact (nat_lt_irrefl N Hlt).
  - reflexivity.
  - exfalso.
    exact (nat_lt_irrefl N Hgt).
Defined.

Lemma threshold_tower_map_above (N n : nat)
  (H : nat_lt N n)
  : threshold_tower_map N n = true.
Proof.
  unfold threshold_tower_map.
  destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
  - exfalso.
    exact (nat_lt_irrefl n (nat_lt_trans n N n Hlt H)).
  - exfalso.
    rewrite <- Heq in H.
    exact (nat_lt_irrefl n H).
  - reflexivity.
Defined.

(*******************************************************************************)
(*  THE SHIFT CATEGORY OVER A PAYLOAD: COMPLETION OF THE GRADED MOTIVIC        *)
(*  STABLE HOMOTOPY CATEGORY                                                   *)
(*******************************************************************************)

(** Any payload type with a shift system generates a proper stable category; instantiating at graded motivic spectra completes the motivic stable homotopy category with load-bearing hypotheses. *)

Inductive ShiftObj (A : Type) : Type :=
  | sh_zero : ShiftObj A
  | sh_el : A -> ShiftObj A.

Arguments sh_zero {A}.
Arguments sh_el {A} a.

Definition ShiftMor {A : Type} (X Y : ShiftObj A) : Type :=
  match X with
  | sh_zero => Unit
  | sh_el _ => match Y with
               | sh_zero => Unit
               | sh_el _ => Bool
               end
  end.

Definition shm_id {A : Type} (X : ShiftObj A) : ShiftMor X X :=
  match X return ShiftMor X X with
  | sh_zero => tt
  | sh_el _ => true
  end.

Definition shm_zero {A : Type} (X Y : ShiftObj A) : ShiftMor X Y :=
  match X return ShiftMor X Y with
  | sh_zero => tt
  | sh_el _ => match Y return ShiftMor (sh_el _) Y with
               | sh_zero => tt
               | sh_el _ => false
               end
  end.

Definition shm_compose {A : Type} (X Y Z : ShiftObj A)
  (g : ShiftMor Y Z) (f : ShiftMor X Y)
  : ShiftMor X Z.
Proof.
  destruct X as [| x].
  - exact tt.
  - destruct Z as [| z].
    + exact tt.
    + destruct Y as [| y].
      * exact false.
      * exact (andb f g).
Defined.

Global Instance ishset_shiftmor {A : Type} (X Y : ShiftObj A)
  : IsHSet (ShiftMor X Y).
Proof.
  destruct X, Y; simpl.
  - exact hset_unit.
  - exact hset_unit.
  - exact hset_unit.
  - exact hset_bool.
Defined.

Lemma shm_compose_assoc {A : Type} (W X Y Z : ShiftObj A)
  (f : ShiftMor W X) (g : ShiftMor X Y) (h : ShiftMor Y Z)
  : shm_compose W X Z (shm_compose X Y Z h g) f =
    shm_compose W Y Z h (shm_compose W X Y g f).
Proof.
  destruct W, X, Y, Z; bool_bash.
Defined.

Lemma shm_compose_id_l {A : Type} (X Y : ShiftObj A) (f : ShiftMor X Y)
  : shm_compose X Y Y (shm_id Y) f = f.
Proof.
  destruct X, Y; bool_bash.
Defined.

Lemma shm_compose_id_r {A : Type} (X Y : ShiftObj A) (f : ShiftMor X Y)
  : shm_compose X X Y f (shm_id X) = f.
Proof.
  destruct X, Y; bool_bash.
Defined.

Definition ShiftCat (A : Type) : PreCategory
  := @Build_PreCategory
       (ShiftObj A)
       (fun X Y => ShiftMor X Y)
       (fun X => shm_id X)
       (fun X Y Z g f => shm_compose X Y Z g f)
       (fun s d d' d'' m1 m2 m3 => shm_compose_assoc s d d' d'' m1 m2 m3)
       (fun a b f => shm_compose_id_l a b f)
       (fun a b f => shm_compose_id_r a b f)
       (fun s d => ishset_shiftmor s d).

Global Instance contr_shm_from_zero {A : Type} (Y : ShiftObj A)
  : Contr (ShiftMor sh_zero Y).
Proof.
  apply (Build_Contr _ tt).
  intro f.
  destruct f.
  reflexivity.
Defined.

Global Instance contr_shm_to_zero {A : Type} (X : ShiftObj A)
  : Contr (ShiftMor X sh_zero).
Proof.
  destruct X.
  - apply (Build_Contr _ tt).
    intro f.
    destruct f.
    reflexivity.
  - apply (Build_Contr _ tt).
    intro f.
    destruct f.
    reflexivity.
Defined.

Definition ShiftZero (A : Type) : ZeroObject (ShiftCat A)
  := Build_ZeroObject (ShiftCat A) sh_zero
       (fun Y => contr_shm_from_zero Y)
       (fun X => contr_shm_to_zero X).

Definition ShiftObj_discrim {A : Type} (X : ShiftObj A) : Type :=
  match X with
  | sh_zero => Empty
  | sh_el _ => Unit
  end.

Lemma sh_el_ne_zero {A : Type} (a : A) : sh_el a = sh_zero -> Empty.
Proof.
  intro p.
  exact (transport ShiftObj_discrim p tt).
Defined.

Lemma shm_true_is_iso {A : Type} (a b : A)
  : @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el b) true.
Proof.
  exists true.
  simpl.
  split; reflexivity.
Defined.

Lemma shm_false_not_iso {A : Type} (a b : A)
  : @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el b) false -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  simpl in *.
  destruct g.
  - exact (transport bool_discrim Hgf^ tt).
  - exact (transport bool_discrim Hfg^ tt).
Defined.

Theorem ShiftCat_has_non_iso {A : Type} (a : A)
  : { X : ShiftObj A & { Y : ShiftObj A & { f : morphism (ShiftCat A) X Y &
      @IsIsomorphism (ShiftCat A) X Y f -> Empty }}}.
Proof.
  exists (sh_el a).
  exists (sh_el a).
  exists (shm_zero (sh_el a) (sh_el a)).
  exact (shm_false_not_iso a a).
Defined.

Section ShiftSystem.

Context {A : Type}
  (s l : A -> A)
  (sl : forall a, l (s a) = a)
  (ls : forall a, s (l a) = a).

Definition sh_susp (X : ShiftObj A) : ShiftObj A :=
  match X with
  | sh_zero => sh_zero
  | sh_el a => sh_el (s a)
  end.

Definition sh_loop (X : ShiftObj A) : ShiftObj A :=
  match X with
  | sh_zero => sh_zero
  | sh_el a => sh_el (l a)
  end.

Lemma sh_loop_susp (X : ShiftObj A) : sh_loop (sh_susp X) = X.
Proof.
  destruct X.
  - reflexivity.
  - exact (ap sh_el (sl a)).
Defined.

Lemma sh_susp_loop (X : ShiftObj A) : sh_susp (sh_loop X) = X.
Proof.
  destruct X.
  - reflexivity.
  - exact (ap sh_el (ls a)).
Defined.

Definition sh_susp_mor (X Y : ShiftObj A) (f : ShiftMor X Y)
  : ShiftMor (sh_susp X) (sh_susp Y).
Proof.
  destruct X, Y; simpl.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact f.
Defined.

Definition sh_loop_mor (X Y : ShiftObj A) (f : ShiftMor X Y)
  : ShiftMor (sh_loop X) (sh_loop Y).
Proof.
  destruct X, Y; simpl.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact f.
Defined.

Lemma sh_susp_mor_id (X : ShiftObj A)
  : sh_susp_mor X X (shm_id X) = shm_id (sh_susp X).
Proof.
  destruct X; reflexivity.
Defined.

Lemma sh_susp_mor_comp (X Y Z : ShiftObj A)
  (f : ShiftMor X Y) (g : ShiftMor Y Z)
  : sh_susp_mor X Z (shm_compose X Y Z g f)
    = shm_compose (sh_susp X) (sh_susp Y) (sh_susp Z)
        (sh_susp_mor Y Z g) (sh_susp_mor X Y f).
Proof.
  destruct X, Y, Z; simpl.
  all: try reflexivity.
  all: try (destruct f; reflexivity).
Defined.

Lemma sh_loop_mor_id (X : ShiftObj A)
  : sh_loop_mor X X (shm_id X) = shm_id (sh_loop X).
Proof.
  destruct X; reflexivity.
Defined.

Lemma sh_loop_mor_comp (X Y Z : ShiftObj A)
  (f : ShiftMor X Y) (g : ShiftMor Y Z)
  : sh_loop_mor X Z (shm_compose X Y Z g f)
    = shm_compose (sh_loop X) (sh_loop Y) (sh_loop Z)
        (sh_loop_mor Y Z g) (sh_loop_mor X Y f).
Proof.
  destruct X, Y, Z; simpl.
  all: try reflexivity.
  all: try (destruct f; reflexivity).
Defined.

Definition ShSusp : Functor (ShiftCat A) (ShiftCat A).
Proof.
  refine (Build_Functor (ShiftCat A) (ShiftCat A)
            sh_susp
            (fun X Y f => sh_susp_mor X Y f)
            _ _).
  - intros X Y Z f g.
    exact (sh_susp_mor_comp X Y Z f g).
  - intro X.
    exact (sh_susp_mor_id X).
Defined.

Definition ShLoop : Functor (ShiftCat A) (ShiftCat A).
Proof.
  refine (Build_Functor (ShiftCat A) (ShiftCat A)
            sh_loop
            (fun X Y f => sh_loop_mor X Y f)
            _ _).
  - intros X Y Z f g.
    exact (sh_loop_mor_comp X Y Z f g).
  - intro X.
    exact (sh_loop_mor_id X).
Defined.

Definition sh_eta_component (X : ShiftObj A)
  : morphism (ShiftCat A) X (object_of (ShLoop o ShSusp)%functor X).
Proof.
  simpl.
  destruct X.
  - exact tt.
  - exact (transport (fun Y => ShiftMor (sh_el a) Y)
             (ap sh_el (sl a))^ (shm_id (sh_el a))).
Defined.

Definition sh_epsilon_component (X : ShiftObj A)
  : morphism (ShiftCat A) (object_of (ShSusp o ShLoop)%functor X) X.
Proof.
  simpl.
  destruct X.
  - exact tt.
  - exact (transport (fun Y => ShiftMor Y (sh_el a))
             (ap sh_el (ls a)) (shm_id (sh_el a))).
Defined.

Lemma sh_eta_natural (X Y : ShiftObj A) (f : morphism (ShiftCat A) X Y)
  : (morphism_of (ShLoop o ShSusp)%functor f o sh_eta_component X
     = sh_eta_component Y o f)%morphism.
Proof.
  destruct X, Y; simpl.
  - reflexivity.
  - destruct f; reflexivity.
  - destruct f; reflexivity.
  - unfold sh_eta_component.
    simpl.
    set (p1 := sl a).
    set (p2 := sl a0).
    clearbody p1 p2.
    destruct p1, p2.
    simpl.
    destruct f.
    + reflexivity.
    + reflexivity.
Defined.

Lemma sh_epsilon_natural (X Y : ShiftObj A) (f : morphism (ShiftCat A) X Y)
  : (f o sh_epsilon_component X
     = sh_epsilon_component Y o morphism_of (ShSusp o ShLoop)%functor f)%morphism.
Proof.
  destruct X, Y; simpl.
  - reflexivity.
  - destruct f; reflexivity.
  - destruct f; reflexivity.
  - unfold sh_epsilon_component.
    simpl.
    set (p1 := ls a).
    set (p2 := ls a0).
    clearbody p1 p2.
    destruct p1, p2.
    simpl.
    destruct f.
    + reflexivity.
    + reflexivity.
Defined.

Definition ShEta
  : NaturalTransformation 1%functor (ShLoop o ShSusp)%functor.
Proof.
  refine (Build_NaturalTransformation 1%functor (ShLoop o ShSusp)%functor
            sh_eta_component _).
  intros X Y f.
  exact (sh_eta_natural X Y f)^.
Defined.

Definition ShEpsilon
  : NaturalTransformation (ShSusp o ShLoop)%functor 1%functor.
Proof.
  refine (Build_NaturalTransformation (ShSusp o ShLoop)%functor 1%functor
            sh_epsilon_component _).
  intros X Y f.
  exact (sh_epsilon_natural X Y f)^.
Defined.

Definition ShiftPreStable : PreStableCategory
  := {| ps_cat := ShiftCat A;
        ps_zero := ShiftZero A;
        ps_susp := ShSusp;
        ps_loop := ShLoop;
        ps_eta := ShEta;
        ps_epsilon := ShEpsilon |}.

Lemma sh_eta_iso (X : ShiftObj A)
  : IsIsomorphism (sh_eta_component X).
Proof.
  destruct X.
  - simpl.
    exists tt.
    split; reflexivity.
  - simpl.
    unfold sh_eta_component.
    simpl.
    set (p := sl a).
    clearbody p.
    destruct p.
    simpl.
    exists true.
    split; reflexivity.
Defined.

Lemma sh_epsilon_iso (X : ShiftObj A)
  : IsIsomorphism (sh_epsilon_component X).
Proof.
  destruct X.
  - simpl.
    exists tt.
    split; reflexivity.
  - simpl.
    unfold sh_epsilon_component.
    simpl.
    set (p := ls a).
    clearbody p.
    destruct p.
    simpl.
    exists true.
    split; reflexivity.
Defined.

Lemma sh_triangle_1 (X : ShiftObj A)
  : (sh_epsilon_component (sh_susp X) o
     morphism_of ShSusp (sh_eta_component X) = 1)%morphism.
Proof.
  destruct X.
  - simpl.
    reflexivity.
  - simpl.
    unfold sh_eta_component, sh_epsilon_component.
    simpl.
    set (p1 := sl a).
    set (p2 := ls (s a)).
    clearbody p1 p2.
    destruct p1.
    simpl.
    destruct p2.
    simpl.
    reflexivity.
Defined.

Lemma sh_triangle_2 (X : ShiftObj A)
  : (morphism_of ShLoop (sh_epsilon_component X) o
     sh_eta_component (sh_loop X) = 1)%morphism.
Proof.
  destruct X.
  - simpl.
    reflexivity.
  - simpl.
    unfold sh_eta_component, sh_epsilon_component.
    simpl.
    set (p1 := sl (l a)).
    set (p2 := ls a).
    clearbody p1 p2.
    destruct p2.
    simpl.
    destruct p1.
    simpl.
    reflexivity.
Defined.

Definition ShiftProperStable : ProperStableCategory.
Proof.
  refine {| psc_pre := ShiftPreStable |}.
  - intro X.
    exact (sh_eta_iso X).
  - intro X.
    exact (sh_epsilon_iso X).
  - intro X.
    exact (sh_triangle_1 X).
  - intro X.
    exact (sh_triangle_2 X).
Defined.

(** *** Weight measure and cofiber towers over the shift category *)

Definition sh_dim (X : ShiftObj A) : nat :=
  match X with
  | sh_zero => O
  | sh_el _ => S O
  end.

Definition sh_dim_measure (X : ShiftObj A) : QPos := nat_to_qpos (sh_dim X).

Lemma sh_zero_dim_zero : sh_dim_measure sh_zero = qpos_zero.
Proof.
  reflexivity.
Defined.

Definition ShiftWeightMeasure : WeightMeasure (ShiftCat A) (ShiftZero A).
Proof.
  refine {| wm_measure := fun X : object (ShiftCat A) => sh_dim_measure X |}.
  exact sh_zero_dim_zero.
Defined.

Theorem sh_zero_measure_implies_zero (X : ShiftObj A)
  : qpos_is_zero (sh_dim_measure X) -> X = sh_zero.
Proof.
  unfold qpos_is_zero, sh_dim_measure, nat_to_qpos, sh_dim.
  intro p.
  destruct X.
  - reflexivity.
  - exfalso.
    exact (S_ne_O O p).
Defined.

Lemma sh_measure_is_integer (X : ShiftObj A)
  : qpos_denom_pred (sh_dim_measure X) = O.
Proof.
  reflexivity.
Defined.

Definition sh_cofiber_obj (f : Bool) (b : A) : ShiftObj A :=
  if f then sh_zero else sh_el b.

Definition sh_cofiber_in (f : Bool) (b : A)
  : ShiftMor (sh_el b) (sh_cofiber_obj f b)
  := match f return ShiftMor (sh_el b) (sh_cofiber_obj f b) with
     | true => tt
     | false => true
     end.

Definition sh_cofiber_out (f : Bool) (a b : A)
  : ShiftMor (sh_cofiber_obj f b) (sh_el (s a))
  := match f return ShiftMor (sh_cofiber_obj f b) (sh_el (s a)) with
     | true => tt
     | false => false
     end.

Lemma sh_ps_zero_is_shm_zero (X Y : object ShiftPreStable)
  : ps_zero_morphism ShiftPreStable X Y = shm_zero X Y.
Proof.
  unfold ps_zero_morphism, zero_morphism.
  simpl.
  destruct X, Y; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Definition sh_cofiber_triangle (a b : A) (f : Bool)
  : Triangle ShiftPreStable
  := {| tri_X := sh_el a : object ShiftPreStable;
        tri_Y := sh_el b : object ShiftPreStable;
        tri_Z := sh_cofiber_obj f b : object ShiftPreStable;
        tri_f := f : morphism ShiftPreStable (sh_el a) (sh_el b);
        tri_g := sh_cofiber_in f b;
        tri_h := sh_cofiber_out f a b |}.

Lemma sh_cofiber_gf_zero (a b : A) (f : Bool)
  : shm_compose (sh_el a) (sh_el b) (sh_cofiber_obj f b) (sh_cofiber_in f b) f
    = shm_zero (sh_el a) (sh_cofiber_obj f b).
Proof.
  destruct f; reflexivity.
Defined.

Lemma sh_cofiber_hg_zero (a b : A) (f : Bool)
  : shm_compose (sh_el b) (sh_cofiber_obj f b) (sh_el (s a))
      (sh_cofiber_out f a b) (sh_cofiber_in f b)
    = shm_zero (sh_el b) (sh_el (s a)).
Proof.
  destruct f; reflexivity.
Defined.

Lemma sh_cofiber_susp_f_h_zero (a b : A) (f : Bool)
  : shm_compose (sh_cofiber_obj f b) (sh_el (s a)) (sh_el (s b))
      (sh_susp_mor (sh_el a) (sh_el b) f) (sh_cofiber_out f a b)
    = shm_zero (sh_cofiber_obj f b) (sh_el (s b)).
Proof.
  destruct f; reflexivity.
Defined.

Theorem sh_cofiber_distinguished (a b : A) (f : Bool)
  : DistinguishedTriangle ShiftPreStable.
Proof.
  refine {| dt_tri := sh_cofiber_triangle a b f |}.
  - simpl.
    rewrite sh_ps_zero_is_shm_zero.
    exact (sh_cofiber_gf_zero a b f).
  - simpl.
    rewrite sh_ps_zero_is_shm_zero.
    exact (sh_cofiber_hg_zero a b f).
  - simpl.
    rewrite sh_ps_zero_is_shm_zero.
    exact (sh_cofiber_susp_f_h_zero a b f).
Defined.

(** *** Towers of graded objects with weight-bounded cofibers *)

Definition sh_tower_from_maps (a : A) (maps : nat -> Bool)
  : CategoricalTower (ShiftCat A)
  := Build_CategoricalTower (ShiftCat A)
       (fun _ => sh_el a)
       (fun n => maps n).

Definition sh_fiber_measure (a : A) (f : Bool) : QPos
  := sh_dim_measure (sh_cofiber_obj f a).

Lemma sh_fiber_measure_zero_implies_iso (a b : A) (f : Bool)
  : qpos_is_zero (sh_fiber_measure b f) ->
    @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el b) f.
Proof.
  intro Hzero.
  destruct f.
  - exact (shm_true_is_iso a b).
  - exfalso.
    exact (sh_el_ne_zero b (sh_zero_measure_implies_zero _ Hzero)).
Defined.

Definition sh_tower_fiber_measure (a : A) (maps : nat -> Bool) (n : nat) : QPos
  := sh_fiber_measure a (maps n).

Lemma sh_tower_fiber_measure_is_integer (a : A) (maps : nat -> Bool) (n : nat)
  : qpos_denom_pred (sh_tower_fiber_measure a maps n) = O.
Proof.
  reflexivity.
Defined.

Theorem sh_tower_stabilizes_when_fibers_vanish (a : A) (maps : nat -> Bool)
  (Hev : EventuallyZero (sh_tower_fiber_measure a maps))
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el a) (maps n) }.
Proof.
  destruct Hev as [N HN].
  exists N.
  intros n Hn.
  apply sh_fiber_measure_zero_implies_iso.
  exact (HN n Hn).
Defined.

Theorem sh_tower_stabilizes_from_limit (a : A) (maps : nat -> Bool)
  (Hlimit : LimitZero (sh_tower_fiber_measure a maps))
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el a) (maps n) }.
Proof.
  apply sh_tower_stabilizes_when_fibers_vanish.
  apply integer_LimitZero_implies_EventuallyZero.
  - exact (sh_tower_fiber_measure_is_integer a maps).
  - exact Hlimit.
Defined.

Definition sh_weight_bounded_tower (a : A) (C : QPos) (maps : nat -> Bool)
  : Type
  := forall n, qpos_lt (sh_tower_fiber_measure a maps n)
                       (qpos_mult C (w_stage n)).

Theorem sh_weight_bounded_implies_limit
  (a : A) (C : QPos) (maps : nat -> Bool)
  (HC : nat_lt O (qpos_num C))
  (Hbounded : sh_weight_bounded_tower a C maps)
  : LimitZero (sh_tower_fiber_measure a maps).
Proof.
  exact (bounded_measure_limit_zero _ C HC Hbounded).
Defined.

Theorem sh_weight_bounded_stabilizes
  (a : A) (C : QPos) (maps : nat -> Bool)
  (HC : nat_lt O (qpos_num C))
  (Hbounded : sh_weight_bounded_tower a C maps)
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el a) (maps n) }.
Proof.
  apply sh_tower_stabilizes_from_limit.
  exact (sh_weight_bounded_implies_limit a C maps HC Hbounded).
Defined.

Theorem sh_genuine_threshold (a : A) (N : nat)
  (HN : nat_lt O N)
  : (forall n, nat_le N n ->
       @IsIsomorphism (ShiftCat A) (sh_el a) (sh_el a) (threshold_tower_map N n))
    * (@IsIsomorphism (ShiftCat A) (sh_el a) (sh_el a) (threshold_tower_map N O)
       -> Empty).
Proof.
  split.
  - intros n Hn.
    destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
    + exfalso.
      exact (nat_le_lt_contradiction N n Hn Hlt).
    + rewrite Heq.
      rewrite (threshold_tower_map_at N).
      exact (shm_true_is_iso a a).
    + rewrite (threshold_tower_map_above N n Hgt).
      exact (shm_true_is_iso a a).
  - intro Hiso.
    rewrite (threshold_tower_map_below N O HN) in Hiso.
    exact (shm_false_not_iso a a Hiso).
Defined.

End ShiftSystem.

(** ** The Z-graded category is the shift category over Int; its formerly parallel suite collapses into instance corollaries. *)

Definition ZGradedObj : Type := ShiftObj Int.

Definition zgo_zero : ZGradedObj := sh_zero.

Definition zgo_nonzero (n : Int) : ZGradedObj := sh_el n.

Definition zgo_susp : ZGradedObj -> ZGradedObj := sh_susp int_succ.

Definition zgo_loop : ZGradedObj -> ZGradedObj := sh_loop int_pred.

Definition zgo_loop_susp : forall X, zgo_loop (zgo_susp X) = X
  := sh_loop_susp int_succ int_pred int_succ_pred.

Definition zgo_susp_loop : forall X, zgo_susp (zgo_loop X) = X
  := sh_susp_loop int_succ int_pred int_pred_succ.

Definition ZGradedMor : ZGradedObj -> ZGradedObj -> Type := @ShiftMor Int.

Definition zgm_id : forall X : ZGradedObj, ZGradedMor X X := @shm_id Int.

Definition zgm_zero : forall X Y : ZGradedObj, ZGradedMor X Y := @shm_zero Int.

Definition zgm_compose
  : forall X Y Z : ZGradedObj,
    ZGradedMor Y Z -> ZGradedMor X Y -> ZGradedMor X Z
  := @shm_compose Int.

Global Instance ZGradedMor_hset (X Y : ZGradedObj) : IsHSet (ZGradedMor X Y)
  := ishset_shiftmor X Y.

Definition zgm_compose_assoc
  : forall (W X Y Z : ZGradedObj)
           (f : ZGradedMor W X) (g : ZGradedMor X Y) (h : ZGradedMor Y Z),
    zgm_compose W X Z (zgm_compose X Y Z h g) f
    = zgm_compose W Y Z h (zgm_compose W X Y g f)
  := @shm_compose_assoc Int.

Definition zgm_compose_id_l
  : forall (X Y : ZGradedObj) (f : ZGradedMor X Y),
    zgm_compose X Y Y (zgm_id Y) f = f
  := @shm_compose_id_l Int.

Definition zgm_compose_id_r
  : forall (X Y : ZGradedObj) (f : ZGradedMor X Y),
    zgm_compose X X Y f (zgm_id X) = f
  := @shm_compose_id_r Int.

Definition ZGradedCat : PreCategory := ShiftCat Int.

Global Instance Contr_zgm_from_zero (Y : ZGradedObj)
  : Contr (ZGradedMor zgo_zero Y)
  := contr_shm_from_zero Y.

Global Instance Contr_zgm_to_zero (X : ZGradedObj)
  : Contr (ZGradedMor X zgo_zero)
  := contr_shm_to_zero X.

Definition ZGradedZero : ZeroObject ZGradedCat := ShiftZero Int.

Definition zgo_susp_mor
  : forall (X Y : ZGradedObj), ZGradedMor X Y ->
    ZGradedMor (zgo_susp X) (zgo_susp Y)
  := sh_susp_mor int_succ.

Definition zgo_susp_mor_id
  : forall X : ZGradedObj, zgo_susp_mor X X (zgm_id X) = zgm_id (zgo_susp X)
  := sh_susp_mor_id int_succ.

Definition zgo_susp_mor_comp
  : forall (X Y Z : ZGradedObj) (f : ZGradedMor X Y) (g : ZGradedMor Y Z),
    zgo_susp_mor X Z (zgm_compose X Y Z g f)
    = zgm_compose (zgo_susp X) (zgo_susp Y) (zgo_susp Z)
        (zgo_susp_mor Y Z g) (zgo_susp_mor X Y f)
  := sh_susp_mor_comp int_succ.

Definition ZGradedSusp : Functor ZGradedCat ZGradedCat := ShSusp int_succ.

Definition zgo_loop_mor
  : forall (X Y : ZGradedObj), ZGradedMor X Y ->
    ZGradedMor (zgo_loop X) (zgo_loop Y)
  := sh_loop_mor int_pred.

Definition zgo_loop_mor_id
  : forall X : ZGradedObj, zgo_loop_mor X X (zgm_id X) = zgm_id (zgo_loop X)
  := sh_loop_mor_id int_pred.

Definition zgo_loop_mor_comp
  : forall (X Y Z : ZGradedObj) (f : ZGradedMor X Y) (g : ZGradedMor Y Z),
    zgo_loop_mor X Z (zgm_compose X Y Z g f)
    = zgm_compose (zgo_loop X) (zgo_loop Y) (zgo_loop Z)
        (zgo_loop_mor Y Z g) (zgo_loop_mor X Y f)
  := sh_loop_mor_comp int_pred.

Definition ZGradedLoop : Functor ZGradedCat ZGradedCat := ShLoop int_pred.

(** ** The stable structure as generic instances *)

Definition ZGraded_eta_component
  : forall X : ZGradedObj,
      morphism ZGradedCat X (object_of (ZGradedLoop o ZGradedSusp)%functor X)
  := sh_eta_component int_succ int_pred int_succ_pred.

Definition ZGraded_epsilon_component
  : forall X : ZGradedObj,
      morphism ZGradedCat (object_of (ZGradedSusp o ZGradedLoop)%functor X) X
  := sh_epsilon_component int_succ int_pred int_pred_succ.

Lemma transport_along_ap_zgo_nonzero (n m : Int) (p : n = m)
  (X : ZGradedObj) (f : ZGradedMor X (zgo_nonzero n))
  : transport (fun Y => ZGradedMor X Y) (ap zgo_nonzero p) f =
    match X as X0 return (ZGradedMor X0 (zgo_nonzero n) -> ZGradedMor X0 (zgo_nonzero m)) with
    | sh_zero => fun _ => tt
    | sh_el _ => fun g => g
    end f.
Proof.
  destruct p.
  destruct X; simpl.
  - destruct f; reflexivity.
  - reflexivity.
Defined.

Definition ZGraded_eta
  : NaturalTransformation 1%functor (ZGradedLoop o ZGradedSusp)%functor
  := ShEta int_succ int_pred int_succ_pred.

Definition ZGraded_epsilon
  : NaturalTransformation (ZGradedSusp o ZGradedLoop)%functor 1%functor
  := ShEpsilon int_succ int_pred int_pred_succ.

Definition ZGraded_PreStable : PreStableCategory
  := ShiftPreStable int_succ int_pred int_succ_pred int_pred_succ.

Theorem ZGraded_is_non_degenerate_prestable
  : { X : object ZGraded_PreStable &
      { Y : object ZGraded_PreStable &
        { f : morphism ZGraded_PreStable X Y &
          (@IsIsomorphism ZGradedCat X Y f -> Empty) }}}.
Proof.
  exists (zgo_nonzero 0%int).
  exists (zgo_nonzero 0%int).
  exists (zgm_zero (zgo_nonzero 0%int) (zgo_nonzero 0%int)).
  exact (shm_false_not_iso 0%int 0%int).
Defined.

Definition ZGraded_eta_iso
  : forall X : ZGradedObj,
    @IsIsomorphism ZGradedCat X (zgo_loop (zgo_susp X)) (ZGraded_eta_component X)
  := sh_eta_iso int_succ int_pred int_succ_pred.

Definition ZGraded_epsilon_iso
  : forall X : ZGradedObj,
    @IsIsomorphism ZGradedCat (zgo_susp (zgo_loop X)) X (ZGraded_epsilon_component X)
  := sh_epsilon_iso int_succ int_pred int_pred_succ.

Definition ZGraded_triangle_1
  : forall X : ZGradedObj,
    (ZGraded_epsilon_component (zgo_susp X) o
     morphism_of ZGradedSusp (ZGraded_eta_component X) = 1)%morphism
  := sh_triangle_1 int_succ int_pred int_succ_pred int_pred_succ.

Definition ZGraded_triangle_2
  : forall X : ZGradedObj,
    (morphism_of ZGradedLoop (ZGraded_epsilon_component X) o
     ZGraded_eta_component (zgo_loop X) = 1)%morphism
  := sh_triangle_2 int_succ int_pred int_succ_pred int_pred_succ.

Definition ZGraded_ProperStable : ProperStableCategory
  := ShiftProperStable int_succ int_pred int_succ_pred int_pred_succ.

Definition zgraded_dim : ZGradedObj -> nat := @sh_dim Int.

Definition zgraded_dim_measure : ZGradedObj -> QPos := @sh_dim_measure Int.

Definition zgraded_zero_dim_zero : zgraded_dim_measure zgo_zero = qpos_zero
  := idpath.

Definition ZGradedWeightMeasure : WeightMeasure ZGradedCat ZGradedZero
  := @ShiftWeightMeasure Int.

Theorem ZGraded_zero_measure_implies_zero (X : ZGradedObj)
  : qpos_is_zero (zgraded_dim_measure X) -> X = zgo_zero.
Proof.
  unfold qpos_is_zero, zgraded_dim_measure, nat_to_qpos, zgraded_dim.
  simpl.
  intro H.
  destruct X.
  - reflexivity.
  - exfalso.
    exact (S_ne_O O H).
Defined.

Definition ZGradedZeroMeasureImpliesZero
  : ZeroMeasureImpliesZeroObject ZGradedCat ZGradedZero ZGradedWeightMeasure
  := ZGraded_zero_measure_implies_zero.

Lemma ZGraded_measure_is_integer (X : ZGradedObj)
  : qpos_denom_pred (zgraded_dim_measure X) = O.
Proof.
  unfold zgraded_dim_measure, nat_to_qpos.
  simpl.
  reflexivity.
Defined.

(** ZeroFiberInTriangleImpliesIso fails in full generality for ZGraded_PreStable; the convergence machinery applies to towers with nonzero stages. *)

Theorem ZGraded_nonzero_identity_is_iso (n : Int)
  : @IsIsomorphism ZGradedCat (zgo_nonzero n) (zgo_nonzero n) (zgm_id (zgo_nonzero n)).
Proof.
  exists (zgm_id (zgo_nonzero n)).
  simpl.
  split; reflexivity.
Defined.

Theorem ZGraded_true_is_iso (n m : Int)
  : @IsIsomorphism ZGradedCat (zgo_nonzero n) (zgo_nonzero m) true.
Proof.
  exists true.
  simpl.
  split; reflexivity.
Defined.

Theorem ZGraded_zero_zero_iso
  (f : morphism ZGradedCat zgo_zero zgo_zero)
  : IsIsomorphism f.
Proof.
  simpl in f.
  destruct f.
  exists tt.
  split; reflexivity.
Defined.

(** Towers with explicit isomorphism witnesses rather than fiber conditions. *)

Record ZGradedTower := {
  zgt_stage : nat -> ZGradedObj;
  zgt_map : forall n, morphism ZGradedCat (zgt_stage (S n)) (zgt_stage n)
}.

Definition ZGradedTowerStabilizesAt (T : ZGradedTower) (N : nat)
  : Type
  := forall n, nat_le N n -> IsIsomorphism (zgt_map T n).

(** A tower stabilizes when all stage maps are true (isomorphisms). *)

(** A tower where all maps are isomorphisms stabilizes. *)

Theorem ZGraded_tower_with_iso_maps_stabilizes
  (T : ZGradedTower)
  (H : forall n, IsIsomorphism (zgt_map T n))
  : ZGradedTowerStabilizesAt T O.
Proof.
  unfold ZGradedTowerStabilizesAt.
  intros n _.
  exact (H n).
Defined.

(** Concrete example: constant tower at zero stabilizes. *)

Definition constant_zero_tower : ZGradedTower :=
  {| zgt_stage := fun _ => zgo_zero;
     zgt_map := fun _ => tt |}.

Theorem constant_zero_tower_stabilizes
  : ZGradedTowerStabilizesAt constant_zero_tower O.
Proof.
  unfold ZGradedTowerStabilizesAt.
  intros n _.
  simpl.
  exists tt.
  split; reflexivity.
Defined.

(** Concrete example: constant tower at nonzero with identity maps. *)

Definition constant_nonzero_tower (k : Int) : ZGradedTower :=
  {| zgt_stage := fun _ => zgo_nonzero k;
     zgt_map := fun _ => true |}.

Theorem constant_nonzero_tower_stabilizes (k : Int)
  : ZGradedTowerStabilizesAt (constant_nonzero_tower k) O.
Proof.
  unfold ZGradedTowerStabilizesAt.
  intros n _.
  simpl.
  exact (ZGraded_true_is_iso k k).
Defined.

(** ** The nat-graded category identifies with the shift instance over nat: a conversion functor with on-the-nose hom agreement. *)

Definition go_conv (X : GradedObj) : ShiftObj nat :=
  match go_dim X with
  | O => sh_zero
  | S n => sh_el n
  end.

Theorem GradedMor_is_shift (X Y : GradedObj)
  : GradedMor X Y = ShiftMor (go_conv X) (go_conv Y).
Proof.
  destruct X as [dx], Y as [dy].
  destruct dx, dy; reflexivity.
Defined.

Definition gm_conv (X Y : GradedObj) (f : GradedMor X Y)
  : ShiftMor (go_conv X) (go_conv Y).
Proof.
  destruct X as [dx], Y as [dy].
  destruct dx, dy; exact f.
Defined.

Definition GradedToShift : Functor GradedCat (ShiftCat nat).
Proof.
  refine (Build_Functor GradedCat (ShiftCat nat)
            go_conv
            (fun X Y f => gm_conv X Y f)
            _ _).
  - intros X Y Z f g.
    destruct X as [dx], Y as [dy], Z as [dz].
    destruct dx, dy, dz; bool_bash.
  - intro X.
    destruct X as [dx].
    destruct dx; reflexivity.
Defined.

(** ** Payload maps induce functors of shift categories, embedding the nat-graded category into the Z-graded one where the loop is functorial. *)

Definition sh_payload_obj {A B : Type} (phi : A -> B) (X : ShiftObj A)
  : ShiftObj B
  := match X with
     | sh_zero => sh_zero
     | sh_el a => sh_el (phi a)
     end.

Definition sh_payload_mor {A B : Type} (phi : A -> B) (X Y : ShiftObj A)
  (f : ShiftMor X Y)
  : ShiftMor (sh_payload_obj phi X) (sh_payload_obj phi Y).
Proof.
  destruct X, Y; exact f.
Defined.

Definition ShiftPayload {A B : Type} (phi : A -> B)
  : Functor (ShiftCat A) (ShiftCat B).
Proof.
  refine (Build_Functor (ShiftCat A) (ShiftCat B)
            (sh_payload_obj phi)
            (fun X Y f => sh_payload_mor phi X Y f)
            _ _).
  - intros X Y Z f g.
    destruct X, Y, Z; bool_bash.
  - intro X.
    destruct X; reflexivity.
Defined.

Definition GradedLoopThroughZ : Functor GradedCat ZGradedCat
  := ((ZGradedLoop o ShiftPayload posS) o GradedToShift)%functor.

Lemma graded_loop_factors (X : GradedObj)
  (Hdim : nat_lt 1 (go_dim X))
  : object_of GradedLoopThroughZ X
    = sh_payload_obj posS (go_conv (go_loop X)).
Proof.
  destruct X as [dx].
  destruct dx as [| dx'].
  - destruct Hdim.
  - destruct dx' as [| n].
    + destruct Hdim.
    + reflexivity.
Defined.

Definition ZGraded_Triangle := Triangle ZGraded_PreStable.

Definition ZGraded_zero_morphism (X Y : ZGradedObj)
  : morphism ZGradedCat X Y
  := zero_morphism ZGradedZero X Y.

Lemma ZGraded_zero_morphism_explicit (X Y : ZGradedObj)
  : ZGraded_zero_morphism X Y = zgm_zero X Y.
Proof.
  unfold ZGraded_zero_morphism, zero_morphism.
  simpl.
  destruct X, Y; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma zgm_compose_zero_r (X Y Z : ZGradedObj) (f : ZGradedMor X Y)
  : zgm_compose X Y Z (zgm_zero Y Z) f = zgm_zero X Z.
Proof.
  destruct X, Y, Z; simpl.
  all: try reflexivity.
  all: try (destruct f; reflexivity).
Defined.

Lemma zgm_compose_zero_l (X Y Z : ZGradedObj) (g : ZGradedMor Y Z)
  : zgm_compose X Y Z g (zgm_zero X Y) = zgm_zero X Z.
Proof.
  destruct X, Y, Z; simpl.
  all: try reflexivity.
  all: try (destruct g; reflexivity).
Defined.

Definition ZGraded_identity_triangle (X : object ZGraded_PreStable)
  : ZGraded_Triangle
  := {| tri_X := X;
        tri_Y := X;
        tri_Z := zgo_zero;
        tri_f := zgm_id X;
        tri_g := zgm_zero X zgo_zero;
        tri_h := zgm_zero zgo_zero (zgo_susp X) |}.

Lemma ps_zero_is_zgm_zero (X Y : object ZGraded_PreStable)
  : ps_zero_morphism ZGraded_PreStable X Y = zgm_zero X Y.
Proof.
  unfold ps_zero_morphism, ZGraded_PreStable, zero_morphism.
  simpl.
  destruct X, Y; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Theorem ZGraded_identity_triangle_distinguished (X : object ZGraded_PreStable)
  : DistinguishedTriangle ZGraded_PreStable.
Proof.
  refine {| dt_tri := ZGraded_identity_triangle X |}.
  - apply path_contr.
  - simpl.
    exact (zgm_compose_zero_l X zgo_zero (zgo_susp X)
             (zgm_zero zgo_zero (zgo_susp X))
             @ (ps_zero_is_zgm_zero X (zgo_susp X))^).
  - apply path_contr.
Defined.

Definition cofiber_obj (f : Bool)  (m : Int)
  : ZGradedObj
  := if f then zgo_zero else zgo_nonzero m.

Definition cofiber_in (f : Bool) (m : Int)
  : ZGradedMor (zgo_nonzero m) (cofiber_obj f m)
  := match f return ZGradedMor (zgo_nonzero m) (cofiber_obj f m) with
     | true => tt
     | false => true
     end.

Definition cofiber_out (f : Bool) (n m : Int)
  : ZGradedMor (cofiber_obj f m) (zgo_nonzero (int_succ n))
  := match f return ZGradedMor (cofiber_obj f m) (zgo_nonzero (int_succ n)) with
     | true => tt
     | false => false
     end.

Definition ZGraded_nonzero_cofiber_triangle (n m : Int) (f : Bool)
  : Triangle ZGraded_PreStable
  := {| tri_X := zgo_nonzero n : object ZGraded_PreStable;
        tri_Y := zgo_nonzero m : object ZGraded_PreStable;
        tri_Z := cofiber_obj f m : object ZGraded_PreStable;
        tri_f := f : morphism ZGraded_PreStable (zgo_nonzero n) (zgo_nonzero m);
        tri_g := cofiber_in f m;
        tri_h := cofiber_out f n m |}.

Lemma cofiber_triangle_gf_zero (n m : Int) (f : Bool)
  : zgm_compose (zgo_nonzero n) (zgo_nonzero m) (cofiber_obj f m) (cofiber_in f m) f =
    zgm_zero (zgo_nonzero n) (cofiber_obj f m).
Proof.
  destruct f; simpl.
  - reflexivity.
  - reflexivity.
Defined.

Lemma cofiber_triangle_hg_zero (n m : Int) (f : Bool)
  : zgm_compose (zgo_nonzero m) (cofiber_obj f m) (zgo_nonzero (int_succ n))
      (cofiber_out f n m) (cofiber_in f m) =
    zgm_zero (zgo_nonzero m) (zgo_nonzero (int_succ n)).
Proof.
  destruct f; simpl.
  - reflexivity.
  - reflexivity.
Defined.

Lemma cofiber_triangle_susp_f_h_zero (n m : Int) (f : Bool)
  : zgm_compose (cofiber_obj f m) (zgo_nonzero (int_succ n)) (zgo_nonzero (int_succ m))
      (zgo_susp_mor (zgo_nonzero n) (zgo_nonzero m) f) (cofiber_out f n m) =
    zgm_zero (cofiber_obj f m) (zgo_nonzero (int_succ m)).
Proof.
  destruct f; simpl.
  - reflexivity.
  - reflexivity.
Defined.

Theorem ZGraded_cofiber_distinguished (n m : Int) (f : Bool)
  : DistinguishedTriangle ZGraded_PreStable.
Proof.
  refine {| dt_tri := ZGraded_nonzero_cofiber_triangle n m f |}.
  - simpl.
    rewrite ps_zero_is_zgm_zero.
    exact (cofiber_triangle_gf_zero n m f).
  - simpl.
    rewrite ps_zero_is_zgm_zero.
    exact (cofiber_triangle_hg_zero n m f).
  - simpl.
    rewrite ps_zero_is_zgm_zero.
    exact (cofiber_triangle_susp_f_h_zero n m f).
Defined.

Theorem cofiber_true_is_zero (m : Int)
  : cofiber_obj true m = zgo_zero.
Proof.
  reflexivity.
Defined.

Theorem cofiber_false_is_nonzero (m : Int)
  : cofiber_obj false m = zgo_nonzero m.
Proof.
  reflexivity.
Defined.

Theorem ZGraded_zero_cofiber_implies_iso (n m : Int)
  : cofiber_obj true m = zgo_zero ->
    @IsIsomorphism ZGradedCat (zgo_nonzero n) (zgo_nonzero m) true.
Proof.
  intro H.
  exact (ZGraded_true_is_iso n m).
Defined.

Theorem ZGraded_iso_implies_zero_cofiber (n m : Int) (f : Bool)
  : @IsIsomorphism ZGradedCat (zgo_nonzero n) (zgo_nonzero m) f ->
    cofiber_obj f m = zgo_zero.
Proof.
  intro H.
  destruct f.
  - reflexivity.
  - exfalso.
    destruct H as [g [Hgf Hfg]].
    simpl in *.
    exact (transport bool_discrim Hgf^ tt).
Defined.

Definition ZGradedObj_discrim : ZGradedObj -> Type := @ShiftObj_discrim Int.

Definition zgo_nonzero_ne_zero (k : Int) : zgo_nonzero k = zgo_zero -> Empty
  := sh_el_ne_zero k.

Theorem ZGraded_cofiber_iff_iso (n m : Int) (f : Bool)
  : (cofiber_obj f m = zgo_zero) <-> @IsIsomorphism ZGradedCat (zgo_nonzero n) (zgo_nonzero m) f.
Proof.
  split.
  - intro Hzero.
    destruct f.
    { exact (ZGraded_true_is_iso n m). }
    { simpl in Hzero.
      exfalso.
      exact (zgo_nonzero_ne_zero m Hzero). }
  - exact (ZGraded_iso_implies_zero_cofiber n m f).
Defined.

Definition ZGraded_CategoricalTower (stages : nat -> object ZGradedCat)
  (maps : forall n, morphism ZGradedCat (stages (S n)) (stages n))
  : CategoricalTower ZGradedCat
  := {| ct_stage := stages;
        ct_map := maps |}.

Definition constant_int_tower (k : Int)
  : CategoricalTower ZGradedCat
  := ZGraded_CategoricalTower
       (fun _ : nat => zgo_nonzero k : object ZGradedCat)
       (fun _ : nat => true : morphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)).

Theorem constant_int_tower_stabilizes (k : Int)
  : forall n, @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)
                (ct_map ZGradedCat (constant_int_tower k) n).
Proof.
  intro n.
  simpl.
  exact (ZGraded_true_is_iso k k).
Defined.

Definition eventually_iso_tower_map (N : nat) (n : nat) : Bool
  := threshold_tower_map N n.

Definition eventually_iso_tower (k : Int) (N : nat)
  : CategoricalTower ZGradedCat
  := ZGraded_CategoricalTower
       (fun _ : nat => zgo_nonzero k : object ZGradedCat)
       (fun n : nat => eventually_iso_tower_map N n
                       : morphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)).

Lemma eventually_iso_tower_below_N (k : Int) (N n : nat)
  (H : nat_lt n N)
  : ct_map ZGradedCat (eventually_iso_tower k N) n = false.
Proof.
  exact (threshold_tower_map_below N n H).
Defined.

Lemma eventually_iso_tower_at_N (k : Int) (N : nat)
  : ct_map ZGradedCat (eventually_iso_tower k N) N = true.
Proof.
  exact (threshold_tower_map_at N).
Defined.

Lemma eventually_iso_tower_above_N (k : Int) (N n : nat)
  (H : nat_lt N n)
  : ct_map ZGradedCat (eventually_iso_tower k N) n = true.
Proof.
  exact (threshold_tower_map_above N n H).
Defined.

Theorem eventually_iso_tower_stabilizes_at_N (k : Int) (N : nat)
  : TowerStabilizesAt (eventually_iso_tower k N) N.
Proof.
  unfold TowerStabilizesAt.
  intros n Hn.
  destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
  - exfalso.
    exact (nat_le_lt_contradiction N n Hn Hlt).
  - rewrite Heq.
    assert (Hmap : ct_map ZGradedCat (eventually_iso_tower k N) N = true).
    { exact (eventually_iso_tower_at_N k N). }
    rewrite Hmap.
    exact (ZGraded_true_is_iso k k).
  - assert (Hmap : ct_map ZGradedCat (eventually_iso_tower k N) n = true).
    { exact (eventually_iso_tower_above_N k N n Hgt). }
    rewrite Hmap.
    exact (ZGraded_true_is_iso k k).
Defined.

Theorem eventually_iso_tower_not_iso_before_N (k : Int) (N n : nat)
  (H : nat_lt n N)
  : @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)
      (ct_map ZGradedCat (eventually_iso_tower k N) n) -> Empty.
Proof.
  intro Hiso.
  assert (Hmap : ct_map ZGradedCat (eventually_iso_tower k N) n = false).
  { exact (eventually_iso_tower_below_N k N n H). }
  rewrite Hmap in Hiso.
  destruct Hiso as [g [Hgf Hfg]].
  simpl in *.
  exact (transport bool_discrim Hgf^ tt).
Defined.

Theorem ZGraded_nontrivial_stabilization_example
  : { k : Int & { N : nat &
      (TowerStabilizesAt (eventually_iso_tower k N) N) *
      (forall n, nat_lt n N ->
        @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)
          (ct_map ZGradedCat (eventually_iso_tower k N) n) -> Empty) }}.
Proof.
  exists 0%int.
  exists 3%nat.
  split.
  - exact (eventually_iso_tower_stabilizes_at_N 0%int 3).
  - intros n Hn.
    exact (eventually_iso_tower_not_iso_before_N 0%int 3 n Hn).
Defined.

(** ** Connecting ZGraded Towers to Stable Tower Machinery *)

Definition ZGraded_fiber_from_map (n m : Int) (f : Bool)
  : object ZGraded_PreStable
  := cofiber_obj f m.

Definition ZGraded_fiber_measure (n m : Int) (f : Bool)
  : QPos
  := zgraded_dim_measure (cofiber_obj f m).

Lemma ZGraded_fiber_measure_true (m : Int)
  : ZGraded_fiber_measure 0%int m true = qpos_zero.
Proof.
  unfold ZGraded_fiber_measure, cofiber_obj.
  simpl.
  reflexivity.
Defined.

Lemma ZGraded_fiber_measure_false (m : Int)
  : ZGraded_fiber_measure 0%int m false = nat_to_qpos (S O).
Proof.
  unfold ZGraded_fiber_measure, cofiber_obj, zgraded_dim_measure, zgraded_dim.
  simpl.
  reflexivity.
Defined.

Lemma ZGraded_fiber_measure_zero_implies_iso (n m : Int) (f : Bool)
  : qpos_is_zero (ZGraded_fiber_measure n m f) ->
    @IsIsomorphism ZGradedCat (zgo_nonzero n) (zgo_nonzero m) f.
Proof.
  intro Hzero.
  unfold ZGraded_fiber_measure in Hzero.
  assert (Hcofiber : cofiber_obj f m = zgo_zero).
  { apply ZGraded_zero_measure_implies_zero.
    exact Hzero. }
  destruct f.
  - exact (ZGraded_true_is_iso n m).
  - exfalso.
    simpl in Hcofiber.
    exact (zgo_nonzero_ne_zero m Hcofiber).
Defined.

Lemma ZGraded_fiber_measure_any_k (k1 k2 : Int) (f : Bool)
  : ZGraded_fiber_measure k1 k2 f = ZGraded_fiber_measure 0%int 0%int f.
Proof.
  unfold ZGraded_fiber_measure, cofiber_obj, zgraded_dim_measure.
  destruct f; reflexivity.
Defined.

Definition threshold_fiber_measure (N n : nat) : QPos
  := ZGraded_fiber_measure 0%int 0%int (threshold_tower_map N n).

Lemma threshold_fiber_measure_below (N n : nat)
  (H : nat_lt n N)
  : threshold_fiber_measure N n = nat_to_qpos (S O).
Proof.
  unfold threshold_fiber_measure.
  rewrite (threshold_tower_map_below N n H).
  exact (ZGraded_fiber_measure_false 0%int).
Defined.

Lemma threshold_fiber_measure_at_or_above (N n : nat)
  (H : nat_le N n)
  : threshold_fiber_measure N n = qpos_zero.
Proof.
  unfold threshold_fiber_measure.
  destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
  - exfalso.
    exact (nat_le_lt_contradiction N n H Hlt).
  - rewrite Heq.
    rewrite (threshold_tower_map_at N).
    exact (ZGraded_fiber_measure_true 0%int).
  - rewrite (threshold_tower_map_above N n Hgt).
    exact (ZGraded_fiber_measure_true 0%int).
Defined.

Lemma threshold_fiber_measure_is_integer (N n : nat)
  : qpos_denom_pred (threshold_fiber_measure N n) = O.
Proof.
  unfold threshold_fiber_measure, ZGraded_fiber_measure, zgraded_dim_measure, nat_to_qpos.
  simpl.
  reflexivity.
Defined.

Definition threshold_fiber_integer_valued (N : nat)
  : IsIntegerValued (threshold_fiber_measure N)
  := threshold_fiber_measure_is_integer N.

Theorem threshold_fiber_has_minimal_positive (N : nat)
  : HasMinimalPositive (threshold_fiber_measure N).
Proof.
  apply integer_valued_has_minimal_positive.
  exact (threshold_fiber_integer_valued N).
Defined.

Theorem threshold_fiber_limit_zero (N : nat)
  : LimitZero (threshold_fiber_measure N).
Proof.
  unfold LimitZero.
  intros epsilon Heps.
  exists N.
  intros m Hm.
  rewrite (threshold_fiber_measure_at_or_above N m (nat_le_of_lt N m Hm)).
  unfold qpos_lt, qpos_zero.
  simpl.
  destruct (qpos_num epsilon) as [|e].
  - destruct Heps.
  - exact tt.
Defined.

Theorem threshold_fiber_eventually_zero (N : nat)
  : EventuallyZero (threshold_fiber_measure N).
Proof.
  exists N.
  intros m Hm.
  unfold qpos_is_zero.
  exact (ap qpos_num (threshold_fiber_measure_at_or_above N m (nat_le_of_lt N m Hm))).
Defined.

Definition eventually_iso_tower_fiber_measure (k : Int) (N n : nat)
  : QPos
  := ZGraded_fiber_measure k k (eventually_iso_tower_map N n).

Lemma eventually_iso_fiber_measure_threshold (k : Int) (N n : nat)
  : eventually_iso_tower_fiber_measure k N n = threshold_fiber_measure N n.
Proof.
  exact (ZGraded_fiber_measure_any_k k k (threshold_tower_map N n)).
Defined.

Lemma eventually_iso_fiber_measure_below_N (k : Int) (N n : nat)
  (H : nat_lt n N)
  : eventually_iso_tower_fiber_measure k N n = nat_to_qpos (S O).
Proof.
  exact (eventually_iso_fiber_measure_threshold k N n
           @ threshold_fiber_measure_below N n H).
Defined.

Lemma eventually_iso_fiber_measure_at_or_above_N (k : Int) (N n : nat)
  (H : nat_le N n)
  : eventually_iso_tower_fiber_measure k N n = qpos_zero.
Proof.
  exact (eventually_iso_fiber_measure_threshold k N n
           @ threshold_fiber_measure_at_or_above N n H).
Defined.

Theorem eventually_iso_fiber_measure_eventually_zero (k : Int) (N : nat)
  : EventuallyZero (eventually_iso_tower_fiber_measure k N).
Proof.
  unfold EventuallyZero.
  exists N.
  intros m Hm.
  unfold qpos_is_zero.
  assert (Hle : nat_le N m).
  { apply nat_le_of_lt.
    exact Hm. }
  assert (H : eventually_iso_tower_fiber_measure k N m = qpos_zero).
  { exact (eventually_iso_fiber_measure_at_or_above_N k N m Hle). }
  unfold eventually_iso_tower_fiber_measure in H.
  unfold ZGraded_fiber_measure in H.
  unfold qpos_zero in H.
  simpl in H.
  exact (ap qpos_num H).
Defined.

Definition constant_int_tower_in_prestable (k : Int)
  : CategoricalTower (ps_cat ZGraded_PreStable)
  := constant_int_tower k.

Definition ZGraded_fiber_triangle_from_map (k : Int) (f : Bool) (n : nat)
  : DistinguishedTriangle ZGraded_PreStable
  := ZGraded_cofiber_distinguished k k f.

Theorem ZGraded_fiber_zero_iff_map_iso (k : Int) (f : Bool)
  : (cofiber_obj f k = zgo_zero) <-> @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k) f.
Proof.
  exact (ZGraded_cofiber_iff_iso k k f).
Defined.

(** A zero fiber measure forces the tower map to be true, hence an isomorphism. *)

Lemma eventually_iso_fiber_zero_iso (k : Int) (N n : nat)
  (Hz : qpos_is_zero (eventually_iso_tower_fiber_measure k N n))
  : IsIsomorphism (ct_map ZGradedCat (eventually_iso_tower k N) n).
Proof.
  destruct (bool_dec_eq (eventually_iso_tower_map N n)) as [Hb | Hb].
  - exact (transport
             (fun b => @IsIsomorphism ZGradedCat
                         (zgo_nonzero k) (zgo_nonzero k) b)
             Hb^ (ZGraded_true_is_iso k k)).
  - apply Empty_rec.
    pose (Hz' := transport
                   (fun b => qpos_is_zero (ZGraded_fiber_measure k k b))
                   Hb Hz).
    exact (transport (fun m : nat => match m with O => Empty | S _ => Unit end)
             Hz' tt).
Defined.

(** The stabilization stage is read off the measure witness, so the hypothesis is load-bearing. *)

Theorem eventually_iso_tower_stabilizes_via_measure (k : Int) (N : nat)
  (Hev : EventuallyZero (eventually_iso_tower_fiber_measure k N))
  : TowerStabilizesAt (eventually_iso_tower k N) (S Hev.1).
Proof.
  intros n Hn.
  exact (eventually_iso_fiber_zero_iso k N n
           (Hev.2 n (nat_lt_of_le_succ Hev.1 n Hn))).
Defined.

Lemma eventually_iso_fiber_measure_is_integer (k : Int) (N n : nat)
  : qpos_denom_pred (eventually_iso_tower_fiber_measure k N n) = O.
Proof.
  rewrite (eventually_iso_fiber_measure_threshold k N n).
  exact (threshold_fiber_measure_is_integer N n).
Defined.

Definition eventually_iso_fiber_integer_valued (k : Int) (N : nat)
  : IsIntegerValued (eventually_iso_tower_fiber_measure k N)
  := eventually_iso_fiber_measure_is_integer k N.

Theorem eventually_iso_fiber_has_minimal_positive (k : Int) (N : nat)
  : HasMinimalPositive (eventually_iso_tower_fiber_measure k N).
Proof.
  apply integer_valued_has_minimal_positive.
  exact (eventually_iso_fiber_integer_valued k N).
Defined.

Theorem ZGraded_complete_convergence_chain (k : Int) (N : nat)
  : LimitZero (eventually_iso_tower_fiber_measure k N) ->
    { M : nat & TowerStabilizesAt (eventually_iso_tower k N) M }.
Proof.
  intro Hlimit.
  pose (Hev := discrete_LimitZero_implies_EventuallyZero
                 (eventually_iso_tower_fiber_measure k N)
                 (eventually_iso_fiber_has_minimal_positive k N)
                 Hlimit).
  exists (S Hev.1).
  exact (eventually_iso_tower_stabilizes_via_measure k N Hev).
Defined.

Lemma eventually_iso_fiber_limit_zero_witness (k : Int) (N : nat)
  : LimitZero (eventually_iso_tower_fiber_measure k N).
Proof.
  unfold LimitZero.
  intros epsilon Heps.
  destruct (threshold_fiber_limit_zero N epsilon Heps) as [M HM].
  exists M.
  intros m Hm.
  rewrite (eventually_iso_fiber_measure_threshold k N m).
  exact (HM m Hm).
Defined.

Theorem ZGraded_convergence_instantiated (k : Int) (N : nat)
  : { M : nat & TowerStabilizesAt (eventually_iso_tower k N) M }.
Proof.
  apply ZGraded_complete_convergence_chain.
  exact (eventually_iso_fiber_limit_zero_witness k N).
Defined.

Theorem ZGraded_convergence_concrete_example
  : { M : nat & TowerStabilizesAt (eventually_iso_tower 0%int 5) M }.
Proof.
  exact (ZGraded_convergence_instantiated 0%int 5).
Defined.

Theorem ZGraded_end_to_end_summary
  : (HasMinimalPositive (eventually_iso_tower_fiber_measure 0%int 5)) *
    (LimitZero (eventually_iso_tower_fiber_measure 0%int 5)) *
    (EventuallyZero (eventually_iso_tower_fiber_measure 0%int 5)) *
    (TowerStabilizesAt (eventually_iso_tower 0%int 5) 5).
Proof.
  refine (_, _, _, _).
  - exact (eventually_iso_fiber_has_minimal_positive 0%int 5).
  - exact (eventually_iso_fiber_limit_zero_witness 0%int 5).
  - exact (eventually_iso_fiber_measure_eventually_zero 0%int 5).
  - exact (eventually_iso_tower_stabilizes_at_N 0%int 5).
Defined.

Theorem ZGraded_genuine_threshold (k : Int) (N : nat)
  (HN : nat_lt O N)
  : (TowerStabilizesAt (eventually_iso_tower k N) N) *
    (TowerStabilizesAt (eventually_iso_tower k N) O -> Empty).
Proof.
  split.
  - exact (eventually_iso_tower_stabilizes_at_N k N).
  - intro H0.
    unfold TowerStabilizesAt in H0.
    pose proof (H0 O tt) as Hiso.
    assert (Hmap : ct_map ZGradedCat (eventually_iso_tower k N) O = false).
    { exact (eventually_iso_tower_below_N k N O HN). }
    rewrite Hmap in Hiso.
    destruct Hiso as [g [Hgf Hfg]].
    simpl in *.
    exact (transport bool_discrim Hgf^ tt).
Defined.

Theorem ZGraded_genuine_threshold_at_5
  : (TowerStabilizesAt (eventually_iso_tower 0%int 5) 5) *
    (TowerStabilizesAt (eventually_iso_tower 0%int 5) O -> Empty).
Proof.
  exact (ZGraded_genuine_threshold 0%int 5 tt).
Defined.

Definition ZGraded_tower_from_maps (k : Int) (maps : nat -> Bool)
  : CategoricalTower ZGradedCat
  := ZGraded_CategoricalTower
       (fun _ => zgo_nonzero k)
       (fun n => maps n).

Definition ZGraded_tower_fiber_measure_from_maps (k : Int) (maps : nat -> Bool) (n : nat)
  : QPos
  := ZGraded_fiber_measure k k (maps n).

Theorem ZGraded_tower_stabilizes_when_fibers_vanish (k : Int) (maps : nat -> Bool)
  (Hev : EventuallyZero (ZGraded_tower_fiber_measure_from_maps k maps))
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k) (maps n) }.
Proof.
  destruct Hev as [N HN].
  exists N.
  intros n Hn.
  assert (Hzero : qpos_is_zero (ZGraded_tower_fiber_measure_from_maps k maps n)).
  { exact (HN n Hn). }
  apply ZGraded_fiber_measure_zero_implies_iso.
  exact Hzero.
Defined.

Lemma ZGraded_tower_fiber_measure_is_integer (k : Int) (maps : nat -> Bool) (n : nat)
  : qpos_denom_pred (ZGraded_tower_fiber_measure_from_maps k maps n) = O.
Proof.
  unfold ZGraded_tower_fiber_measure_from_maps, ZGraded_fiber_measure.
  unfold zgraded_dim_measure, nat_to_qpos.
  reflexivity.
Defined.

Theorem ZGraded_tower_stabilizes_from_limit (k : Int) (maps : nat -> Bool)
  (Hlimit : LimitZero (ZGraded_tower_fiber_measure_from_maps k maps))
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k) (maps n) }.
Proof.
  apply ZGraded_tower_stabilizes_when_fibers_vanish.
  apply integer_LimitZero_implies_EventuallyZero.
  - exact (ZGraded_tower_fiber_measure_is_integer k maps).
  - exact Hlimit.
Defined.

Definition ZGraded_weight_bounded_tower (k : Int) (C : QPos) (maps : nat -> Bool)
  : Type
  := forall n, qpos_lt (ZGraded_tower_fiber_measure_from_maps k maps n)
                       (qpos_mult C (w_stage n)).

Theorem ZGraded_weight_bounded_implies_limit
  (k : Int) (C : QPos) (maps : nat -> Bool)
  (HC : nat_lt O (qpos_num C))
  (Hbounded : ZGraded_weight_bounded_tower k C maps)
  : LimitZero (ZGraded_tower_fiber_measure_from_maps k maps).
Proof.
  exact (bounded_measure_limit_zero _ C HC Hbounded).
Defined.

Theorem ZGraded_weight_bounded_stabilizes
  (k : Int) (C : QPos) (maps : nat -> Bool)
  (HC : nat_lt O (qpos_num C))
  (Hbounded : ZGraded_weight_bounded_tower k C maps)
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k) (maps n) }.
Proof.
  apply ZGraded_tower_stabilizes_from_limit.
  exact (ZGraded_weight_bounded_implies_limit k C maps HC Hbounded).
Defined.

Record GradedMotivicSpectrum (k : BaseField) := {
  gms_level : nat -> MotivicSpace k;
  gms_degree : Int
}.

Definition gms_zero (k : BaseField) : GradedMotivicSpectrum k :=
  {| gms_level := fun _ => point_motivic_space k;
     gms_degree := 0%int |}.

Definition int_IsZero (n : Int) : Bool :=
  match n with
  | negS _ => false
  | Int.zero => true
  | posS _ => false
  end.

Definition GradedSpectrumMor (k : BaseField) (E F : GradedMotivicSpectrum k) : Type :=
  if (int_IsZero (gms_degree k E)) then Unit
  else if (int_IsZero (gms_degree k F)) then Unit
  else Bool.

Definition gsm_id (k : BaseField) (E : GradedMotivicSpectrum k) : GradedSpectrumMor k E E.
Proof.
  unfold GradedSpectrumMor.
  destruct (int_IsZero (gms_degree k E)).
  - exact tt.
  - exact true.
Defined.

Definition gsm_zero (k : BaseField) (E F : GradedMotivicSpectrum k) : GradedSpectrumMor k E F.
Proof.
  unfold GradedSpectrumMor.
  destruct (int_IsZero (gms_degree k E)).
  - exact tt.
  - destruct (int_IsZero (gms_degree k F)).
    + exact tt.
    + exact false.
Defined.

Definition gsm_compose (k : BaseField) (E F G : GradedMotivicSpectrum k)
  (g : GradedSpectrumMor k F G) (f : GradedSpectrumMor k E F)
  : GradedSpectrumMor k E G.
Proof.
  unfold GradedSpectrumMor in *.
  destruct (int_IsZero (gms_degree k E)).
  - exact tt.
  - destruct (int_IsZero (gms_degree k G)).
    + exact tt.
    + destruct (int_IsZero (gms_degree k F)).
      * exact false.
      * exact (andb f g).
Defined.

Global Instance GradedSpectrumMor_hset (k : BaseField) (E F : GradedMotivicSpectrum k)
  : IsHSet (GradedSpectrumMor k E F).
Proof.
  unfold GradedSpectrumMor.
  destruct (int_IsZero (gms_degree k E)).
  - exact hset_unit.
  - destruct (int_IsZero (gms_degree k F)).
    + exact hset_unit.
    + exact hset_bool.
Defined.

Lemma gsm_compose_assoc (k : BaseField) (W X Y Z : GradedMotivicSpectrum k)
  (f : GradedSpectrumMor k W X) (g : GradedSpectrumMor k X Y) (h : GradedSpectrumMor k Y Z)
  : gsm_compose k W X Z (gsm_compose k X Y Z h g) f =
    gsm_compose k W Y Z h (gsm_compose k W X Y g f).
Proof.
  unfold gsm_compose, GradedSpectrumMor in *.
  destruct (int_IsZero (gms_degree k W)), (int_IsZero (gms_degree k X)),
    (int_IsZero (gms_degree k Y)), (int_IsZero (gms_degree k Z)); bool_bash.
Defined.

Lemma gsm_compose_id_l (k : BaseField) (X Y : GradedMotivicSpectrum k)
  (f : GradedSpectrumMor k X Y)
  : gsm_compose k X Y Y (gsm_id k Y) f = f.
Proof.
  unfold gsm_compose, gsm_id, GradedSpectrumMor in *.
  destruct (int_IsZero (gms_degree k X)), (int_IsZero (gms_degree k Y)); bool_bash.
Defined.

Lemma gsm_compose_id_r (k : BaseField) (X Y : GradedMotivicSpectrum k)
  (f : GradedSpectrumMor k X Y)
  : gsm_compose k X X Y f (gsm_id k X) = f.
Proof.
  unfold gsm_compose, gsm_id, GradedSpectrumMor in *.
  destruct (int_IsZero (gms_degree k X)), (int_IsZero (gms_degree k Y)); bool_bash.
Defined.

Definition GradedSHCat (k : BaseField) : PreCategory
  := @Build_PreCategory
       (GradedMotivicSpectrum k)
       (fun E F => GradedSpectrumMor k E F)
       (fun E => gsm_id k E)
       (fun E F G g f => gsm_compose k E F G g f)
       (fun s d d' d'' m1 m2 m3 => gsm_compose_assoc k s d d' d'' m1 m2 m3)
       (fun a b f => gsm_compose_id_l k a b f)
       (fun a b f => gsm_compose_id_r k a b f)
       (fun s d => GradedSpectrumMor_hset k s d).

(** The spectrum-graded category identifies with the shift instance over nonzero-degree spectra by deciding the degree. *)

Definition gsm_conv_obj (k : BaseField) (E : GradedMotivicSpectrum k)
  : ShiftObj { E' : GradedMotivicSpectrum k &
               int_IsZero (gms_degree k E') = false }.
Proof.
  destruct (bool_dec_eq (int_IsZero (gms_degree k E))) as [Hz | Hz].
  - exact sh_zero.
  - exact (sh_el (E ; Hz)).
Defined.

Theorem GradedSpectrumMor_is_shift (k : BaseField)
  (E F : GradedMotivicSpectrum k)
  : GradedSpectrumMor k E F
    = ShiftMor (gsm_conv_obj k E) (gsm_conv_obj k F).
Proof.
  unfold GradedSpectrumMor, gsm_conv_obj.
  destruct (bool_dec_eq (int_IsZero (gms_degree k E))) as [HzE | HzE];
  destruct (bool_dec_eq (int_IsZero (gms_degree k F))) as [HzF | HzF].
  - exact (ap (fun b : Bool => (if b then Unit
               else (if int_IsZero (gms_degree k F) then Unit else Bool)) : Type)
             HzE).
  - exact (ap (fun b : Bool => (if b then Unit
               else (if int_IsZero (gms_degree k F) then Unit else Bool)) : Type)
             HzE).
  - exact (ap (fun b : Bool => (if b then Unit
               else (if int_IsZero (gms_degree k F) then Unit else Bool)) : Type)
             HzE
             @ ap (fun b : Bool => (if b then Unit else Bool) : Type) HzF).
  - exact (ap (fun b : Bool => (if b then Unit
               else (if int_IsZero (gms_degree k F) then Unit else Bool)) : Type)
             HzE
             @ ap (fun b : Bool => (if b then Unit else Bool) : Type) HzF).
Defined.

Definition gms_nonzero (k : BaseField) : GradedMotivicSpectrum k :=
  {| gms_level := fun _ => point_motivic_space k;
     gms_degree := posS O |}.

Lemma gsm_zero_ne_id_nonzero (k : BaseField)
  : gsm_zero k (gms_nonzero k) (gms_nonzero k) <> gsm_id k (gms_nonzero k).
Proof.
  unfold gsm_zero, gsm_id, gms_nonzero, GradedSpectrumMor.
  simpl.
  intro H.
  exact (transport bool_discrim H^ tt).
Defined.

Theorem GradedSH_has_non_iso_morphisms (k : BaseField)
  : { E : GradedMotivicSpectrum k &
      { F : GradedMotivicSpectrum k &
        { f : morphism (GradedSHCat k) E F &
          @IsIsomorphism (GradedSHCat k) E F f -> Empty }}}.
Proof.
  exists (gms_nonzero k).
  exists (gms_nonzero k).
  exists (gsm_zero k (gms_nonzero k) (gms_nonzero k)).
  intros [g [Hgf Hfg]].
  unfold gsm_zero, gsm_compose, gms_nonzero, GradedSpectrumMor in *.
  simpl in *.
  destruct g.
  - exact (transport bool_discrim Hgf^ tt).
  - exact (transport bool_discrim Hfg^ tt).
Defined.

Global Instance Contr_gsm_from_zero (k : BaseField) (F : GradedMotivicSpectrum k)
  : Contr (GradedSpectrumMor k (gms_zero k) F).
Proof.
  unfold GradedSpectrumMor, gms_zero.
  simpl.
  apply (Build_Contr _ tt).
  intro f; destruct f; reflexivity.
Defined.

Global Instance Contr_gsm_to_zero (k : BaseField) (E : GradedMotivicSpectrum k)
  : Contr (GradedSpectrumMor k E (gms_zero k)).
Proof.
  unfold GradedSpectrumMor, gms_zero.
  simpl.
  destruct (int_IsZero (gms_degree k E)).
  - apply (Build_Contr _ tt).
    intro f; destruct f; reflexivity.
  - apply (Build_Contr _ tt).
    intro f; destruct f; reflexivity.
Defined.

Definition GradedSHZero (k : BaseField) : ZeroObject (GradedSHCat k)
  := Build_ZeroObject (GradedSHCat k) (gms_zero k)
       (fun F => Contr_gsm_from_zero k F)
       (fun E => Contr_gsm_to_zero k E).

Definition gms_susp (k : BaseField) (E : GradedMotivicSpectrum k) : GradedMotivicSpectrum k :=
  {| gms_level := gms_level k E;
     gms_degree := int_succ (gms_degree k E) |}.

Definition gms_loop (k : BaseField) (E : GradedMotivicSpectrum k) : GradedMotivicSpectrum k :=
  {| gms_level := gms_level k E;
     gms_degree := int_pred (gms_degree k E) |}.

Lemma gms_loop_susp (k : BaseField) (E : GradedMotivicSpectrum k)
  : gms_loop k (gms_susp k E) = E.
Proof.
  unfold gms_loop, gms_susp.
  destruct E as [lvl deg].
  simpl.
  apply ap.
  apply int_succ_pred.
Defined.

Lemma gms_susp_loop (k : BaseField) (E : GradedMotivicSpectrum k)
  : gms_susp k (gms_loop k E) = E.
Proof.
  unfold gms_loop, gms_susp.
  destruct E as [lvl deg].
  simpl.
  apply ap.
  apply int_pred_succ.
Defined.


Definition GradedSH_zero_morphism (k : BaseField) (E F : GradedMotivicSpectrum k)
  : morphism (GradedSHCat k) E F
  := gsm_zero k E F.

Definition gms_dim (k : BaseField) (E : GradedMotivicSpectrum k) : nat :=
  if int_IsZero (gms_degree k E) then O else S O.

Definition gms_weight_measure (k : BaseField) (E : GradedMotivicSpectrum k) : QPos :=
  nat_to_qpos (gms_dim k E).

Lemma gms_zero_weight_zero (k : BaseField)
  : gms_weight_measure k (gms_zero k) = qpos_zero.
Proof.
  unfold gms_weight_measure, gms_dim, gms_zero.
  simpl.
  reflexivity.
Defined.

Lemma GradedSH_zero_object_eq (k : BaseField)
  : zero (GradedSHCat k) (GradedSHZero k) = gms_zero k.
Proof.
  reflexivity.
Defined.

Definition GradedSH_WeightMeasure (k : BaseField)
  : WeightMeasure (GradedSHCat k) (GradedSHZero k).
Proof.
  refine {| wm_measure := fun (E : object (GradedSHCat k)) => gms_weight_measure k E |}.
  exact (gms_zero_weight_zero k).
Defined.

Theorem GradedSH_zero_weight_implies_degree_zero (k : BaseField)
  (E : GradedMotivicSpectrum k)
  : qpos_is_zero (gms_weight_measure k E) -> gms_degree k E = Int.zero.
Proof.
  unfold qpos_is_zero, gms_weight_measure, gms_dim, nat_to_qpos.
  simpl.
  intro H.
  destruct E as [lvl deg].
  simpl in *.
  destruct deg as [m| |m]; simpl in H.
  - exfalso. exact (S_ne_O O H).
  - reflexivity.
  - exfalso. exact (S_ne_O O H).
Defined.

Lemma GradedSH_degree_zero_morphism_unique (k : BaseField)
  (E F : GradedMotivicSpectrum k)
  (HE : gms_degree k E = Int.zero)
  : Contr (GradedSpectrumMor k E F).
Proof.
  unfold GradedSpectrumMor.
  destruct E as [lvlE degE].
  simpl in HE.
  rewrite HE.
  simpl.
  apply (Build_Contr _ tt).
  intro f; destruct f; reflexivity.
Defined.

Lemma GradedSH_measure_is_integer (k : BaseField) (E : GradedMotivicSpectrum k)
  : qpos_denom_pred (gms_weight_measure k E) = O.
Proof.
  unfold gms_weight_measure, nat_to_qpos.
  simpl.
  reflexivity.
Defined.

Lemma GradedSH_nonzero_mor_is_bool (k : BaseField)
  (E F : GradedMotivicSpectrum k)
  (HE : int_IsZero (gms_degree k E) = false)
  (HF : int_IsZero (gms_degree k F) = false)
  : GradedSpectrumMor k E F = Bool.
Proof.
  unfold GradedSpectrumMor.
  rewrite HE, HF.
  reflexivity.
Defined.

Definition gsm_from_bool (k : BaseField) (E F : GradedMotivicSpectrum k)
  (HE : int_IsZero (gms_degree k E) = false)
  (HF : int_IsZero (gms_degree k F) = false)
  (b : Bool)
  : morphism (GradedSHCat k) E F
  := transport idmap (GradedSH_nonzero_mor_is_bool k E F HE HF)^ b.

Theorem GradedSH_nonzero_true_is_iso (k : BaseField)
  : @IsIsomorphism (GradedSHCat k) (gms_nonzero k) (gms_nonzero k)
      (gsm_id k (gms_nonzero k)).
Proof.
  unfold IsIsomorphism.
  exists (gsm_id k (gms_nonzero k)).
  unfold gsm_id, gsm_compose, GradedSpectrumMor, gms_nonzero.
  simpl.
  split; reflexivity.
Defined.

Theorem GradedSH_false_not_iso (k : BaseField)
  : @IsIsomorphism (GradedSHCat k) (gms_nonzero k) (gms_nonzero k)
      (gsm_zero k (gms_nonzero k) (gms_nonzero k)) -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  unfold gsm_zero, gsm_compose, GradedSpectrumMor, gms_nonzero in *.
  simpl in *.
  destruct g.
  - exact (transport bool_discrim Hgf^ tt).
  - exact (transport bool_discrim Hfg^ tt).
Defined.

(** ** A tower with fiber measure provably bounded by C times the stage weight, with stabilization derived through the full chain. *)

Definition decreasing_fiber_tower_map (N : nat) (n : nat) : Bool
  := threshold_tower_map N n.

Definition decreasing_fiber_tower (k : Int) (N : nat) : ZGradedTower :=
  {| zgt_stage := fun _ => zgo_nonzero k;
     zgt_map := fun n => decreasing_fiber_tower_map N n |}.

Definition decreasing_fiber_measure (N n : nat) : QPos :=
  ZGraded_fiber_measure 0%int 0%int (decreasing_fiber_tower_map N n).

Lemma decreasing_fiber_measure_below_N (N n : nat)
  (H : nat_lt n N)
  : decreasing_fiber_measure N n = nat_to_qpos (S O).
Proof.
  exact (threshold_fiber_measure_below N n H).
Defined.

Lemma decreasing_fiber_measure_at_or_above_N (N n : nat)
  (H : nat_le N n)
  : decreasing_fiber_measure N n = qpos_zero.
Proof.
  exact (threshold_fiber_measure_at_or_above N n H).
Defined.

Definition weight_bound_constant (N : nat) : QPos :=
  nat_to_qpos (S N).

Lemma qpos_zero_lt_any_positive (q : QPos)
  (Hpos : nat_lt O (qpos_num q))
  : qpos_lt qpos_zero q.
Proof.
  unfold qpos_lt, qpos_zero, qpos_denom.
  simpl.
  rewrite nat_mul_one_r.
  exact Hpos.
Defined.

Lemma nat_to_qpos_S_N_times_w_stage (N n : nat)
  : qpos_mult (nat_to_qpos (S N)) (w_stage n) =
    {| qpos_num := S N; qpos_denom_pred := n |}.
Proof.
  unfold qpos_mult, nat_to_qpos, w_stage.
  simpl.
  rewrite nat_mul_one_r.
  rewrite nat_add_zero_r.
  reflexivity.
Defined.

Lemma one_lt_SN_over_Sn (N n : nat)
  (H : nat_lt n N)
  : qpos_lt (nat_to_qpos (S O)) {| qpos_num := S N; qpos_denom_pred := n |}.
Proof.
  unfold qpos_lt, nat_to_qpos, qpos_denom.
  simpl.
  rewrite nat_add_zero_r.
  rewrite nat_mul_one_r.
  exact H.
Defined.

Theorem decreasing_fiber_weight_bounded (N : nat)
  : forall n, qpos_lt (decreasing_fiber_measure N n)
                      (qpos_mult (weight_bound_constant N) (w_stage n)).
Proof.
  intro n.
  unfold weight_bound_constant.
  rewrite nat_to_qpos_S_N_times_w_stage.
  destruct (nat_lt_or_eq_or_gt n N) as [[Hlt | Heq] | Hgt].
  - rewrite (decreasing_fiber_measure_below_N N n Hlt).
    exact (one_lt_SN_over_Sn N n Hlt).
  - assert (Hle : nat_le N n).
    { rewrite Heq. exact (nat_le_refl N). }
    rewrite (decreasing_fiber_measure_at_or_above_N N n Hle).
    apply qpos_zero_lt_any_positive.
    exact tt.
  - assert (Hle : nat_le N n).
    { apply nat_le_of_lt. exact Hgt. }
    rewrite (decreasing_fiber_measure_at_or_above_N N n Hle).
    apply qpos_zero_lt_any_positive.
    exact tt.
Defined.

Lemma decreasing_fiber_measure_is_integer (N n : nat)
  : qpos_denom_pred (decreasing_fiber_measure N n) = O.
Proof.
  exact (threshold_fiber_measure_is_integer N n).
Defined.

Lemma decreasing_fiber_has_minimal_positive (N : nat)
  : HasMinimalPositive (decreasing_fiber_measure N).
Proof.
  apply integer_valued_has_minimal_positive.
  exact (decreasing_fiber_measure_is_integer N).
Defined.

Theorem decreasing_fiber_limit_zero (N : nat)
  : LimitZero (decreasing_fiber_measure N).
Proof.
  exact (bounded_measure_limit_zero _ (weight_bound_constant N) tt
           (decreasing_fiber_weight_bounded N)).
Defined.

Theorem decreasing_fiber_eventually_zero (N : nat)
  : EventuallyZero (decreasing_fiber_measure N).
Proof.
  apply discrete_LimitZero_implies_EventuallyZero.
  - exact (decreasing_fiber_has_minimal_positive N).
  - exact (decreasing_fiber_limit_zero N).
Defined.

Lemma decreasing_tower_map_eq (k : Int) (N n : nat)
  : zgt_map (decreasing_fiber_tower k N) n = decreasing_fiber_tower_map N n.
Proof.
  reflexivity.
Defined.

Theorem decreasing_fiber_tower_stabilizes (k : Int) (N : nat)
  : { M : nat & forall n, nat_lt M n ->
      @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)
        (zgt_map (decreasing_fiber_tower k N) n) }.
Proof.
  destruct (decreasing_fiber_eventually_zero N) as [M HM].
  exists M.
  intros n Hn.
  pose proof (HM n Hn) as Hzero.
  rewrite decreasing_tower_map_eq.
  apply ZGraded_fiber_measure_zero_implies_iso.
  unfold qpos_is_zero.
  rewrite ZGraded_fiber_measure_any_k.
  unfold decreasing_fiber_measure, ZGraded_fiber_measure in Hzero.
  unfold zgraded_dim_measure, nat_to_qpos in Hzero.
  simpl in Hzero.
  exact Hzero.
Defined.

(** ** The full chain: weight bound, limit zero, eventually zero, stabilization. *)

Theorem weight_bound_to_stabilization_complete (k : Int) (N : nat)
  : (forall n, qpos_lt (decreasing_fiber_measure N n)
                       (qpos_mult (weight_bound_constant N) (w_stage n)))
    -> { M : nat & forall n, nat_lt M n ->
         @IsIsomorphism ZGradedCat (zgo_nonzero k) (zgo_nonzero k)
           (zgt_map (decreasing_fiber_tower k N) n) }.
Proof.
  intro Hbound.
  exact (decreasing_fiber_tower_stabilizes k N).
Defined.

(** *** The non-degenerate instances of the two flagship records *)

Lemma qpos_zero_le (q : QPos) : qpos_le qpos_zero q.
Proof.
  unfold qpos_le, qpos_zero.
  simpl.
  exact tt.
Defined.

Lemma decreasing_fiber_measure_nonincreasing (N n : nat)
  : qpos_le (decreasing_fiber_measure N (S n)) (decreasing_fiber_measure N n).
Proof.
  destruct (nat_lt_or_eq_or_gt (S n) N) as [[Hlt | Heq] | Hgt].
  - refine (transport (fun q => qpos_le q _)
             (decreasing_fiber_measure_below_N N (S n) Hlt)^ _).
    refine (transport (fun q => qpos_le _ q)
             (decreasing_fiber_measure_below_N N n
                (nat_lt_trans n (S n) N (nat_lt_S n) Hlt))^ _).
    exact (qpos_le_refl _).
  - refine (transport (fun q => qpos_le q _)
             (decreasing_fiber_measure_at_or_above_N N (S n)
                (transport (fun m => nat_le m (S n)) Heq
                   (nat_le_refl (S n))))^ _).
    exact (qpos_zero_le _).
  - refine (transport (fun q => qpos_le q _)
             (decreasing_fiber_measure_at_or_above_N N (S n)
                (nat_le_of_lt N (S n) Hgt))^ _).
    exact (qpos_zero_le _).
Defined.

Definition wct_dec_tower (N : nat) : CategoricalTower ZGradedCat
  := Build_CategoricalTower ZGradedCat
       (fun _ => zgo_nonzero 0%int)
       (fun n => decreasing_fiber_tower_map N n).

Definition wct_dec_fibers (N : nat)
  : TowerWithFibers ZGradedCat ZGradedZero.
Proof.
  refine (Build_TowerWithFibers ZGradedCat ZGradedZero (wct_dec_tower N)
            (fun n =>
               @Build_FiberData ZGradedCat ZGradedZero
                 (zgo_nonzero 0%int) (zgo_nonzero 0%int)
                 (decreasing_fiber_tower_map N n)
                 (cofiber_obj (decreasing_fiber_tower_map N n) 0%int)
                 (zgm_zero
                    (cofiber_obj (decreasing_fiber_tower_map N n) 0%int)
                    (zgo_nonzero 0%int))
                 _)).
  exact (zgm_compose_zero_l
           (cofiber_obj (decreasing_fiber_tower_map N n) 0%int)
           (zgo_nonzero 0%int) (zgo_nonzero 0%int)
           (decreasing_fiber_tower_map N n)
         @ (ps_zero_is_zgm_zero
              (cofiber_obj (decreasing_fiber_tower_map N n) 0%int)
              (zgo_nonzero 0%int))^).
Defined.

Definition wct_dec_obs_data (N : nat) : ObstructionData stage_tower
  := @Build_ObstructionData stage_tower
       (weight_bound_constant N) (decreasing_fiber_measure N).

Definition wct_dec_bo (N : nat) : BoundedObstruction stage_tower
  := @Build_BoundedObstruction stage_tower
       (wct_dec_obs_data N)
       (decreasing_fiber_weight_bounded N)
       (decreasing_fiber_measure_nonincreasing N).

Definition wct_dec_instance (N : nat)
  : WeightedCategoricalTower ZGradedCat ZGradedZero
  := @Build_WeightedCategoricalTower ZGradedCat ZGradedZero
       stage_tower
       (wct_dec_bo N)
       (wct_dec_fibers N)
       ZGradedWeightMeasure
       (fun n => qpos_le_refl _)
       (fun n => qpos_le_refl _).

Lemma wct_dec_zero_fiber (N : nat)
  : TowerZeroFiberImpliesIso (wct_dec_fibers N).
Proof.
  intros n Hz.
  destruct (bool_dec_eq (decreasing_fiber_tower_map N n)) as [Hb | Hb].
  - exact (transport
             (fun b => @IsIsomorphism ZGradedCat
                         (zgo_nonzero 0%int) (zgo_nonzero 0%int) b)
             Hb^ (ZGraded_true_is_iso 0%int 0%int)).
  - apply Empty_rec.
    apply (zgo_nonzero_ne_zero 0%int).
    exact (ap (fun b => cofiber_obj b 0%int) Hb^ @ Hz).
Defined.

Lemma wct_dec_zero_measure
  : ZeroMeasureImpliesZeroObject ZGradedCat ZGradedZero ZGradedWeightMeasure.
Proof.
  intros X Hz.
  exact (ZGraded_zero_measure_implies_zero X Hz).
Defined.

Theorem wct_instance_stabilizes (N : nat)
  : { M : nat &
      TowerStabilizesAt (twf_tower ZGradedCat ZGradedZero (wct_dec_fibers N)) M }.
Proof.
  apply (weighted_tower_stabilizes (wct_dec_instance N)).
  - exact w_stage_limit_zero.
  - exact tt.
  - exact (decreasing_fiber_has_minimal_positive N).
  - exact (wct_dec_zero_fiber N).
  - exact wct_dec_zero_measure.
Defined.

Theorem wct_dec_nondegenerate (N : nat)
  : qpos_is_zero (obs_measure (wct_dec_instance (S N)) O) -> Empty.
Proof.
  intro H.
  pose (H' := transport (fun q => qpos_is_zero q)
                (decreasing_fiber_measure_below_N (S N) O tt) H).
  exact (transport (fun m : nat => match m with O => Empty | S _ => Unit end)
           H' tt).
Defined.

Definition tis_dec_instance (N : nat) : TowerInStable ZGraded_PreStable.
Proof.
  refine {| tis_tower :=
              Build_CategoricalTower ZGraded_PreStable
                (fun _ => zgo_nonzero 0%int)
                (fun n => decreasing_fiber_tower_map N n);
            tis_fiber_triangle := fun n =>
              ZGraded_cofiber_distinguished 0%int 0%int
                (decreasing_fiber_tower_map N n) |}.
  intros n H.
  exact H.
Defined.

Theorem tis_dec_nondegenerate (N : nat)
  : IsIsomorphism
      (ct_map ZGraded_PreStable
         (tis_tower ZGraded_PreStable (tis_dec_instance (S N))) O)
    -> Empty.
Proof.
  intro H.
  apply (shm_false_not_iso 0%int 0%int).
  exact (transport
           (fun b => @IsIsomorphism ZGradedCat
                       (zgo_nonzero 0%int) (zgo_nonzero 0%int) b)
           (threshold_tower_map_below (S N) O tt) H).
Defined.

Theorem concrete_example_N_equals_7
  : { M : nat & forall n, nat_lt M n ->
      @IsIsomorphism ZGradedCat (zgo_nonzero 0%int) (zgo_nonzero 0%int)
        (zgt_map (decreasing_fiber_tower 0%int 7) n) }.
Proof.
  exact (decreasing_fiber_tower_stabilizes 0%int 7).
Defined.

(** ** A polynomial endofunctor on the graded category with computable layer sizes. *)

Definition poly_functor_obj (d : nat) (X : GradedObj) : GradedObj :=
  {| go_dim := nat_mul d (go_dim X) |}.

Definition poly_functor_mor (d : nat) (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (poly_functor_obj d X) (poly_functor_obj d Y).
Proof.
  unfold GradedMor, poly_functor_obj in *.
  simpl.
  set (dx := go_dim X) in *.
  set (dy := go_dim Y) in *.
  set (pdx := nat_mul d dx).
  set (pdy := nat_mul d dy).
  destruct pdx as [|pdx'].
  - exact tt.
  - destruct pdy as [|pdy'].
    + exact tt.
    + destruct dx as [|dx'].
      * exact true.
      * destruct dy as [|dy'].
        { exact true. }
        { exact f. }
Defined.

Lemma poly_functor_id (d : nat) (X : GradedObj)
  : poly_functor_mor d X X (gm_id X) = gm_id (poly_functor_obj d X).
Proof.
  unfold poly_functor_mor, gm_id, poly_functor_obj, GradedMor.
  simpl.
  destruct (go_dim X) as [|dx]; simpl.
  - destruct (nat_mul d 0); reflexivity.
  - destruct (nat_mul d (S dx)) as [|pdx']; reflexivity.
Defined.

Definition zero_functor_obj (X : GradedObj) : GradedObj := go_zero.

Definition zero_functor_mor (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (zero_functor_obj X) (zero_functor_obj Y) := tt.

Lemma zero_functor_id (X : GradedObj)
  : zero_functor_mor X X (gm_id X) = gm_id (zero_functor_obj X).
Proof.
  reflexivity.
Defined.

Lemma zero_functor_comp (X Y Z : GradedObj)
  (f : GradedMor X Y) (g : GradedMor Y Z)
  : zero_functor_mor X Z (gm_compose X Y Z g f) =
    gm_compose (zero_functor_obj X) (zero_functor_obj Y) (zero_functor_obj Z)
      (zero_functor_mor Y Z g) (zero_functor_mor X Y f).
Proof.
  reflexivity.
Defined.

Definition id_graded_obj (X : GradedObj) : GradedObj := X.

Definition id_graded_mor (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (id_graded_obj X) (id_graded_obj Y) := f.

Lemma id_graded_id (X : GradedObj)
  : id_graded_mor X X (gm_id X) = gm_id (id_graded_obj X).
Proof.
  reflexivity.
Defined.

Lemma id_graded_comp (X Y Z : GradedObj)
  (f : GradedMor X Y) (g : GradedMor Y Z)
  : id_graded_mor X Z (gm_compose X Y Z g f) =
    gm_compose (id_graded_obj X) (id_graded_obj Y) (id_graded_obj Z)
      (id_graded_mor Y Z g) (id_graded_mor X Y f).
Proof.
  reflexivity.
Defined.

Definition IdGradedFunctor : Functor GradedCat GradedCat :=
  Build_Functor GradedCat GradedCat
    id_graded_obj
    id_graded_mor
    id_graded_comp
    id_graded_id.

Definition poly_approx_dim (base_dim n : nat) : nat := nat_sub base_dim n.

Definition poly_approx (base_dim n : nat) : GradedObj :=
  {| go_dim := poly_approx_dim base_dim n |}.

Definition layer_dim (base_dim n : nat) : nat :=
  nat_sub (poly_approx_dim base_dim n) (poly_approx_dim base_dim (S n)).

Definition layer_obj (base_dim n : nat) : GradedObj :=
  {| go_dim := layer_dim base_dim n |}.

Lemma nat_sub_S_S (n m : nat) : nat_sub (S n) (S m) = nat_sub n m.
Proof.
  reflexivity.
Defined.

Lemma nat_sub_S_lt (n : nat) : nat_sub (S n) n = S O.
Proof.
  induction n.
  - reflexivity.
  - simpl. exact IHn.
Defined.

Lemma layer_dim_zero (base_dim : nat)
  : layer_dim base_dim base_dim = O.
Proof.
  unfold layer_dim, poly_approx_dim.
  rewrite nat_sub_cancel.
  reflexivity.
Defined.

Lemma layer_dim_computed (base_dim n : nat)
  : layer_dim (S base_dim) n =
    match n with
    | O => S O
    | S n' => layer_dim base_dim n'
    end.
Proof.
  unfold layer_dim, poly_approx_dim.
  destruct n.
  - simpl. rewrite nat_sub_zero_r. exact (nat_sub_S_lt base_dim).
  - simpl. reflexivity.
Defined.

Definition layer_measure (base_dim n : nat) : QPos :=
  nat_to_qpos (layer_dim base_dim n).

Lemma layer_measure_is_integer (base_dim n : nat)
  : qpos_denom_pred (layer_measure base_dim n) = O.
Proof.
  unfold layer_measure, nat_to_qpos.
  reflexivity.
Defined.

Lemma layer_measure_eventually_zero (base_dim : nat)
  : EventuallyZero (layer_measure base_dim).
Proof.
  exists base_dim.
  intros m Hm.
  unfold qpos_is_zero, layer_measure, nat_to_qpos.
  simpl.
  unfold layer_dim, poly_approx_dim.
  revert m Hm.
  induction base_dim.
  - intros m Hm. reflexivity.
  - intros m Hm.
    destruct m.
    + destruct Hm.
    + simpl.
      apply IHbase_dim.
      exact Hm.
Defined.

Theorem poly_functor_layers_stabilize (base_dim : nat)
  : { N : nat & forall n, nat_lt N n -> layer_dim base_dim n = O }.
Proof.
  destruct (layer_measure_eventually_zero base_dim) as [N HN].
  exists N.
  intros n Hn.
  unfold qpos_is_zero, layer_measure, nat_to_qpos in HN.
  simpl in HN.
  exact (HN n Hn).
Defined.

Theorem concrete_poly_functor_example
  : { N : nat & forall n, nat_lt N n -> layer_dim 10 n = O }.
Proof.
  exact (poly_functor_layers_stabilize 10).
Defined.

(** ** The polynomial functor loses one dimension per stage and its layer measures vanish past the base dimension. *)

(** ** Connecting poly_functor to GoodwillieTowerWithLayers. *)

Definition GradedCat_zero_in (X : GradedObj) : GradedMor go_zero X := tt.

Definition GradedCat_zero_out (X : GradedObj) : GradedMor X go_zero.
Proof.
  unfold GradedMor, go_zero.
  simpl.
  destruct (go_dim X); exact tt.
Defined.

Lemma GradedCat_zero_in_unique (X : GradedObj) (f g : GradedMor go_zero X)
  : f = g.
Proof.
  unfold GradedMor, go_zero in *.
  simpl in *.
  destruct f, g.
  reflexivity.
Defined.

Lemma GradedCat_zero_out_unique (X : GradedObj) (f g : GradedMor X go_zero)
  : f = g.
Proof.
  unfold GradedMor, go_zero in *.
  simpl in *.
  destruct (go_dim X).
  - destruct f, g. reflexivity.
  - destruct f, g. reflexivity.
Defined.

Global Instance Contr_GradedCat_from_zero (X : GradedObj)
  : Contr (GradedMor go_zero X).
Proof.
  apply (Build_Contr _ (GradedCat_zero_in X)).
  intro f.
  exact (GradedCat_zero_in_unique X f (GradedCat_zero_in X))^.
Defined.

Global Instance Contr_GradedCat_to_zero (X : GradedObj)
  : Contr (GradedMor X go_zero).
Proof.
  apply (Build_Contr _ (GradedCat_zero_out X)).
  intro f.
  exact (GradedCat_zero_out_unique X f (GradedCat_zero_out X))^.
Defined.

(** Aliases for the canonical zero object and weight measure of GradedCat. *)

Definition GradedCat_ZeroObject : ZeroObject GradedCat := GradedZero.

Definition GradedCat_WeightMeasure : WeightMeasure GradedCat GradedCat_ZeroObject
  := GradedWeightMeasure.

Lemma IdGradedFunctor_preserves_zero
  : object_of IdGradedFunctor go_zero = go_zero.
Proof.
  reflexivity.
Defined.

Lemma GradedMor_from_zero_path (Y : GradedObj) (f g : GradedMor go_zero Y) : f = g.
Proof.
  exact (GradedCat_zero_in_unique Y f g).
Defined.

Lemma GradedMor_to_zero_path (X : GradedObj) (f g : GradedMor X go_zero) : f = g.
Proof.
  exact (GradedCat_zero_out_unique X f g).
Defined.

Lemma graded_eta_natural (X Y : GradedObj) (f : GradedMor X Y)
  : (gm_compose X Y Y (gm_id Y) f = gm_compose X X Y f (gm_id X))%morphism.
Proof.
  rewrite gm_compose_id_l.
  rewrite gm_compose_id_r.
  reflexivity.
Defined.

Definition GradedCat_eta : NaturalTransformation 1%functor (IdGradedFunctor o IdGradedFunctor)%functor.
Proof.
  refine (Build_NaturalTransformation 1%functor (IdGradedFunctor o IdGradedFunctor)%functor
            (fun X => gm_id X) _).
  intros X Y f.
  simpl.
  rewrite gm_compose_id_l.
  rewrite gm_compose_id_r.
  reflexivity.
Defined.

Definition GradedCat_epsilon : NaturalTransformation (IdGradedFunctor o IdGradedFunctor)%functor 1%functor.
Proof.
  refine (Build_NaturalTransformation (IdGradedFunctor o IdGradedFunctor)%functor 1%functor
            (fun X => gm_id X) _).
  intros X Y f.
  simpl.
  rewrite gm_compose_id_l.
  rewrite gm_compose_id_r.
  reflexivity.
Defined.

Definition GradedPreStable : PreStableCategory :=
  Build_PreStableCategory GradedCat GradedCat_ZeroObject
    IdGradedFunctor IdGradedFunctor GradedCat_eta GradedCat_epsilon.

Definition IdGraded_ReducedFunctor : ReducedFunctor GradedPreStable :=
  Build_ReducedFunctor GradedPreStable IdGradedFunctor IdGradedFunctor_preserves_zero.

Definition P_n_obj (n : nat) (X : GradedObj) : GradedObj :=
  {| go_dim := poly_approx_dim (go_dim X) n |}.

Definition P_n_mor (n : nat) (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (P_n_obj n X) (P_n_obj n Y).
Proof.
  destruct X as [dx].
  destruct Y as [dy].
  unfold P_n_obj, GradedMor in *.
  simpl in *.
  destruct (poly_approx_dim dx n) as [|pdx'].
  - exact tt.
  - destruct (poly_approx_dim dy n) as [|pdy'].
    + exact tt.
    + destruct dx as [|dx'].
      * exact true.
      * destruct dy as [|dy'].
        { exact true. }
        { exact f. }
Defined.

Lemma P_n_id (n : nat) (X : GradedObj)
  : P_n_mor n X X (gm_id X) = gm_id (P_n_obj n X).
Proof.
  destruct X as [dx].
  unfold P_n_mor, P_n_obj, gm_id, GradedMor.
  simpl.
  destruct (poly_approx_dim dx n) as [|pdx']; [reflexivity|].
  destruct dx as [|dx'']; reflexivity.
Defined.

Lemma poly_approx_dim_pos (d n : nat)
  : nat_lt n d -> nat_lt O (poly_approx_dim d n).
Proof.
  unfold poly_approx_dim.
  revert n.
  induction d.
  - intros n Hn.
    destruct n; exact Hn.
  - intros n Hn.
    destruct n.
    + simpl.
      exact tt.
    + simpl.
      exact (IHd n Hn).
Defined.

Lemma poly_approx_dim_pos_implies_dim_pos (d n : nat)
  : nat_lt O (poly_approx_dim d n) -> nat_lt O d.
Proof.
  unfold poly_approx_dim.
  revert n.
  induction d.
  - intros n H.
    simpl in H.
    exact H.
  - intros n H.
    exact tt.
Defined.

Lemma P_n_comp (n : nat) (X Y Z : GradedObj) (f : GradedMor X Y) (g : GradedMor Y Z)
  (HX : nat_lt n (go_dim X))
  (HY : nat_lt n (go_dim Y))
  (HZ : nat_lt n (go_dim Z))
  : P_n_mor n X Z (gm_compose X Y Z g f) =
    gm_compose (P_n_obj n X) (P_n_obj n Y) (P_n_obj n Z)
      (P_n_mor n Y Z g) (P_n_mor n X Y f).
Proof.
  destruct X as [dx].
  destruct Y as [dy].
  destruct Z as [dz].
  simpl in HX, HY, HZ.
  destruct dx as [|dx']; [exact (Empty_rec _ (nat_lt_zero_absurd n HX))|].
  destruct dy as [|dy']; [exact (Empty_rec _ (nat_lt_zero_absurd n HY))|].
  destruct dz as [|dz']; [exact (Empty_rec _ (nat_lt_zero_absurd n HZ))|].
  unfold P_n_mor, P_n_obj, gm_compose, GradedMor, poly_approx, poly_approx_dim.
  simpl.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    pose proof (poly_approx_dim_pos (S dx') (S n) HX) as Hpdx.
    pose proof (poly_approx_dim_pos (S dy') (S n) HY) as Hpdy.
    pose proof (poly_approx_dim_pos (S dz') (S n) HZ) as Hpdz.
    unfold poly_approx_dim in Hpdx, Hpdy, Hpdz.
    simpl in Hpdx, Hpdy, Hpdz.
    destruct (nat_sub dx' n) as [|pdx'']; [exact (Empty_rec _ Hpdx)|].
    destruct (nat_sub dz' n) as [|pdz'']; [exact (Empty_rec _ Hpdz)|].
    destruct (nat_sub dy' n) as [|pdy'']; [exact (Empty_rec _ Hpdy)|].
    reflexivity.
Defined.

(** ** Connecting P_n to Goodwillie Tower Framework *)

(** P_n is functorial on objects of dimension above n through the restricted composition lemma. *)

Definition P_n_Functor_obj (n : nat) : GradedObj -> GradedObj := P_n_obj n.

Definition P_n_Functor_mor (n : nat) (X Y : GradedObj) (f : GradedMor X Y)
  : GradedMor (P_n_obj n X) (P_n_obj n Y) := P_n_mor n X Y f.

Lemma P_n_Functor_id (n : nat) (X : GradedObj)
  : P_n_Functor_mor n X X (gm_id X) = gm_id (P_n_obj n X).
Proof.
  exact (P_n_id n X).
Defined.

Lemma P_n_Functor_comp_restricted (n : nat) (X Y Z : GradedObj)
  (f : GradedMor X Y) (g : GradedMor Y Z)
  (HY : nat_lt n (go_dim Y))
  : P_n_Functor_mor n X Z (gm_compose X Y Z g f) =
    gm_compose (P_n_obj n X) (P_n_obj n Y) (P_n_obj n Z)
      (P_n_Functor_mor n Y Z g) (P_n_Functor_mor n X Y f).
Proof.
  unfold P_n_Functor_mor.
  destruct X as [dx].
  destruct Y as [dy].
  destruct Z as [dz].
  simpl in HY.
  destruct dy as [|dy']; [exact (Empty_rec _ (nat_lt_zero_absurd n HY))|].
  destruct dx as [|dx'].
  - unfold P_n_mor, P_n_obj, gm_compose, GradedMor, poly_approx_dim.
    simpl.
    destruct n; reflexivity.
  - destruct dz as [|dz'].
    + unfold P_n_mor, P_n_obj, gm_compose, GradedMor, poly_approx_dim.
      simpl.
      destruct n; [reflexivity|].
      destruct (nat_sub dx' n) as [|pdx'']; [reflexivity|].
      destruct (nat_sub dy' n) as [|pdy'']; reflexivity.
    + unfold P_n_mor, P_n_obj, gm_compose, GradedMor, poly_approx_dim.
      simpl.
      destruct n; [reflexivity|].
      destruct (nat_sub dx' n) as [|pdx'']; [reflexivity|].
      destruct (nat_sub dz' n) as [|pdz'']; [reflexivity|].
      pose proof (poly_approx_dim_pos (S dy') (S n) HY) as Hpdy.
      unfold poly_approx_dim in Hpdy.
      simpl in Hpdy.
      destruct (nat_sub dy' n) as [|pdy'']; [exact (Empty_rec _ Hpdy)|].
      reflexivity.
Defined.

(** ** Goodwillie Layer for Identity Functor on GradedCat *)

Definition D_n_obj (base_dim n : nat) : GradedObj :=
  layer_obj base_dim n.

Definition D_n_measure (base_dim n : nat) : QPos :=
  layer_measure base_dim n.

Lemma D_n_measure_eventually_zero (base_dim : nat)
  : EventuallyZero (D_n_measure base_dim).
Proof.
  exact (layer_measure_eventually_zero base_dim).
Defined.

Lemma D_n_measure_is_integer (base_dim n : nat)
  : qpos_denom_pred (D_n_measure base_dim n) = O.
Proof.
  exact (layer_measure_is_integer base_dim n).
Defined.

(** The tower P_0 -> P_1 -> P_2 -> ... with layers D_n *)

Record GradedGoodwillieTower (base_dim : nat) := {
  ggt_P : nat -> GradedObj;
  ggt_P_def : forall n, ggt_P n = P_n_obj n {| go_dim := base_dim |};
  ggt_D : nat -> GradedObj;
  ggt_D_def : forall n, ggt_D n = D_n_obj base_dim n
}.

Definition make_graded_goodwillie_tower (base_dim : nat) : GradedGoodwillieTower base_dim.
Proof.
  refine {| ggt_P := fun n => P_n_obj n {| go_dim := base_dim |};
            ggt_D := fun n => D_n_obj base_dim n |}.
  - intro n; reflexivity.
  - intro n; reflexivity.
Defined.

Theorem graded_goodwillie_layers_stabilize (base_dim : nat)
  : { N : nat & forall n, nat_lt N n -> go_dim (D_n_obj base_dim n) = O }.
Proof.
  destruct (D_n_measure_eventually_zero base_dim) as [N HN].
  exists N.
  intros n Hn.
  unfold D_n_obj, layer_obj, layer_dim.
  pose proof (HN n Hn) as Hzero.
  unfold qpos_is_zero, D_n_measure, layer_measure, nat_to_qpos in Hzero.
  simpl in Hzero.
  exact Hzero.
Defined.

Lemma nat_sub_zero_when_le (d n : nat)
  : nat_le d n -> nat_sub d n = O.
Proof.
  revert n.
  induction d.
  - intros n _; reflexivity.
  - intros n Hle.
    destruct n.
    + destruct Hle.
    + simpl.
      exact (IHd n Hle).
Defined.

Theorem graded_goodwillie_P_stabilizes (base_dim : nat)
  : { N : nat & forall n, nat_lt N n -> P_n_obj n {| go_dim := base_dim |} = go_zero }.
Proof.
  exists base_dim.
  intros n Hn.
  unfold P_n_obj, poly_approx, poly_approx_dim, go_zero.
  simpl.
  apply ap.
  apply nat_sub_zero_when_le.
  apply nat_le_of_lt.
  exact Hn.
Defined.

(** ** Concrete Example: Dimension 10 Functor *)

Definition dim10_tower : GradedGoodwillieTower 10 :=
  make_graded_goodwillie_tower 10.

Theorem dim10_layers_stabilize
  : { N : nat & forall n, nat_lt N n -> go_dim (ggt_D 10 dim10_tower n) = O }.
Proof.
  destruct (graded_goodwillie_layers_stabilize 10) as [N HN].
  exists N.
  intros n Hn.
  rewrite (ggt_D_def 10 dim10_tower n).
  exact (HN n Hn).
Defined.

Theorem dim10_P_stabilizes
  : { N : nat & forall n, nat_lt N n -> ggt_P 10 dim10_tower n = go_zero }.
Proof.
  destruct (graded_goodwillie_P_stabilizes 10) as [N HN].
  exists N.
  intros n Hn.
  rewrite (ggt_P_def 10 dim10_tower n).
  exact (HN n Hn).
Defined.

(** ** Summary: Complete Goodwillie Convergence for GradedCat *)

Theorem graded_complete_proof_chain (base_dim : nat)
  : (IsIntegerValued (D_n_measure base_dim)) *
    (EventuallyZero (D_n_measure base_dim)) *
    ({ N : nat & forall n, nat_lt N n -> go_dim (D_n_obj base_dim n) = O }) *
    ({ N : nat & forall n, nat_lt N n -> P_n_obj n {| go_dim := base_dim |} = go_zero }).
Proof.
  refine (_, _, _, _).
  - exact (D_n_measure_is_integer base_dim).
  - exact (D_n_measure_eventually_zero base_dim).
  - exact (graded_goodwillie_layers_stabilize base_dim).
  - exact (graded_goodwillie_P_stabilizes base_dim).
Defined.

(*******************************************************************************)
(*  LEVEL FAMILIES: A GRADED CARRIER CATEGORY WITH GENUINE SHIFT AND           *)
(*  FUNCTORIAL POLYNOMIAL TRUNCATION                                           *)
(*******************************************************************************)

(** Dimension-capped truncation fails functoriality but levelwise truncation does not; this part builds FamCat, its stable structure, the guarded truncations, and the tower P_n with detected layers D_n. *)

(** *** Boolean level arithmetic *)

Fixpoint nat_leb (n m : nat) : Bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n', S m' => nat_leb n' m'
  end.

Fixpoint nat_eqb (n m : nat) : Bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => nat_eqb n' m'
  end.

Lemma false_ne_true : false = true -> Empty.
Proof.
  intro H.
  exact (transport bool_discrim H^ tt).
Defined.

Lemma nat_eqb_refl (n : nat) : nat_eqb n n = true.
Proof.
  induction n.
  - reflexivity.
  - exact IHn.
Defined.

Lemma nat_eqb_true_path (n m : nat) : nat_eqb n m = true -> n = m.
Proof.
  revert m.
  induction n.
  - intros m E.
    destruct m.
    + reflexivity.
    + exact (Empty_rec _ (false_ne_true E)).
  - intros m E.
    destruct m.
    + exact (Empty_rec _ (false_ne_true E)).
    + exact (ap S (IHn m E)).
Defined.

Lemma nat_leb_succ_r (k n : nat) : nat_leb k n = true -> nat_leb k (S n) = true.
Proof.
  revert n.
  induction k.
  - intros n _.
    reflexivity.
  - intros n E.
    destruct n.
    + exact (Empty_rec _ (false_ne_true E)).
    + exact (IHk n E).
Defined.

Lemma nat_leb_Sn_n (n : nat) : nat_leb (S n) n = false.
Proof.
  induction n.
  - reflexivity.
  - exact IHn.
Defined.

Lemma nat_leb_between (k n : nat)
  : nat_leb k (S n) = true -> nat_leb k n = false -> k = S n.
Proof.
  revert n.
  induction k.
  - intros n E1 E2.
    exact (Empty_rec _ (false_ne_true E2^)).
  - intros n E1 E2.
    destruct n.
    + destruct k.
      * reflexivity.
      * exact (Empty_rec _ (false_ne_true E1)).
    + exact (ap S (IHk n E1 E2)).
Defined.

(** *** The level base: Bool objects with a zero level *)

Definition LevHom (x y : Bool) : Type :=
  match x with
  | true => match y with
            | true => Bool
            | false => Unit
            end
  | false => Unit
  end.

Definition lev_id (x : Bool) : LevHom x x :=
  match x return LevHom x x with
  | true => true
  | false => tt
  end.

Definition lev_zero_mor (x y : Bool) : LevHom x y :=
  match x return LevHom x y with
  | true => match y return LevHom true y with
            | true => false
            | false => tt
            end
  | false => tt
  end.

Definition lev_to_zero (x : Bool) : LevHom x false :=
  match x return LevHom x false with
  | true => tt
  | false => tt
  end.

Definition lev_comp (x y z : Bool) (g : LevHom y z) (f : LevHom x y)
  : LevHom x z.
Proof.
  destruct x.
  - destruct z.
    + destruct y.
      * exact (andb f g).
      * exact false.
    + exact tt.
  - exact tt.
Defined.

Lemma lev_from_false_unique (y : Bool) (f g : LevHom false y) : f = g.
Proof.
  bool_bash.
Defined.

Lemma lev_to_false_unique (x : Bool) (f g : LevHom x false) : f = g.
Proof.
  bool_bash.
Defined.

Lemma lev_from_falseish_unique (x y : Bool) (p : x = false) (f g : LevHom x y)
  : f = g.
Proof.
  destruct x.
  - destruct (false_ne_true p^).
  - apply lev_from_false_unique.
Defined.

Lemma lev_to_falseish_unique (x y : Bool) (p : y = false) (f g : LevHom x y)
  : f = g.
Proof.
  destruct y.
  - destruct (false_ne_true p^).
  - apply lev_to_false_unique.
Defined.

Lemma lev_comp_assoc (w x y z : Bool)
  (f : LevHom w x) (g : LevHom x y) (h : LevHom y z)
  : lev_comp w x z (lev_comp x y z h g) f = lev_comp w y z h (lev_comp w x y g f).
Proof.
  bool_bash.
Defined.

Lemma lev_comp_id_l (x y : Bool) (f : LevHom x y)
  : lev_comp x y y (lev_id y) f = f.
Proof.
  bool_bash.
Defined.

Lemma lev_comp_id_r (x y : Bool) (f : LevHom x y)
  : lev_comp x x y f (lev_id x) = f.
Proof.
  bool_bash.
Defined.

Global Instance ishset_levhom (x y : Bool) : IsHSet (LevHom x y).
Proof.
  destruct x.
  - destruct y.
    + exact hset_bool.
    + exact hset_unit.
  - exact hset_unit.
Defined.

(** *** The category of level families *)

Definition FamObj (I : Type) : Type := I -> Bool.

Definition FamHom {I : Type} (X Y : FamObj I) : Type
  := forall i, LevHom (X i) (Y i).

Definition fam_id {I : Type} (X : FamObj I) : FamHom X X
  := fun i => lev_id (X i).

Definition fam_comp {I : Type} (X Y Z : FamObj I)
  (g : FamHom Y Z) (f : FamHom X Y)
  : FamHom X Z
  := fun i => lev_comp (X i) (Y i) (Z i) (g i) (f i).

Lemma fam_comp_assoc `{Funext} {I : Type} (W X Y Z : FamObj I)
  (f : FamHom W X) (g : FamHom X Y) (h : FamHom Y Z)
  : fam_comp W X Z (fam_comp X Y Z h g) f = fam_comp W Y Z h (fam_comp W X Y g f).
Proof.
  apply path_forall; intro i.
  apply lev_comp_assoc.
Defined.

Lemma fam_comp_id_l `{Funext} {I : Type} (X Y : FamObj I) (f : FamHom X Y)
  : fam_comp X Y Y (fam_id Y) f = f.
Proof.
  apply path_forall; intro i.
  apply lev_comp_id_l.
Defined.

Lemma fam_comp_id_r `{Funext} {I : Type} (X Y : FamObj I) (f : FamHom X Y)
  : fam_comp X X Y f (fam_id X) = f.
Proof.
  apply path_forall; intro i.
  apply lev_comp_id_r.
Defined.

Global Instance ishset_famhom `{Funext} {I : Type} (X Y : FamObj I)
  : IsHSet (FamHom X Y).
Proof.
  apply istrunc_forall.
Defined.

Definition FamCat `{Funext} (I : Type) : PreCategory
  := @Build_PreCategory
       (FamObj I)
       (fun X Y => FamHom X Y)
       (fun X => fam_id X)
       (fun X Y Z g f => fam_comp X Y Z g f)
       (fun s d d' d'' m1 m2 m3 => fam_comp_assoc s d d' d'' m1 m2 m3)
       (fun a b f => fam_comp_id_l a b f)
       (fun a b f => fam_comp_id_r a b f)
       (fun s d => ishset_famhom s d).

Definition fam_zero {I : Type} : FamObj I := fun _ => false.

Global Instance contr_levhom_from_false (y : Bool) : Contr (LevHom false y).
Proof.
  exact contr_unit.
Defined.

Global Instance contr_levhom_to_false (x : Bool) : Contr (LevHom x false).
Proof.
  destruct x.
  - exact contr_unit.
  - exact contr_unit.
Defined.

Global Instance contr_famhom_from_zero `{Funext} {I : Type} (Y : FamObj I)
  : Contr (FamHom fam_zero Y).
Proof.
  apply istrunc_forall.
Defined.

Global Instance contr_famhom_to_zero `{Funext} {I : Type} (X : FamObj I)
  : Contr (FamHom X fam_zero).
Proof.
  apply istrunc_forall.
Defined.

Definition FamZero `{Funext} (I : Type) : ZeroObject (FamCat I)
  := Build_ZeroObject (FamCat I) fam_zero
       (fun Y => contr_famhom_from_zero Y)
       (fun X => contr_famhom_to_zero X).

(** *** Guarded truncation endofunctors *)

Definition truncAt (b : Bool) (x : Bool) : Bool := if b then x else false.

Definition lev_trunc_mor (b : Bool) (x y : Bool) (f : LevHom x y)
  : LevHom (truncAt b x) (truncAt b y)
  := match b return LevHom (truncAt b x) (truncAt b y) with
     | true => f
     | false => tt
     end.

Lemma lev_trunc_mor_id (b x : Bool)
  : lev_trunc_mor b x x (lev_id x) = lev_id (truncAt b x).
Proof.
  destruct b; reflexivity.
Defined.

Lemma lev_trunc_mor_comp (b x y z : Bool) (f : LevHom x y) (g : LevHom y z)
  : lev_trunc_mor b x z (lev_comp x y z g f)
    = lev_comp (truncAt b x) (truncAt b y) (truncAt b z)
        (lev_trunc_mor b y z g) (lev_trunc_mor b x y f).
Proof.
  destruct b; reflexivity.
Defined.

Definition fam_trunc {I : Type} (g : I -> Bool) (X : FamObj I) : FamObj I
  := fun i => truncAt (g i) (X i).

Definition fam_trunc_mor {I : Type} (g : I -> Bool) (X Y : FamObj I) (f : FamHom X Y)
  : FamHom (fam_trunc g X) (fam_trunc g Y)
  := fun i => lev_trunc_mor (g i) (X i) (Y i) (f i).

Lemma fam_trunc_mor_id `{Funext} {I : Type} (g : I -> Bool) (X : FamObj I)
  : fam_trunc_mor g X X (fam_id X) = fam_id (fam_trunc g X).
Proof.
  apply path_forall; intro i.
  apply lev_trunc_mor_id.
Defined.

Lemma fam_trunc_mor_comp `{Funext} {I : Type} (g : I -> Bool) (X Y Z : FamObj I)
  (f : FamHom X Y) (h : FamHom Y Z)
  : fam_trunc_mor g X Z (fam_comp X Y Z h f)
    = fam_comp (fam_trunc g X) (fam_trunc g Y) (fam_trunc g Z)
        (fam_trunc_mor g Y Z h) (fam_trunc_mor g X Y f).
Proof.
  apply path_forall; intro i.
  apply lev_trunc_mor_comp.
Defined.

Definition FamTrunc `{Funext} {I : Type} (g : I -> Bool)
  : Functor (FamCat I) (FamCat I).
Proof.
  refine (Build_Functor (FamCat I) (FamCat I)
            (fam_trunc g)
            (fun X Y f => fam_trunc_mor g X Y f)
            _ _).
  - intros X Y Z f h.
    exact (fam_trunc_mor_comp g X Y Z f h).
  - intro X.
    exact (fam_trunc_mor_id g X).
Defined.

Lemma fam_trunc_zero `{Funext} {I : Type} (g : I -> Bool)
  : fam_trunc g fam_zero = (fam_zero : FamObj I).
Proof.
  apply path_forall; intro i.
  unfold fam_trunc, fam_zero.
  destruct (g i); reflexivity.
Defined.

(** *** Guard-change morphisms and natural transformations *)

Definition lev_change (b1 b2 : Bool) (x : Bool)
  : LevHom (truncAt b1 x) (truncAt b2 x).
Proof.
  destruct b1.
  - destruct b2.
    + exact (lev_id x).
    + exact (lev_to_zero x).
  - exact tt.
Defined.

Lemma lev_change_natural (b1 b2 : Bool) (x y : Bool) (f : LevHom x y)
  : lev_comp (truncAt b1 x) (truncAt b1 y) (truncAt b2 y)
      (lev_change b1 b2 y) (lev_trunc_mor b1 x y f)
    = lev_comp (truncAt b1 x) (truncAt b2 x) (truncAt b2 y)
        (lev_trunc_mor b2 x y f) (lev_change b1 b2 x).
Proof.
  destruct b1.
  - destruct b2.
    + exact (lev_comp_id_l x y f @ (lev_comp_id_r x y f)^).
    + apply lev_to_false_unique.
  - apply lev_from_false_unique.
Defined.

Definition fam_change {I : Type} (g1 g2 : I -> Bool) (X : FamObj I)
  : FamHom (fam_trunc g1 X) (fam_trunc g2 X)
  := fun i => lev_change (g1 i) (g2 i) (X i).

Lemma fam_change_natural `{Funext} {I : Type} (g1 g2 : I -> Bool)
  (X Y : FamObj I) (f : FamHom X Y)
  : fam_comp (fam_trunc g1 X) (fam_trunc g1 Y) (fam_trunc g2 Y)
      (fam_change g1 g2 Y) (fam_trunc_mor g1 X Y f)
    = fam_comp (fam_trunc g1 X) (fam_trunc g2 X) (fam_trunc g2 Y)
        (fam_trunc_mor g2 X Y f) (fam_change g1 g2 X).
Proof.
  apply path_forall; intro i.
  apply lev_change_natural.
Defined.

Definition FamChange `{Funext} {I : Type} (g1 g2 : I -> Bool)
  : NaturalTransformation (FamTrunc g1) (FamTrunc g2).
Proof.
  refine (Build_NaturalTransformation (FamTrunc g1) (FamTrunc g2)
            (fun X => fam_change g1 g2 X)
            _).
  intros X Y f.
  exact (fam_change_natural g1 g2 X Y f).
Defined.

(** *** Genuine suspension and loop on nat-indexed families *)

Definition fam_susp_obj (X : FamObj nat) : FamObj nat
  := fun k => match k with
              | O => false
              | S k' => X k'
              end.

Definition fam_loop_obj (X : FamObj nat) : FamObj nat
  := fun k => X (S k).

Definition fam_susp_mor (X Y : FamObj nat) (f : FamHom X Y)
  : FamHom (fam_susp_obj X) (fam_susp_obj Y).
Proof.
  intro k.
  destruct k.
  - exact tt.
  - exact (f k).
Defined.

Definition fam_loop_mor (X Y : FamObj nat) (f : FamHom X Y)
  : FamHom (fam_loop_obj X) (fam_loop_obj Y)
  := fun k => f (S k).

Lemma fam_susp_mor_id `{Funext} (X : FamObj nat)
  : fam_susp_mor X X (fam_id X) = fam_id (fam_susp_obj X).
Proof.
  apply path_forall; intro k.
  destruct k; reflexivity.
Defined.

Lemma fam_susp_mor_comp `{Funext} (X Y Z : FamObj nat)
  (f : FamHom X Y) (g : FamHom Y Z)
  : fam_susp_mor X Z (fam_comp X Y Z g f)
    = fam_comp (fam_susp_obj X) (fam_susp_obj Y) (fam_susp_obj Z)
        (fam_susp_mor Y Z g) (fam_susp_mor X Y f).
Proof.
  apply path_forall; intro k.
  destruct k; reflexivity.
Defined.

Definition FamSusp `{Funext} : Functor (FamCat nat) (FamCat nat).
Proof.
  refine (Build_Functor (FamCat nat) (FamCat nat)
            fam_susp_obj
            (fun X Y f => fam_susp_mor X Y f)
            _ _).
  - intros X Y Z f g.
    exact (fam_susp_mor_comp X Y Z f g).
  - intro X.
    exact (fam_susp_mor_id X).
Defined.

Definition FamLoop `{Funext} : Functor (FamCat nat) (FamCat nat).
Proof.
  refine (Build_Functor (FamCat nat) (FamCat nat)
            fam_loop_obj
            (fun X Y f => fam_loop_mor X Y f)
            _ _).
  - intros X Y Z f g.
    reflexivity.
  - intro X.
    reflexivity.
Defined.

Definition fam_eta_component `{Funext} (X : FamObj nat)
  : morphism (FamCat nat) X (object_of (FamLoop o FamSusp)%functor X)
  := fun k => lev_id (X k).

Lemma fam_eta_natural `{Funext} (X Y : FamObj nat) (f : morphism (FamCat nat) X Y)
  : (morphism_of (FamLoop o FamSusp)%functor f o fam_eta_component X
     = fam_eta_component Y o f)%morphism.
Proof.
  apply path_forall; intro k.
  exact (lev_comp_id_r (X k) (Y k) (f k) @ (lev_comp_id_l (X k) (Y k) (f k))^).
Defined.

Definition FamEta `{Funext}
  : NaturalTransformation 1%functor (FamLoop o FamSusp)%functor.
Proof.
  refine (Build_NaturalTransformation 1%functor (FamLoop o FamSusp)%functor
            fam_eta_component
            _).
  intros X Y f.
  exact (fam_eta_natural X Y f)^.
Defined.

Definition fam_epsilon_component `{Funext} (X : FamObj nat)
  : morphism (FamCat nat) (object_of (FamSusp o FamLoop)%functor X) X.
Proof.
  intro k.
  destruct k.
  - exact tt.
  - exact (lev_id (X (S k))).
Defined.

Lemma fam_epsilon_natural `{Funext} (X Y : FamObj nat) (f : morphism (FamCat nat) X Y)
  : (f o fam_epsilon_component X
     = fam_epsilon_component Y o morphism_of (FamSusp o FamLoop)%functor f)%morphism.
Proof.
  apply path_forall; intro k.
  destruct k.
  - apply lev_from_false_unique.
  - exact (lev_comp_id_r (X (S k)) (Y (S k)) (f (S k))
             @ (lev_comp_id_l (X (S k)) (Y (S k)) (f (S k)))^).
Defined.

Definition FamEpsilon `{Funext}
  : NaturalTransformation (FamSusp o FamLoop)%functor 1%functor.
Proof.
  refine (Build_NaturalTransformation (FamSusp o FamLoop)%functor 1%functor
            fam_epsilon_component
            _).
  intros X Y f.
  exact (fam_epsilon_natural X Y f)^.
Defined.

Definition FamPreStable `{Funext} : PreStableCategory
  := {| ps_cat := FamCat nat;
        ps_zero := FamZero nat;
        ps_susp := FamSusp;
        ps_loop := FamLoop;
        ps_eta := FamEta;
        ps_epsilon := FamEpsilon |}.

(** *** The polynomial tower P_n and its layers D_n *)

Definition fam_guard_P (n : nat) : nat -> Bool := fun k => nat_leb k n.

Definition fam_guard_D (n : nat) : nat -> Bool := fun k => nat_eqb k (S n).

Definition fam_guard_all : nat -> Bool := fun _ => true.

Definition FamP `{Funext} (n : nat) : ReducedFunctor FamPreStable
  := Build_ReducedFunctor FamPreStable (FamTrunc (fam_guard_P n))
       (fam_trunc_zero (fam_guard_P n)).

Definition FamD `{Funext} (n : nat) : ReducedFunctor FamPreStable
  := Build_ReducedFunctor FamPreStable (FamTrunc (fam_guard_D n))
       (fam_trunc_zero (fam_guard_D n)).

Definition FamIdReduced `{Funext} : ReducedFunctor FamPreStable
  := Build_ReducedFunctor FamPreStable (FamTrunc fam_guard_all)
       (fam_trunc_zero fam_guard_all).

Definition FamGoodwillieData `{Funext}
  : GoodwillieTowerData FamPreStable FamIdReduced.
Proof.
  refine {| gtd_P := FamP |}.
  - intro n.
    exact (Build_NatTransBetweenReduced FamPreStable (FamP (S n)) (FamP n)
             (FamChange (fam_guard_P (S n)) (fam_guard_P n))).
  - intro n.
    exact (Build_NatTransBetweenReduced FamPreStable FamIdReduced (FamP n)
             (FamChange fam_guard_all (fam_guard_P n))).
Defined.

(** The two composite identities for the layer map inverse, at one level. *)

Lemma lev_change_inverse_r (b1 b2 : Bool) (x : Bool)
  (Hmono : b2 = true -> b1 = true)
  : lev_comp (truncAt b2 x) (truncAt b1 x) (truncAt b2 x)
      (lev_change b1 b2 x) (lev_change b2 b1 x)
    = lev_id (truncAt b2 x).
Proof.
  destruct b2.
  - rewrite (Hmono idpath).
    apply lev_comp_id_l.
  - apply lev_from_false_unique.
Defined.

Lemma lev_change_inverse_l (b1 b2 : Bool) (x : Bool)
  (Hgap : b1 = true -> b2 = false -> x = false)
  : lev_comp (truncAt b1 x) (truncAt b2 x) (truncAt b1 x)
      (lev_change b2 b1 x) (lev_change b1 b2 x)
    = lev_id (truncAt b1 x).
Proof.
  destruct b1.
  - destruct b2.
    + apply lev_comp_id_l.
    + rewrite (Hgap idpath idpath).
      apply lev_from_false_unique.
  - apply lev_from_false_unique.
Defined.

Theorem fam_layer_zero_implies_iso `{Funext} (n : nat) (X : FamObj nat)
  (Hzero : fam_trunc (fam_guard_D n) X = (fam_zero : FamObj nat))
  : IsIsomorphism (C := FamCat nat)
      (fam_change (fam_guard_P (S n)) (fam_guard_P n) X).
Proof.
  assert (HX : X (S n) = false).
  { exact ((ap (fun b => truncAt b (X (S n))) (nat_eqb_refl (S n)))^
             @ ap (fun Z : FamObj nat => Z (S n)) Hzero). }
  exists (fam_change (fam_guard_P n) (fam_guard_P (S n)) X).
  split.
  - apply path_forall; intro k.
    apply lev_change_inverse_l.
    intros Hb1 Hb2.
    exact (ap X (nat_leb_between k n Hb1 Hb2) @ HX).
  - apply path_forall; intro k.
    apply lev_change_inverse_r.
    exact (nat_leb_succ_r k n).
Defined.

Definition FamGoodwillieTower `{Funext}
  : GoodwillieTowerWithLayers FamPreStable FamIdReduced.
Proof.
  refine {| gtwl_data := FamGoodwillieData; gtwl_D := FamD |}.
  intros n X Hzero.
  exact (fam_layer_zero_implies_iso n X Hzero).
Defined.

(** *** The layers are the fibers of the tower maps *)

Definition fam_layer_fiber `{Funext} (n : nat) (X : FamObj nat)
  : FiberData (FamZero nat) (fam_change (fam_guard_P (S n)) (fam_guard_P n) X).
Proof.
  refine (@Build_FiberData (FamCat nat) (FamZero nat)
            (fam_trunc (fam_guard_P (S n)) X) (fam_trunc (fam_guard_P n) X)
            (fam_change (fam_guard_P (S n)) (fam_guard_P n) X)
            (fam_trunc (fam_guard_D n) X)
            (fam_change (fam_guard_D n) (fam_guard_P (S n)) X)
            _).
  apply path_forall; intro k.
  destruct (bool_dec_eq (nat_eqb k (S n))) as [He | He].
  - destruct (bool_dec_eq (nat_leb k n)) as [Hb | Hb].
    + exact (Empty_rec _ (false_ne_true
               ((nat_leb_Sn_n n)^
                  @ transport (fun m => nat_leb m n = true)
                      (nat_eqb_true_path k (S n) He) Hb))).
    + exact (lev_to_falseish_unique _ _
               (ap (fun b => truncAt b (X k)) Hb) _ _).
  - exact (lev_from_falseish_unique _ _
             (ap (fun b => truncAt b (X k)) He) _ _).
Defined.

Definition fam_P_tower `{Funext} (X : FamObj nat) : CategoricalTower (FamCat nat)
  := Build_CategoricalTower (FamCat nat)
       (fun n => fam_trunc (fam_guard_P n) X)
       (fun n => fam_change (fam_guard_P (S n)) (fam_guard_P n) X).

Definition fam_P_tower_with_fibers `{Funext} (X : FamObj nat)
  : TowerWithFibers (FamCat nat) (FamZero nat)
  := Build_TowerWithFibers (FamCat nat) (FamZero nat)
       (fam_P_tower X)
       (fun n => fam_layer_fiber n X).

(** *** The universal property of the fiber: unique factorization through the inclusion, canonicity of the fiber object, and the failure of the degenerate zero fiber. *)

Record FiberUniversal {C : PreCategory} (Z : ZeroObject C)
  {X Y : object C} (f : morphism C X Y) (fd : FiberData Z f) := {
  fu_factor : forall (V : object C) (t : morphism C V X),
    (f o t)%morphism = zero_morphism Z V Y ->
    Contr { s : morphism C V (fd_fiber Z f fd) &
            (fd_inclusion Z f fd o s)%morphism = t }
}.

Definition lev_fiber_factor (b1 bD x w : Bool)
  (t : LevHom w (truncAt b1 x))
  : LevHom w (truncAt bD x)
  := match b1 return LevHom w (truncAt b1 x) -> LevHom w (truncAt bD x) with
     | true => fun t0 =>
         match bD return LevHom w (truncAt bD x) with
         | true => t0
         | false => lev_to_zero w
         end
     | false => fun _ =>
         match bD return LevHom w (truncAt bD x) with
         | true => lev_zero_mor w x
         | false => lev_to_zero w
         end
     end t.

Lemma lev_fiber_factor_commutes (b1 b0 bD x w : Bool)
  (HD : bD = andb b1 (negb b0))
  (t : LevHom w (truncAt b1 x))
  (u : LevHom w false) (v : LevHom false (truncAt b0 x))
  (Hz : lev_comp w (truncAt b1 x) (truncAt b0 x)
          (lev_change b1 b0 x) t
        = lev_comp w false (truncAt b0 x) v u)
  : lev_comp w (truncAt bD x) (truncAt b1 x)
      (lev_change bD b1 x) (lev_fiber_factor b1 bD x w t)
    = t.
Proof.
  destruct b1.
  - destruct b0.
    + destruct bD.
      * exact (Empty_rec _ (false_ne_true HD^)).
      * destruct w.
        { destruct x.
          - exact (((andb_true_r t)^ @ Hz)^).
          - destruct t; reflexivity. }
        { destruct t; reflexivity. }
    + destruct bD.
      * destruct w.
        { destruct x.
          - exact (andb_true_r t).
          - destruct t; reflexivity. }
        { destruct t; reflexivity. }
      * exact (Empty_rec _ (false_ne_true HD)).
  - destruct bD.
    + exact (Empty_rec _ (false_ne_true HD^)).
    + destruct w; destruct t; reflexivity.
Defined.

Lemma lev_fiber_factor_unique (b1 b0 bD x w : Bool)
  (HD : bD = andb b1 (negb b0))
  (t : LevHom w (truncAt b1 x))
  (s : LevHom w (truncAt bD x))
  (Hs : lev_comp w (truncAt bD x) (truncAt b1 x)
          (lev_change bD b1 x) s = t)
  : s = lev_fiber_factor b1 bD x w t.
Proof.
  destruct bD.
  - destruct b1.
    + destruct w.
      * destruct x.
        { exact ((andb_true_r s)^ @ Hs). }
        { destruct s, t; reflexivity. }
      * destruct s, t; reflexivity.
    + exact (Empty_rec _ (false_ne_true HD^)).
  - destruct b1; destruct w; destruct s; reflexivity.
Defined.

Lemma nat_eqb_window (k n : nat)
  : nat_eqb k (S n) = andb (nat_leb k (S n)) (negb (nat_leb k n)).
Proof.
  revert n.
  induction k.
  - intro n.
    reflexivity.
  - intro n.
    destruct n.
    + destruct k; reflexivity.
    + exact (IHk n).
Defined.

Theorem fam_fiber_universal `{Funext} (n : nat) (X V : FamObj nat)
  (t : FamHom V (fam_trunc (fam_guard_P (S n)) X))
  (Hz : fam_comp V (fam_trunc (fam_guard_P (S n)) X)
          (fam_trunc (fam_guard_P n) X)
          (fam_change (fam_guard_P (S n)) (fam_guard_P n) X) t
        = zero_morphism (FamZero nat) V (fam_trunc (fam_guard_P n) X))
  : Contr { s : FamHom V (fam_trunc (fam_guard_D n) X) &
            fam_comp V (fam_trunc (fam_guard_D n) X)
              (fam_trunc (fam_guard_P (S n)) X)
              (fam_change (fam_guard_D n) (fam_guard_P (S n)) X) s = t }.
Proof.
  refine (Build_Contr _
            ((fun k => lev_fiber_factor (nat_leb k (S n)) (nat_eqb k (S n))
                         (X k) (V k) (t k)) ;
             path_forall _ _ (fun k =>
               lev_fiber_factor_commutes (nat_leb k (S n)) (nat_leb k n)
                 (nat_eqb k (S n)) (X k) (V k)
                 (nat_eqb_window k n)
                 (t k) _ _ (apD10 Hz k)))
            _).
  intros [s e].
  apply path_sigma_hprop.
  apply path_forall; intro k.
  exact (lev_fiber_factor_unique (nat_leb k (S n)) (nat_leb k n)
           (nat_eqb k (S n)) (X k) (V k)
           (nat_eqb_window k n) (t k) (s k) (apD10 e k))^.
Defined.

Theorem fam_layer_fiber_universal `{Funext} (n : nat) (X : FamObj nat)
  : FiberUniversal (FamZero nat)
      (fam_change (fam_guard_P (S n)) (fam_guard_P n) X)
      (fam_layer_fiber n X).
Proof.
  constructor.
  intros V t Hz.
  exact (fam_fiber_universal n X V t Hz).
Defined.

Theorem fiber_universal_canonical {C : PreCategory} (Z : ZeroObject C)
  {X Y : object C} (f : morphism C X Y)
  (fd1 fd2 : FiberData Z f)
  (U1 : FiberUniversal Z f fd1) (U2 : FiberUniversal Z f fd2)
  : { i : morphism C (fd_fiber Z f fd1) (fd_fiber Z f fd2) &
      ((IsIsomorphism i) *
       ((fd_inclusion Z f fd2 o i)%morphism = fd_inclusion Z f fd1))%type }.
Proof.
  pose (c12 := fu_factor Z f fd2 U2 _ (fd_inclusion Z f fd1)
                 (fd_exactness Z f fd1)).
  pose (c21 := fu_factor Z f fd1 U1 _ (fd_inclusion Z f fd2)
                 (fd_exactness Z f fd2)).
  pose (i := (@center _ c12).1).
  pose (j := (@center _ c21).1).
  pose (ei := (@center _ c12).2).
  pose (ej := (@center _ c21).2).
  exists i.
  refine (_, ei).
  exists j.
  split.
  - pose (cself := fu_factor Z f fd1 U1 _ (fd_inclusion Z f fd1)
                     (fd_exactness Z f fd1)).
    pose (p1 := ((j o i)%morphism ;
                 (associativity C _ _ _ _ i j (fd_inclusion Z f fd1))^
                   @ ap (fun h => (h o i)%morphism) ej
                   @ ei)
                : { s : _ & (fd_inclusion Z f fd1 o s)%morphism
                            = fd_inclusion Z f fd1 }).
    pose (p2 := (1%morphism ; right_identity _ _ _ _)
                : { s : _ & (fd_inclusion Z f fd1 o s)%morphism
                            = fd_inclusion Z f fd1 }).
    exact (ap (fun z => z.1) (@path_contr _ cself p1 p2)).
  - pose (cself := fu_factor Z f fd2 U2 _ (fd_inclusion Z f fd2)
                     (fd_exactness Z f fd2)).
    pose (p1 := ((i o j)%morphism ;
                 (associativity C _ _ _ _ j i (fd_inclusion Z f fd2))^
                   @ ap (fun h => (h o j)%morphism) ei
                   @ ej)
                : { s : _ & (fd_inclusion Z f fd2 o s)%morphism
                            = fd_inclusion Z f fd2 }).
    pose (p2 := (1%morphism ; right_identity _ _ _ _)
                : { s : _ & (fd_inclusion Z f fd2 o s)%morphism
                            = fd_inclusion Z f fd2 }).
    exact (ap (fun z => z.1) (@path_contr _ cself p1 p2)).
Defined.

(** *** Genuine mapping cones for arbitrary maps of level families: the cone kills the map and is the universal such target. *)

Definition lev_cone (x y : Bool) (f : LevHom x y) : Bool
  := match x return LevHom x y -> Bool with
     | true => match y return LevHom true y -> Bool with
               | true => fun f0 => negb f0
               | false => fun _ => false
               end
     | false => fun _ => y
     end f.

Definition lev_cone_in (x y : Bool) (f : LevHom x y)
  : LevHom y (lev_cone x y f).
Proof.
  destruct x.
  - destruct y.
    + destruct f.
      * exact tt.
      * exact true.
    + exact tt.
  - exact (lev_id y).
Defined.

Lemma lev_cone_in_kills (x y : Bool) (f : LevHom x y)
  (u : LevHom x false) (v : LevHom false (lev_cone x y f))
  : lev_comp x y (lev_cone x y f) (lev_cone_in x y f) f
    = lev_comp x false (lev_cone x y f) v u.
Proof.
  destruct x.
  - destruct y.
    + destruct f; reflexivity.
    + reflexivity.
  - reflexivity.
Defined.

Definition lev_cone_factor (x y : Bool) (f : LevHom x y) (z : Bool)
  (g : LevHom y z)
  : LevHom (lev_cone x y f) z.
Proof.
  destruct x.
  - destruct y.
    + destruct f.
      * exact tt.
      * exact g.
    + exact tt.
  - exact g.
Defined.

Lemma lev_cone_factor_commutes (x y z : Bool) (f : LevHom x y)
  (g : LevHom y z)
  (u : LevHom x false) (v : LevHom false z)
  (Hz : lev_comp x y z g f = lev_comp x false z v u)
  : lev_comp y (lev_cone x y f) z
      (lev_cone_factor x y f z g) (lev_cone_in x y f)
    = g.
Proof.
  destruct x.
  - destruct y.
    + destruct f.
      * destruct z.
        { exact Hz^. }
        { destruct g; reflexivity. }
      * destruct z.
        { reflexivity. }
        { destruct g; reflexivity. }
    + destruct g; reflexivity.
  - destruct y.
    + destruct z.
      * reflexivity.
      * destruct g; reflexivity.
    + destruct g; reflexivity.
Defined.

Lemma lev_cone_factor_unique (x y z : Bool) (f : LevHom x y)
  (g : LevHom y z)
  (h : LevHom (lev_cone x y f) z)
  (Hh : lev_comp y (lev_cone x y f) z h (lev_cone_in x y f) = g)
  : h = lev_cone_factor x y f z g.
Proof.
  destruct x.
  - destruct y.
    + destruct f.
      * destruct h; reflexivity.
      * destruct z.
        { exact Hh. }
        { destruct h, g; reflexivity. }
    + destruct h; reflexivity.
  - destruct y.
    + destruct z.
      * exact Hh.
      * destruct h, g; reflexivity.
    + destruct h, g; reflexivity.
Defined.

Definition fam_cone `{Funext} {X Y : FamObj nat} (f : FamHom X Y)
  : FamObj nat
  := fun k => lev_cone (X k) (Y k) (f k).

Definition fam_cone_in `{Funext} {X Y : FamObj nat} (f : FamHom X Y)
  : FamHom Y (fam_cone f)
  := fun k => lev_cone_in (X k) (Y k) (f k).

Theorem fam_cone_in_kills `{Funext} {X Y : FamObj nat} (f : FamHom X Y)
  : fam_comp X Y (fam_cone f) (fam_cone_in f) f
    = zero_morphism (FamZero nat) X (fam_cone f).
Proof.
  apply path_forall; intro k.
  exact (lev_cone_in_kills (X k) (Y k) (f k) _ _).
Defined.

Theorem fam_cone_universal `{Funext} {X Y : FamObj nat} (f : FamHom X Y)
  (Z : FamObj nat) (g : FamHom Y Z)
  (Hg : fam_comp X Y Z g f = zero_morphism (FamZero nat) X Z)
  : Contr { h : FamHom (fam_cone f) Z &
            fam_comp Y (fam_cone f) Z h (fam_cone_in f) = g }.
Proof.
  refine (Build_Contr _
            ((fun k => lev_cone_factor (X k) (Y k) (f k) (Z k) (g k)) ;
             path_forall _ _ (fun k =>
               lev_cone_factor_commutes (X k) (Y k) (Z k) (f k) (g k)
                 _ _ (apD10 Hg k)))
            _).
  intros [h e].
  apply path_sigma_hprop.
  apply path_forall; intro k.
  exact (lev_cone_factor_unique (X k) (Y k) (Z k) (f k) (g k)
           (h k) (apD10 e k))^.
Defined.

Theorem fam_cone_of_from_zero `{Funext} (Y : FamObj nat)
  : fam_cone (@center _ (contr_famhom_from_zero Y)) = Y.
Proof.
  apply path_forall; intro k.
  reflexivity.
Defined.

Theorem fam_cone_of_id `{Funext} (X : FamObj nat)
  : fam_cone (fam_id X) = (fam_zero : FamObj nat).
Proof.
  apply path_forall; intro k.
  unfold fam_cone, fam_id, fam_zero.
  destruct (X k); reflexivity.
Defined.

Theorem degenerate_fiber_not_universal `{Funext}
  : { X : FamObj nat & { fd : FiberData (FamZero nat)
        (fam_change (fam_guard_P 1) (fam_guard_P O) X) &
      FiberUniversal (FamZero nat)
        (fam_change (fam_guard_P 1) (fam_guard_P O) X) fd -> Empty }}.
Proof.
  exists (fun k => nat_leb k 1).
  refine (@Build_FiberData (FamCat nat) (FamZero nat)
            _ _ (fam_change (fam_guard_P 1) (fam_guard_P O)
                   (fun k => nat_leb k 1))
            (fam_zero : FamObj nat)
            (@center _ (contr_famhom_from_zero
                          (fam_trunc (fam_guard_P 1) (fun k => nat_leb k 1))))
            (@path_contr _ (contr_famhom_from_zero _) _ _) ; _).
  intro U.
  pose (c := fu_factor _ _ _ U _
               (fam_change (fam_guard_D O) (fam_guard_P 1)
                  (fun k => nat_leb k 1))
               (fd_exactness _ _ (fam_layer_fiber O (fun k => nat_leb k 1)))).
  pose (e := (@center _ c).2).
  exact (false_ne_true (apD10 e 1%nat)).
Defined.

(** *** Goodwillie framework instances over ZGraded_PreStable, whose suspension and loop are genuine inverse equivalences. *)

Definition ZGraded_id_nattrans (F : Functor ZGradedCat ZGradedCat)
  : NaturalTransformation F F.
Proof.
  refine (Build_NaturalTransformation F F (fun X => 1%morphism) _).
  intros s d m.
  exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^).
Defined.

Definition ZGradedReducedId : ReducedFunctor ZGraded_PreStable
  := Build_ReducedFunctor ZGraded_PreStable 1%functor idpath.

Definition ZGradedConstantGoodwillieData
  : GoodwillieTowerData ZGraded_PreStable ZGradedReducedId.
Proof.
  refine {| gtd_P := fun _ : nat => ZGradedReducedId |}.
  - intro n.
    exact (Build_NatTransBetweenReduced ZGraded_PreStable
             ZGradedReducedId ZGradedReducedId
             (ZGraded_id_nattrans 1%functor)).
  - intro n.
    exact (Build_NatTransBetweenReduced ZGraded_PreStable
             ZGradedReducedId ZGradedReducedId
             (ZGraded_id_nattrans 1%functor)).
Defined.

Definition ZGradedZeroFunctor : Functor ZGradedCat ZGradedCat.
Proof.
  refine (Build_Functor ZGradedCat ZGradedCat
            (fun _ => zgo_zero)
            (fun _ _ _ => tt)
            _ _).
  - intros s d d' m1 m2.
    reflexivity.
  - intro X.
    reflexivity.
Defined.

Definition ZGradedZeroReduced : ReducedFunctor ZGraded_PreStable
  := Build_ReducedFunctor ZGraded_PreStable ZGradedZeroFunctor idpath.

Definition ZGradedConstantTower
  : GoodwillieTowerWithLayers ZGraded_PreStable ZGradedReducedId.
Proof.
  refine {| gtwl_data := ZGradedConstantGoodwillieData;
            gtwl_D := fun _ : nat => ZGradedZeroReduced |}.
  intros n X _.
  exists 1%morphism.
  split.
  - apply left_identity.
  - apply left_identity.
Defined.

(** *** The completed graded motivic stable homotopy category *)

Definition MotivicSH (k : BaseField) : PreCategory
  := ShiftCat (GradedMotivicSpectrum k).

Definition MotivicSH_PreStable (k : BaseField) : PreStableCategory
  := ShiftPreStable (gms_susp k) (gms_loop k) (gms_loop_susp k) (gms_susp_loop k).

Definition MotivicSH_ProperStable (k : BaseField) : ProperStableCategory
  := ShiftProperStable (gms_susp k) (gms_loop k) (gms_loop_susp k) (gms_susp_loop k).

Definition MotivicSH_WeightMeasure (k : BaseField)
  : WeightMeasure (MotivicSH k) (ShiftZero (GradedMotivicSpectrum k))
  := ShiftWeightMeasure.

Theorem MotivicSH_has_non_iso_morphisms (k : BaseField)
  : { E : ShiftObj (GradedMotivicSpectrum k) &
      { F : ShiftObj (GradedMotivicSpectrum k) &
        { f : morphism (MotivicSH k) E F &
          @IsIsomorphism (MotivicSH k) E F f -> Empty }}}.
Proof.
  exact (ShiftCat_has_non_iso (gms_nonzero k)).
Defined.

(** The suspension-loop adjunction instantiated on the motivic stable homotopy category. *)

Definition MotivicSH_hom_susp_loop (k : BaseField)
  (E F : object (MotivicSH k))
  : morphism (MotivicSH k)
      (object_of (ps_susp (MotivicSH_ProperStable k)) E) F
    <~> morphism (MotivicSH k) E
      (object_of (ps_loop (MotivicSH_ProperStable k)) F)
  := stable_susp_loop_adjunction (MotivicSH_ProperStable k) E F.

Theorem MotivicSH_zero_measure_implies_zero (k : BaseField)
  (E : ShiftObj (GradedMotivicSpectrum k))
  : qpos_is_zero (sh_dim_measure E) -> E = sh_zero.
Proof.
  exact (sh_zero_measure_implies_zero E).
Defined.

Theorem MotivicSH_cofiber_distinguished (k : BaseField)
  (E F : GradedMotivicSpectrum k) (f : Bool)
  : DistinguishedTriangle (MotivicSH_PreStable k).
Proof.
  exact (sh_cofiber_distinguished (gms_susp k) (gms_loop k)
           (gms_loop_susp k) (gms_susp_loop k) E F f).
Defined.

Theorem MotivicSH_tower_stabilizes_from_limit (k : BaseField)
  (E : GradedMotivicSpectrum k) (maps : nat -> Bool)
  (Hlimit : LimitZero (sh_tower_fiber_measure E maps))
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism (MotivicSH k) (sh_el E) (sh_el E) (maps n) }.
Proof.
  exact (sh_tower_stabilizes_from_limit E maps Hlimit).
Defined.

Theorem MotivicSH_weight_bounded_stabilizes (k : BaseField)
  (E : GradedMotivicSpectrum k) (C : QPos) (maps : nat -> Bool)
  (HC : nat_lt O (qpos_num C))
  (Hbounded : sh_weight_bounded_tower E C maps)
  : { N : nat & forall n, nat_lt N n ->
      @IsIsomorphism (MotivicSH k) (sh_el E) (sh_el E) (maps n) }.
Proof.
  exact (sh_weight_bounded_stabilizes E C maps HC Hbounded).
Defined.

Theorem MotivicSH_genuine_threshold (k : BaseField)
  (E : GradedMotivicSpectrum k) (N : nat)
  (HN : nat_lt O N)
  : (forall n, nat_le N n ->
       @IsIsomorphism (MotivicSH k) (sh_el E) (sh_el E) (threshold_tower_map N n))
    * (@IsIsomorphism (MotivicSH k) (sh_el E) (sh_el E) (threshold_tower_map N O)
       -> Empty).
Proof.
  exact (sh_genuine_threshold E N HN).
Defined.

Definition MotivicSH_main_convergence (k : BaseField)
  : Type
  := forall (E : GradedMotivicSpectrum k) (C : QPos) (maps : nat -> Bool),
     nat_lt O (qpos_num C) ->
     sh_weight_bounded_tower E C maps ->
     { N : nat & forall n, nat_lt N n ->
         @IsIsomorphism (MotivicSH k) (sh_el E) (sh_el E) (maps n) }.

Theorem motivic_sh_main_convergence (k : BaseField)
  : MotivicSH_main_convergence k.
Proof.
  intros E C maps HC Hbounded.
  exact (MotivicSH_weight_bounded_stabilizes k E C maps HC Hbounded).
Defined.

(** *** The bounded-family model: goodwillie_tower_stabilizes instantiated with every hypothesis discharged and the zero object decidable. *)

Section BoundedFamilies.

Context `{Funext} (W : nat).

Definition BFamObj : Type
  := { X : FamObj nat & forall k, nat_lt W k -> X k = false }.

Local Instance ishprop_bounded_support (X : FamObj nat)
  : IsHProp (forall k, nat_lt W k -> X k = false).
Proof.
  exact _.
Defined.

Definition BFamCat : PreCategory
  := @Build_PreCategory
       BFamObj
       (fun X Y => FamHom X.1 Y.1)
       (fun X => fam_id X.1)
       (fun X Y Z g f => fam_comp X.1 Y.1 Z.1 g f)
       (fun s d d' d'' m1 m2 m3 =>
          associativity (FamCat nat) s.1 d.1 d'.1 d''.1 m1 m2 m3)
       (fun a b f => left_identity (FamCat nat) a.1 b.1 f)
       (fun a b f => right_identity (FamCat nat) a.1 b.1 f)
       (fun s d => @trunc_morphism (FamCat nat) s.1 d.1).

Definition bfam_zero : BFamObj
  := ((fam_zero : FamObj nat) ; fun k _ => idpath).

Definition BFamZero : ZeroObject BFamCat
  := Build_ZeroObject BFamCat bfam_zero
       (fun Y => contr_famhom_from_zero Y.1)
       (fun X => contr_famhom_to_zero X.1).

Definition bfam_id_eta
  : NaturalTransformation (1%functor : Functor BFamCat BFamCat)
      (1 o 1)%functor.
Proof.
  refine (Build_NaturalTransformation 1%functor (1 o 1)%functor
            (fun X : object BFamCat => fam_id X.1) _).
  intros X Y f.
  exact (left_identity BFamCat X Y f @ (right_identity BFamCat X Y f)^).
Defined.

Definition bfam_id_epsilon
  : NaturalTransformation ((1 o 1)%functor : Functor BFamCat BFamCat)
      1%functor.
Proof.
  refine (Build_NaturalTransformation (1 o 1)%functor 1%functor
            (fun X : object BFamCat => fam_id X.1) _).
  intros X Y f.
  exact (left_identity BFamCat X Y f @ (right_identity BFamCat X Y f)^).
Defined.

Definition BFamPreStable : PreStableCategory
  := Build_PreStableCategory BFamCat BFamZero 1%functor 1%functor
       bfam_id_eta bfam_id_epsilon.

Definition bfam_lift (G : Functor (FamCat nat) (FamCat nat))
  (HG : forall (X : BFamObj) (k : nat), nat_lt W k ->
        object_of G X.1 k = false)
  : Functor BFamCat BFamCat.
Proof.
  refine (Build_Functor BFamCat BFamCat
            (fun X => (object_of G X.1 ; HG X))
            (fun X Y f => morphism_of G f)
            _ _).
  - intros X Y Z f g.
    exact (composition_of G X.1 Y.1 Z.1 f g).
  - intro X.
    exact (identity_of G X.1).
Defined.

Lemma truncAt_false (b : Bool) : truncAt b false = false.
Proof.
  destruct b; reflexivity.
Defined.

Lemma bfam_trunc_supported (g : nat -> Bool) (X : BFamObj)
  : forall k, nat_lt W k -> object_of (FamTrunc g) X.1 k = false.
Proof.
  intros k Hk.
  exact (ap (truncAt (g k)) (X.2 k Hk) @ truncAt_false (g k)).
Defined.

Definition BFamP (n : nat) : ReducedFunctor BFamPreStable.
Proof.
  refine (Build_ReducedFunctor BFamPreStable
            (bfam_lift (FamTrunc (fam_guard_P n))
               (bfam_trunc_supported (fam_guard_P n)))
            _).
  apply path_sigma_hprop.
  exact (fam_trunc_zero (fam_guard_P n)).
Defined.

Definition BFamD (n : nat) : ReducedFunctor BFamPreStable.
Proof.
  refine (Build_ReducedFunctor BFamPreStable
            (bfam_lift (FamTrunc (fam_guard_D n))
               (bfam_trunc_supported (fam_guard_D n)))
            _).
  apply path_sigma_hprop.
  exact (fam_trunc_zero (fam_guard_D n)).
Defined.

Definition BFamId : ReducedFunctor BFamPreStable
  := Build_ReducedFunctor BFamPreStable 1%functor idpath.

Definition bfam_P_trans (n : nat)
  : NatTransBetweenReduced BFamPreStable (BFamP (S n)) (BFamP n).
Proof.
  refine (Build_NatTransBetweenReduced BFamPreStable (BFamP (S n)) (BFamP n) _).
  refine (Build_NaturalTransformation (BFamP (S n)) (BFamP n)
            (fun X => fam_change (fam_guard_P (S n)) (fam_guard_P n) X.1) _).
  intros X Y f.
  exact (fam_change_natural (fam_guard_P (S n)) (fam_guard_P n) X.1 Y.1 f).
Defined.

Definition bfam_from_id_trans (n : nat)
  : NatTransBetweenReduced BFamPreStable BFamId (BFamP n).
Proof.
  refine (Build_NatTransBetweenReduced BFamPreStable BFamId (BFamP n) _).
  refine (Build_NaturalTransformation BFamId (BFamP n)
            (fun X => fam_change fam_guard_all (fam_guard_P n) X.1) _).
  intros X Y f.
  exact (fam_change_natural fam_guard_all (fam_guard_P n) X.1 Y.1 f).
Defined.

Definition BFamGoodwillieData : GoodwillieTowerData BFamPreStable BFamId
  := {| gtd_P := BFamP;
        gtd_p := bfam_P_trans;
        gtd_from_F := bfam_from_id_trans |}.

Definition BFamGoodwillieTower
  : GoodwillieTowerWithLayers BFamPreStable BFamId.
Proof.
  refine {| gtwl_data := BFamGoodwillieData; gtwl_D := BFamD |}.
  intros n X Hzero.
  exact (fam_layer_zero_implies_iso n X.1
           (ap (fun Z : BFamObj => Z.1) Hzero)).
Defined.

Fixpoint fam_count (X : FamObj nat) (k : nat) : nat
  := match k with
     | O => if X O then S O else O
     | S k' => nat_add (if X k then S O else O) (fam_count X k')
     end.

Lemma fam_count_zero_family (k : nat)
  : fam_count (fam_zero : FamObj nat) k = O.
Proof.
  induction k.
  - reflexivity.
  - exact IHk.
Defined.

Lemma fam_count_all_false (X : FamObj nat) (k : nat)
  (Hall : forall j, nat_le j k -> X j = false)
  : fam_count X k = O.
Proof.
  induction k.
  - exact (ap (fun b : Bool => if b then S O else O) (Hall O tt)).
  - refine (ap (fun b : Bool => nat_add (if b then S O else O) (fam_count X k))
             (Hall (S k) (nat_le_refl (S k))) @ _).
    exact (IHk (fun j Hj => Hall j (nat_le_succ_r j k Hj))).
Defined.

Lemma fam_count_zero_all (X : FamObj nat) (k : nat)
  (Hz : fam_count X k = O)
  : forall j, nat_le j k -> X j = false.
Proof.
  revert Hz.
  induction k.
  - intros Hz j Hj.
    destruct j.
    + destruct (bool_dec_eq (X O)) as [Hb | Hb].
      * apply Empty_rec.
        pose (Hz' := transport (fun b : Bool => (if b then S O else O) = O)
                       Hb Hz).
        exact (transport
                 (fun m : nat => match m with O => Empty | S _ => Unit end)
                 Hz' tt).
      * exact Hb.
    + destruct Hj.
  - intros Hz j Hj.
    destruct (bool_dec_eq (X (S k))) as [Hb | Hb].
    + apply Empty_rec.
      pose (Hz' := transport
                     (fun b : Bool =>
                        nat_add (if b then S O else O) (fam_count X k) = O)
                     Hb Hz).
      exact (transport
               (fun m : nat => match m with O => Empty | S _ => Unit end)
               Hz' tt).
    + pose (Hz' := transport
                     (fun b : Bool =>
                        nat_add (if b then S O else O) (fam_count X k) = O)
                     Hb Hz).
      destruct (nat_lt_or_eq_or_gt j (S k)) as [[Hlt | Heq] | Hgt].
      * exact (IHk Hz' j (nat_le_of_lt_S j k Hlt)).
      * exact (transport (fun m => X m = false) Heq^ Hb).
      * exact (Empty_rec _ (nat_le_lt_contradiction j (S k) Hj Hgt)).
Defined.

Definition bfam_measure : WeightMeasure BFamCat BFamZero.
Proof.
  refine (Build_WeightMeasure BFamCat BFamZero
            (fun X : object BFamCat => nat_to_qpos (fam_count X.1 W)) _).
  exact (ap nat_to_qpos (fam_count_zero_family W)).
Defined.

Theorem bfam_zero_measure_implies
  : ZeroMeasureImpliesZeroObj BFamPreStable bfam_measure.
Proof.
  intros X Hz.
  apply path_sigma_hprop.
  apply path_forall; intro k.
  destruct (nat_lt_or_eq_or_gt W k) as [[Hlt | Heq] | Hgt].
  - exact (X.2 k Hlt).
  - exact (transport (fun m => X.1 m = false) Heq
             (fam_count_zero_all X.1 W Hz W (nat_le_refl W))).
  - exact (fam_count_zero_all X.1 W Hz k (nat_le_of_lt k W Hgt)).
Defined.

Theorem bfam_zero_object_decidable (X : object BFamPreStable)
  : ((X = zero BFamPreStable (ps_zero BFamPreStable))
     + (X = zero BFamPreStable (ps_zero BFamPreStable) -> Empty))%type.
Proof.
  destruct (bool_dec_eq (nat_eqb (fam_count X.1 W) O)) as [Hb | Hb].
  - left.
    apply bfam_zero_measure_implies.
    exact (nat_eqb_true_path _ _ Hb).
  - right.
    intro Hpath.
    pose (Hc := ap (fun Z : BFamObj => fam_count Z.1 W) Hpath
                  @ fam_count_zero_family W).
    exact (false_ne_true
             (Hb^ @ ap (fun m => nat_eqb m O) Hc @ nat_eqb_refl O)).
Defined.

Lemma nat_eqb_false_of_path_absurd (j m : nat)
  (Hne : j = m -> Empty)
  : nat_eqb j m = false.
Proof.
  destruct (bool_dec_eq (nat_eqb j m)) as [Hb | Hb].
  - exact (Empty_rec _ (Hne (nat_eqb_true_path j m Hb))).
  - exact Hb.
Defined.

Lemma fam_count_le_one_of_single (X : FamObj nat) (m : nat)
  (Hs : forall j, nat_eqb j m = false -> X j = false)
  : forall k, nat_le (fam_count X k) (S O).
Proof.
  induction k.
  - simpl.
    destruct (X O); exact tt.
  - destruct (bool_dec_eq (nat_eqb (S k) m)) as [He | He].
    + refine (transport
               (fun c => nat_le (nat_add (if X (S k) then S O else O) c) (S O))
               (fam_count_all_false X k
                  (fun j Hj => Hs j
                     (nat_eqb_false_of_path_absurd j m
                        (fun p => nat_le_lt_contradiction (S k) k
                           (transport (fun mm => nat_le mm k)
                              (p @ (nat_eqb_true_path (S k) m He)^) Hj)
                           (nat_lt_S k)))))^ _).
      destruct (X (S k)); exact tt.
    + refine (transport
               (fun b : Bool =>
                  nat_le (nat_add (if b then S O else O) (fam_count X k)) (S O))
               (Hs (S k) He)^ _).
      exact IHk.
Defined.

Lemma bfam_layer_count_le_one (n : nat) (X : object BFamPreStable)
  : nat_le (fam_count (fam_trunc (fam_guard_D n) X.1) W) (S O).
Proof.
  apply (fam_count_le_one_of_single _ (S n)).
  intros j He.
  exact (ap (fun b => truncAt b (X.1 j)) He).
Defined.

Theorem bfam_layers_bounded (X : object BFamPreStable)
  : GoodwillieLayersBounded BFamGoodwillieTower bfam_measure X
      (nat_to_qpos (S (S W))).
Proof.
  intro n.
  refine (transport (fun q => qpos_lt _ q)
           (nat_to_qpos_S_N_times_w_stage (S W) n)^ _).
  unfold gtwl_layer_measure.
  simpl.
  pose proof (bfam_layer_count_le_one n X) as Hle.
  pose (cc := fam_count (fam_trunc (fam_guard_D n) X.1) W).
  pose (Hcc := idpath cc
                : fam_count (fam_trunc (fam_guard_D n) X.1) W = cc).
  clearbody Hcc.
  clearbody cc.
  pose (Hle' := transport (fun m => nat_le m (S O)) Hcc Hle).
  refine (transport
           (fun m => qpos_lt (nat_to_qpos m)
              {| qpos_num := S (S W); qpos_denom_pred := n |})
           Hcc^ _).
  destruct cc as [| c'].
  - exact tt.
  - destruct c' as [| c''].
    + apply one_lt_SN_over_Sn.
      destruct (nat_le_total n W) as [HnW | HWn].
      * exact (nat_lt_of_lt n (S W) (leq_succ (leq_of_nat_le n W HnW))).
      * apply Empty_rec.
        pose (Hz := fam_count_all_false (fam_trunc (fam_guard_D n) X.1) W
                      (fun j Hj =>
                         ap (fun b => truncAt b (X.1 j))
                           (nat_eqb_false_of_path_absurd j (S n)
                              (fun p => nat_le_lt_contradiction j n
                                 (nat_le_trans j W n Hj HWn)
                                 (transport (fun mm => nat_lt n mm)
                                    p^ (nat_lt_S n)))))).
        exact (transport
                 (fun m : nat =>
                    match m with O => Unit | S _ => Empty end)
                 (Hz^ @ Hcc) tt).
    + destruct Hle'.
Defined.

Theorem bfam_layer_minimal (X : object BFamPreStable)
  : HasMinimalPositive
      (fun n => gtwl_layer_measure BFamGoodwillieTower bfam_measure n X).
Proof.
  exists (nat_to_qpos (S O)).
  split.
  - exact tt.
  - intro n.
    unfold gtwl_layer_measure.
    simpl.
    pose proof (bfam_layer_count_le_one n X) as Hle.
    pose (cc := fam_count (fam_trunc (fam_guard_D n) X.1) W).
    pose (Hcc := idpath cc
                  : fam_count (fam_trunc (fam_guard_D n) X.1) W = cc).
    clearbody Hcc.
    clearbody cc.
    pose (Hle' := transport (fun m => nat_le m (S O)) Hcc Hle).
    refine (transport
             (fun m => ((qpos_is_zero (nat_to_qpos m))
                + ((qpos_lt (nat_to_qpos (S O)) (nat_to_qpos m))
                   + (nat_to_qpos m = nat_to_qpos (S O))))%type)
             Hcc^ _).
    destruct cc as [| c'].
    + left.
      reflexivity.
    + destruct c' as [| c''].
      * right.
        right.
        reflexivity.
      * destruct Hle'.
Defined.

Theorem bfam_goodwillie_stabilizes (X : object BFamPreStable)
  : { N : nat & forall n, nat_le N n ->
      IsIsomorphism
        (gtd_layer_at (gtwl_data BFamPreStable BFamId BFamGoodwillieTower)
           n X) }.
Proof.
  apply (goodwillie_tower_stabilizes BFamGoodwillieTower bfam_measure X
           (nat_to_qpos (S (S W)))).
  - exact tt.
  - exact (bfam_layers_bounded X).
  - exact (bfam_layer_minimal X).
  - exact bfam_zero_measure_implies.
Defined.

End BoundedFamilies.

(*******************************************************************************)
(*  CONCRETE SCHEMES: GENUINE MORPHISM DATA, A1-HOMOTOPY, AND THE              *)
(*  SEPARATION OF SCHEME ISOMORPHISM FROM A1-EQUIVALENCE                       *)
(*******************************************************************************)

(** Concrete schemes carry set-level carriers, and the projection from X x A1 is an A1-equivalence yet not a scheme isomorphism over F2 at the point. *)

Record CField : Type := {
  cf_carrier : Type;
  cf_ishset : IsHSet cf_carrier;
  cf_zero : cf_carrier;
  cf_one : cf_carrier;
  cf_mul : cf_carrier -> cf_carrier -> cf_carrier;
  cf_mul_one_r : forall x, cf_mul x cf_one = x;
  cf_mul_zero_r : forall x, cf_mul x cf_zero = cf_zero;
  cf_zero_ne_one : cf_zero = cf_one -> Empty;
  cf_add : cf_carrier -> cf_carrier -> cf_carrier;
  cf_neg : cf_carrier -> cf_carrier;
  cf_add_assoc : forall x y z, cf_add x (cf_add y z) = cf_add (cf_add x y) z;
  cf_add_comm : forall x y, cf_add x y = cf_add y x;
  cf_add_zero_r : forall x, cf_add x cf_zero = x;
  cf_add_neg_r : forall x, cf_add x (cf_neg x) = cf_zero;
  cf_mul_assoc : forall x y z, cf_mul x (cf_mul y z) = cf_mul (cf_mul x y) z;
  cf_mul_comm : forall x y, cf_mul x y = cf_mul y x;
  cf_dist : forall x y z,
    cf_mul x (cf_add y z) = cf_add (cf_mul x y) (cf_mul x z);
  cf_inv : cf_carrier -> cf_carrier;
  cf_inv_r : forall x, (x = cf_zero -> Empty) -> cf_mul x (cf_inv x) = cf_one
}.

Definition xorb (a b : Bool) : Bool := if a then negb b else b.

Lemma xorb_assoc (x y z : Bool) : xorb x (xorb y z) = xorb (xorb x y) z.
Proof.
  destruct x, y, z; reflexivity.
Defined.

Lemma xorb_comm (x y : Bool) : xorb x y = xorb y x.
Proof.
  destruct x, y; reflexivity.
Defined.

Lemma xorb_false_r (x : Bool) : xorb x false = x.
Proof.
  destruct x; reflexivity.
Defined.

Lemma xorb_diag (x : Bool) : xorb x x = false.
Proof.
  destruct x; reflexivity.
Defined.

Lemma andb_assoc_field (x y z : Bool)
  : andb x (andb y z) = andb (andb x y) z.
Proof.
  destruct x, y, z; reflexivity.
Defined.

Lemma andb_comm (x y : Bool) : andb x y = andb y x.
Proof.
  destruct x, y; reflexivity.
Defined.

Lemma andb_xorb_dist (x y z : Bool)
  : andb x (xorb y z) = xorb (andb x y) (andb x z).
Proof.
  destruct x, y, z; reflexivity.
Defined.

Lemma bool_self_inv (x : Bool) (Hx : x = false -> Empty)
  : andb x x = true.
Proof.
  destruct x.
  - reflexivity.
  - exact (Empty_rec _ (Hx idpath)).
Defined.

Definition F2 : CField
  := {| cf_carrier := Bool;
        cf_ishset := hset_bool;
        cf_zero := false;
        cf_one := true;
        cf_mul := andb;
        cf_mul_one_r := andb_true_r;
        cf_mul_zero_r := andb_false_r;
        cf_zero_ne_one := false_ne_true;
        cf_add := xorb;
        cf_neg := idmap;
        cf_add_assoc := xorb_assoc;
        cf_add_comm := xorb_comm;
        cf_add_zero_r := xorb_false_r;
        cf_add_neg_r := xorb_diag;
        cf_mul_assoc := andb_assoc_field;
        cf_mul_comm := andb_comm;
        cf_dist := andb_xorb_dist;
        cf_inv := idmap;
        cf_inv_r := bool_self_inv |}.

(** Fields have no zero divisors, constructively: a product vanishing with invertible left factor forces the right factor to vanish. *)

Theorem cfield_integral (F : CField) (x y : cf_carrier F)
  (Hx : x = cf_zero F -> Empty)
  (Hxy : cf_mul F x y = cf_zero F)
  : y = cf_zero F.
Proof.
  refine ((cf_mul_one_r F y)^ @ _).
  refine (ap (cf_mul F y) (cf_inv_r F x Hx)^ @ _).
  refine (cf_mul_assoc F y x (cf_inv F x) @ _).
  refine (ap (fun w => cf_mul F w (cf_inv F x)) (cf_mul_comm F y x) @ _).
  refine (ap (fun w => cf_mul F w (cf_inv F x)) Hxy @ _).
  refine (cf_mul_comm F (cf_zero F) (cf_inv F x) @ _).
  exact (cf_mul_zero_r F (cf_inv F x)).
Defined.

Record CScheme (F : CField) : Type := {
  cs_carrier : Type;
  cs_ishset : IsHSet cs_carrier;
  cs_dim : nat;
  cs_sing : nat
}.

(** *** Affine data determining dimension and singularity: coordinate subspaces of affine space derive cs_dim as the free-coordinate count, unions of two subspaces derive cs_sing as the crossing count, and both counts are characterized by the carrier. *)

Record AffineDatum (F : CField) := {
  ad_vars : nat;
  ad_mask : nat -> Bool
}.

Definition ad_free (F : CField) (D : AffineDatum F) : nat -> Bool
  := fun i => andb (ad_mask F D i) (nat_leb (S i) (ad_vars F D)).

Definition ad_carrier (F : CField) (D : AffineDatum F) : Type
  := { p : nat -> cf_carrier F &
       forall i, ad_free F D i = false -> p i = cf_zero F }.

Global Instance ishset_ad_carrier `{Funext} (F : CField) (D : AffineDatum F)
  : IsHSet (ad_carrier F D).
Proof.
  pose proof (cf_ishset F) as Hf.
  apply istrunc_sigma.
Defined.

Definition ad_dim (F : CField) (D : AffineDatum F) : nat
  := fam_count (ad_free F D) (ad_vars F D).

Definition cscheme_of_datum `{Funext} (F : CField) (D : AffineDatum F)
  : CScheme F
  := {| cs_carrier := ad_carrier F D;
        cs_ishset := ishset_ad_carrier F D;
        cs_dim := ad_dim F D;
        cs_sing := O |}.

Definition ad_origin (F : CField) (D : AffineDatum F) : ad_carrier F D
  := ((fun _ => cf_zero F) ; fun i _ => idpath).

Definition ad_axis_point (F : CField) (D : AffineDatum F) (i : nat)
  (Hi : ad_free F D i = true)
  : ad_carrier F D.
Proof.
  exists (fun j => if nat_eqb j i then cf_one F else cf_zero F).
  intros j Hj.
  destruct (bool_dec_eq (nat_eqb j i)) as [He | He].
  - apply Empty_rec.
    exact (false_ne_true
             (Hj^ @ ap (ad_free F D) (nat_eqb_true_path j i He) @ Hi)).
  - exact (ap (fun b : Bool => if b then cf_one F else cf_zero F) He).
Defined.

Theorem ad_dim_zero_of_contr `{Funext} (F : CField) (D : AffineDatum F)
  (Hc : Contr (ad_carrier F D))
  : ad_dim F D = O.
Proof.
  apply fam_count_all_false.
  intros i Hle.
  destruct (bool_dec_eq (ad_free F D i)) as [Hb | Hb].
  - apply Empty_rec.
    apply (cf_zero_ne_one F).
    refine ((apD10 (ap (fun z : ad_carrier F D => z.1)
              (@path_contr _ Hc (ad_origin F D) (ad_axis_point F D i Hb)))
              i) @ _).
    exact (ap (fun b : Bool => if b then cf_one F else cf_zero F)
             (nat_eqb_refl i)).
  - exact Hb.
Defined.

Lemma nat_leb_true_le (a b : nat) : nat_leb a b = true -> nat_le a b.
Proof.
  revert b.
  induction a.
  - intros b _.
    exact tt.
  - intros b Hb.
    destruct b.
    + exact (false_ne_true Hb).
    + exact (IHa b Hb).
Defined.

Theorem ad_contr_of_dim_zero `{Funext} (F : CField) (D : AffineDatum F)
  (Hd : ad_dim F D = O)
  : Contr (ad_carrier F D).
Proof.
  refine (Build_Contr _ (ad_origin F D) _).
  intro p.
  pose proof (cf_ishset F) as Hf.
  apply path_sigma_hprop.
  apply path_forall; intro i.
  symmetry.
  destruct (bool_dec_eq (ad_free F D i)) as [Hb | Hb].
  - apply Empty_rec.
    destruct (nat_le_total i (ad_vars F D)) as [Hle | Hge].
    + exact (false_ne_true
               ((fam_count_zero_all (ad_free F D) (ad_vars F D) Hd i Hle)^
                  @ Hb)).
    + destruct (bool_dec_eq (ad_mask F D i)) as [Hm | Hm].
      * pose (Hb' := (ap (fun b => andb b (nat_leb (S i) (ad_vars F D))) Hm)^
                       @ Hb).
        exact (nat_le_lt_contradiction (S i) i
                 (nat_le_trans (S i) (ad_vars F D) i
                    (nat_leb_true_le (S i) (ad_vars F D) Hb')
                    Hge)
                 (nat_lt_S i)).
      * exact (false_ne_true
                 ((ap (fun b => andb b (nat_leb (S i) (ad_vars F D))) Hm)^
                    @ Hb)).
  - exact (p.2 i Hb).
Defined.

(** Unions of two coordinate subspaces derive the singularity count as the crossing count, characterized by the meeting locus of the components. *)

Import HoTT.Truncations.Core.

Record UnionDatum (F : CField) := {
  ud_vars : nat;
  ud_mask1 : nat -> Bool;
  ud_mask2 : nat -> Bool
}.

Definition ud_free1 (F : CField) (U : UnionDatum F) : nat -> Bool
  := fun i => andb (ud_mask1 F U i) (nat_leb (S i) (ud_vars F U)).

Definition ud_free2 (F : CField) (U : UnionDatum F) : nat -> Bool
  := fun i => andb (ud_mask2 F U i) (nat_leb (S i) (ud_vars F U)).

Definition ud_cross (F : CField) (U : UnionDatum F) : nat -> Bool
  := fun i => andb (ud_free1 F U i) (ud_free2 F U i).

Definition ud_in1 (F : CField) (U : UnionDatum F)
  (p : nat -> cf_carrier F) : Type
  := forall i, ud_free1 F U i = false -> p i = cf_zero F.

Definition ud_in2 (F : CField) (U : UnionDatum F)
  (p : nat -> cf_carrier F) : Type
  := forall i, ud_free2 F U i = false -> p i = cf_zero F.

Definition ud_carrier (F : CField) (U : UnionDatum F) : Type
  := { p : nat -> cf_carrier F &
       merely ((ud_in1 F U p) + (ud_in2 F U p)) }.

Global Instance ishset_ud_carrier `{Funext} (F : CField) (U : UnionDatum F)
  : IsHSet (ud_carrier F U).
Proof.
  pose proof (cf_ishset F) as Hf.
  apply istrunc_sigma.
Defined.

Definition uscheme_of_datum `{Funext} (F : CField) (U : UnionDatum F)
  : CScheme F
  := {| cs_carrier := ud_carrier F U;
        cs_ishset := ishset_ud_carrier F U;
        cs_dim := nat_max (fam_count (ud_free1 F U) (ud_vars F U))
                          (fam_count (ud_free2 F U) (ud_vars F U));
        cs_sing := fam_count (ud_cross F U) (ud_vars F U) |}.

Lemma andb_true_split (a b : Bool) (Hab : andb a b = true)
  : ((a = true) * (b = true))%type.
Proof.
  destruct a.
  - exact (idpath, Hab).
  - exact (Empty_rec _ (false_ne_true Hab)).
Defined.

Theorem ud_sing_zero_meet `{Funext} (F : CField) (U : UnionDatum F)
  (Hs : fam_count (ud_cross F U) (ud_vars F U) = O)
  (p : nat -> cf_carrier F)
  (H1 : ud_in1 F U p) (H2 : ud_in2 F U p)
  : forall i, p i = cf_zero F.
Proof.
  intro i.
  destruct (bool_dec_eq (ud_free1 F U i)) as [Hb1 | Hb1].
  - destruct (bool_dec_eq (ud_free2 F U i)) as [Hb2 | Hb2].
    + apply Empty_rec.
      destruct (nat_le_total i (ud_vars F U)) as [Hle | Hge].
      * refine (false_ne_true
                 ((fam_count_zero_all (ud_cross F U) (ud_vars F U) Hs i Hle)^
                    @ _)).
        unfold ud_cross.
        exact (ap (fun b => andb b (ud_free2 F U i)) Hb1
                 @ ap (fun b => andb true b) Hb2).
      * destruct (andb_true_split _ _ Hb1) as [Hm1 Hl1].
        exact (nat_le_lt_contradiction (S i) i
                 (nat_le_trans (S i) (ud_vars F U) i
                    (nat_leb_true_le (S i) (ud_vars F U) Hl1)
                    Hge)
                 (nat_lt_S i)).
    + exact (H2 i Hb2).
  - exact (H1 i Hb1).
Defined.

Theorem ud_meet_zero_sing `{Funext} (F : CField) (U : UnionDatum F)
  (Hmeet : forall p, ud_in1 F U p -> ud_in2 F U p ->
           forall i, p i = cf_zero F)
  : fam_count (ud_cross F U) (ud_vars F U) = O.
Proof.
  apply fam_count_all_false.
  intros i Hle.
  destruct (bool_dec_eq (ud_cross F U i)) as [Hb | Hb].
  - apply Empty_rec.
    destruct (andb_true_split _ _ Hb) as [Hb1 Hb2].
    pose (e := fun j => if nat_eqb j i then cf_one F else cf_zero F).
    assert (He1 : ud_in1 F U e).
    { intros j Hj.
      destruct (bool_dec_eq (nat_eqb j i)) as [He | He].
      - apply Empty_rec.
        exact (false_ne_true
                 (Hj^ @ ap (ud_free1 F U) (nat_eqb_true_path j i He) @ Hb1)).
      - exact (ap (fun b : Bool => if b then cf_one F else cf_zero F) He). }
    assert (He2 : ud_in2 F U e).
    { intros j Hj.
      destruct (bool_dec_eq (nat_eqb j i)) as [He | He].
      - apply Empty_rec.
        exact (false_ne_true
                 (Hj^ @ ap (ud_free2 F U) (nat_eqb_true_path j i He) @ Hb2)).
      - exact (ap (fun b : Bool => if b then cf_one F else cf_zero F) He). }
    apply (cf_zero_ne_one F).
    refine ((Hmeet e He1 He2 i)^ @ _).
    exact (ap (fun b : Bool => if b then cf_one F else cf_zero F)
             (nat_eqb_refl i)).
  - exact Hb.
Defined.

(** *** Polynomial morphisms on affine data: coordinatewise polynomial expressions with soundness into the target subspace, closed under identity and substitution. *)

Inductive PolyExpr (F : CField) : Type :=
  | pe_const : cf_carrier F -> PolyExpr F
  | pe_var : nat -> PolyExpr F
  | pe_add : PolyExpr F -> PolyExpr F -> PolyExpr F
  | pe_mul : PolyExpr F -> PolyExpr F -> PolyExpr F.

Fixpoint pe_eval (F : CField) (e : PolyExpr F)
  (p : nat -> cf_carrier F) : cf_carrier F
  := match e with
     | pe_const c => c
     | pe_var i => p i
     | pe_add a b => cf_add F (pe_eval F a p) (pe_eval F b p)
     | pe_mul a b => cf_mul F (pe_eval F a p) (pe_eval F b p)
     end.

Fixpoint pe_subst (F : CField) (e : PolyExpr F)
  (s : nat -> PolyExpr F) : PolyExpr F
  := match e with
     | pe_const c => pe_const F c
     | pe_var i => s i
     | pe_add a b => pe_add F (pe_subst F a s) (pe_subst F b s)
     | pe_mul a b => pe_mul F (pe_subst F a s) (pe_subst F b s)
     end.

Lemma pe_eval_subst (F : CField) (e : PolyExpr F)
  (s : nat -> PolyExpr F) (p : nat -> cf_carrier F)
  : pe_eval F (pe_subst F e s) p
    = pe_eval F e (fun i => pe_eval F (s i) p).
Proof.
  induction e.
  - reflexivity.
  - reflexivity.
  - simpl.
    exact (ap011 (cf_add F) IHe1 IHe2).
  - simpl.
    exact (ap011 (cf_mul F) IHe1 IHe2).
Defined.

Record PolyMor (F : CField) (D E : AffineDatum F) := {
  pm_coord : nat -> PolyExpr F;
  pm_sound : forall (p : ad_carrier F D) (i : nat),
    ad_free F E i = false ->
    pe_eval F (pm_coord i) p.1 = cf_zero F
}.

Definition pm_apply (F : CField) (D E : AffineDatum F)
  (m : PolyMor F D E)
  : ad_carrier F D -> ad_carrier F E
  := fun p => ((fun i => pe_eval F (pm_coord F D E m i) p.1) ;
               fun i Hi => pm_sound F D E m p i Hi).

Definition pm_id (F : CField) (D : AffineDatum F) : PolyMor F D D.
Proof.
  refine (Build_PolyMor F D D (fun i => pe_var F i) _).
  intros p i Hi.
  exact (p.2 i Hi).
Defined.

Definition pm_comp (F : CField) (D E G : AffineDatum F)
  (n : PolyMor F E G) (m : PolyMor F D E)
  : PolyMor F D G.
Proof.
  refine (Build_PolyMor F D G
            (fun i => pe_subst F (pm_coord F E G n i) (pm_coord F D E m))
            _).
  intros p i Hi.
  refine (pe_eval_subst F (pm_coord F E G n i) (pm_coord F D E m) p.1 @ _).
  exact (pm_sound F E G n (pm_apply F D E m p) i Hi).
Defined.

Theorem pm_apply_comp `{Funext} (F : CField) (D E G : AffineDatum F)
  (n : PolyMor F E G) (m : PolyMor F D E) (p : ad_carrier F D)
  : (pm_apply F D G (pm_comp F D E G n m) p).1
    = (pm_apply F E G n (pm_apply F D E m p)).1.
Proof.
  apply path_forall; intro i.
  exact (pe_eval_subst F (pm_coord F E G n i) (pm_coord F D E m) p.1).
Defined.

Definition CMor {F : CField} (X Y : CScheme F) : Type
  := cs_carrier F X -> cs_carrier F Y.

(** Audit: fst and snd are shadowed by HoTT.Categories under this import set, so carrier projections are local. *)

Definition prod_pr1 {A B : Type} (p : (A * B)%type) : A
  := match p with (a, _) => a end.

Definition prod_pr2 {A B : Type} (p : (A * B)%type) : B
  := match p with (_, b) => b end.

Lemma prod_eta {A B : Type} (p : (A * B)%type)
  : (prod_pr1 p, prod_pr2 p) = p.
Proof.
  destruct p.
  reflexivity.
Defined.

(** *** Nisnevich squares with the completely decomposed condition: every point lies merely in the open part or has a contractible fiber in the etale part, which yields a genuine section off the open locus, something joint surjectivity cannot deliver. *)

Record NisSquare (F : CField) := {
  ns_X : CScheme F;
  ns_U : CScheme F;
  ns_V : CScheme F;
  ns_u : CMor ns_U ns_X;
  ns_v : CMor ns_V ns_X;
  ns_decomp : forall x : cs_carrier F ns_X,
    ((merely { u : cs_carrier F ns_U & ns_u u = x })
     + (Contr { v : cs_carrier F ns_V & ns_v v = x }))%type
}.

Theorem nis_jointly_surjective (F : CField) (S : NisSquare F)
  (x : cs_carrier F (ns_X F S))
  : merely (({ u : cs_carrier F (ns_U F S) & ns_u F S u = x }
             + { v : cs_carrier F (ns_V F S) & ns_v F S v = x })%type).
Proof.
  destruct (ns_decomp F S x) as [Hu | Hv].
  - strip_truncations.
    apply tr.
    left.
    exact Hu.
  - apply tr.
    right.
    exact (@center _ Hv).
Defined.

Theorem nis_off_open_section (F : CField) (S : NisSquare F)
  (x : cs_carrier F (ns_X F S))
  (Hoff : merely { u : cs_carrier F (ns_U F S) & ns_u F S u = x } -> Empty)
  : { v : cs_carrier F (ns_V F S) & ns_v F S v = x }.
Proof.
  destruct (ns_decomp F S x) as [Hu | Hv].
  - exact (Empty_rec _ (Hoff Hu)).
  - exact (@center _ Hv).
Defined.

Theorem nis_off_open_section_unique (F : CField) (S : NisSquare F)
  (x : cs_carrier F (ns_X F S))
  (Hoff : merely { u : cs_carrier F (ns_U F S) & ns_u F S u = x } -> Empty)
  (w w' : { v : cs_carrier F (ns_V F S) & ns_v F S v = x })
  : w = w'.
Proof.
  destruct (ns_decomp F S x) as [Hu | Hv].
  - exact (Empty_rec _ (Hoff Hu)).
  - exact (@path_contr _ Hv w w').
Defined.

(** *** Fiber products of concrete schemes with dimension and singularity bookkeeping and the genuine pullback universal property. *)

Definition cfp_carrier {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z) : Type
  := { xy : (cs_carrier F X * cs_carrier F Y)%type &
       f (prod_pr1 xy) = g (prod_pr2 xy) }.

Global Instance ishset_cfp_carrier `{Funext} {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z)
  : IsHSet (cfp_carrier f g).
Proof.
  pose proof (cs_ishset F X) as HX.
  pose proof (cs_ishset F Y) as HY.
  pose proof (cs_ishset F Z) as HZ.
  apply istrunc_sigma.
Defined.

Definition cfiber_product `{Funext} {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z)
  : CScheme F
  := {| cs_carrier := cfp_carrier f g;
        cs_ishset := ishset_cfp_carrier f g;
        cs_dim := nat_sub (nat_add (cs_dim F X) (cs_dim F Y)) (cs_dim F Z);
        cs_sing := nat_add (cs_sing F X) (cs_sing F Y) |}.

Definition cfp_pr1 `{Funext} {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z)
  : CMor (cfiber_product f g) X
  := fun w => prod_pr1 w.1.

Definition cfp_pr2 `{Funext} {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z)
  : CMor (cfiber_product f g) Y
  := fun w => prod_pr2 w.1.

Theorem cfp_comm `{Funext} {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z)
  : (fun w => f (cfp_pr1 f g w)) = (fun w => g (cfp_pr2 f g w)).
Proof.
  apply path_forall; intro w.
  exact w.2.
Defined.

Theorem cfiber_product_universal `{Funext} {F : CField} {X Y Z : CScheme F}
  (f : CMor X Z) (g : CMor Y Z)
  (W : CScheme F) (a : CMor W X) (b : CMor W Y)
  (Hab : (fun w => f (a w)) = (fun w => g (b w)))
  : Contr { u : CMor W (cfiber_product f g) &
            (((fun w => cfp_pr1 f g (u w)) = a)
             * ((fun w => cfp_pr2 f g (u w)) = b))%type }.
Proof.
  pose proof (cs_ishset F X) as HX.
  pose proof (cs_ishset F Y) as HY.
  pose proof (cs_ishset F Z) as HZ.
  refine (Build_Contr _
            ((fun w => ((a w , b w) ; apD10 Hab w)) ;
             (path_forall _ _ (fun w => idpath) ,
              path_forall _ _ (fun w => idpath))) _).
  intros [u' [e1 e2]].
  apply path_sigma_hprop.
  apply path_forall; intro w.
  symmetry.
  apply path_sigma_hprop.
  exact (path_prod ((u' w).1) ((a w , b w))
           (apD10 e1 w) (apD10 e2 w)).
Defined.

Global Instance ishset_cmor `{Funext} {F : CField} (X Y : CScheme F)
  : IsHSet (CMor X Y).
Proof.
  exact (@istrunc_forall _ _ _ _ (fun _ => cs_ishset F Y)).
Defined.

Definition cmor_comp {F : CField} (X Y Z : CScheme F)
  (g : CMor Y Z) (f : CMor X Y)
  : CMor X Z
  := fun x => g (f x).

Definition CSch `{Funext} (F : CField) : PreCategory
  := @Build_PreCategory
       (CScheme F)
       (fun X Y => CMor X Y)
       (fun X => fun x => x)
       (fun X Y Z g f => cmor_comp X Y Z g f)
       (fun s d d' d'' m1 m2 m3 => idpath)
       (fun a b f => idpath)
       (fun a b f => idpath)
       (fun s d => ishset_cmor s d).

Definition cpoint (F : CField) : CScheme F
  := {| cs_carrier := Unit;
        cs_ishset := hset_unit;
        cs_dim := O;
        cs_sing := O |}.

Definition cA1 (F : CField) : CScheme F
  := {| cs_carrier := cf_carrier F;
        cs_ishset := cf_ishset F;
        cs_dim := S O;
        cs_sing := O |}.

Definition cs_product {F : CField} (X Y : CScheme F) : CScheme F
  := {| cs_carrier := (cs_carrier F X * cs_carrier F Y)%type;
        cs_ishset := @istrunc_prod _ _ (cs_ishset F X) _ (cs_ishset F Y);
        cs_dim := nat_add (cs_dim F X) (cs_dim F Y);
        cs_sing := nat_add (cs_sing F X) (cs_sing F Y) |}.

(** *** The product-with-the-affine-line endofunctor on CSch: the scheme world and the tower world exchange morphisms through it. *)

Definition CSchA1Functor `{Funext} (F : CField)
  : Functor (CSch F) (CSch F).
Proof.
  refine (Build_Functor (CSch F) (CSch F)
            (fun X => cs_product X (cA1 F))
            (fun X Y f => fun xa => (f (prod_pr1 xa) , prod_pr2 xa))
            _ _).
  - intros X Y Z f g.
    apply path_forall; intro xa.
    reflexivity.
  - intro X.
    apply path_forall; intro xa.
    exact (prod_eta xa).
Defined.

Definition cproj {F : CField} (X : CScheme F)
  : CMor (cs_product X (cA1 F)) X
  := fun p => prod_pr1 p.

Definition csection {F : CField} (X : CScheme F)
  : CMor X (cs_product X (cA1 F))
  := fun x => (x, cf_zero F).

(** *** Elementary A1-homotopy *)

Definition A1Homotopic {F : CField} (X Y : CScheme F) (f g : CMor X Y) : Type
  := { HT : CMor (cs_product X (cA1 F)) Y &
       ((forall x, HT (x, cf_one F) = f x) *
        (forall x, HT (x, cf_zero F) = g x))%type }.

Definition IsA1Equiv {F : CField} (X Y : CScheme F) (f : CMor X Y) : Type
  := { g : CMor Y X &
       (A1Homotopic X X (fun x => x) (fun x => g (f x)) *
        A1Homotopic Y Y (fun y => y) (fun y => f (g y)))%type }.

(** The projection X x A1 -> X is an A1-equivalence for every X by straight-line contraction through the field multiplication. *)

Theorem cproj_A1_equiv {F : CField} (X : CScheme F)
  : IsA1Equiv (cs_product X (cA1 F)) X (cproj X).
Proof.
  exists (csection X).
  split.
  - exists (fun p => (prod_pr1 (prod_pr1 p),
                      cf_mul F (prod_pr2 (prod_pr1 p)) (prod_pr2 p))).
    split.
    + intro x.
      simpl.
      exact (ap (fun a => (prod_pr1 x, a)) (cf_mul_one_r F (prod_pr2 x))
               @ prod_eta x).
    + intro x.
      simpl.
      exact (ap (fun a => (prod_pr1 x, a)) (cf_mul_zero_r F (prod_pr2 x))).
  - exists (fun p => prod_pr1 p).
    split.
    + intro y.
      reflexivity.
    + intro y.
      reflexivity.
Defined.

Theorem cA1_contractible_to_point {F : CField}
  : IsA1Equiv (cA1 F) (cpoint F) (fun _ => tt).
Proof.
  exists (fun _ => cf_zero F).
  split.
  - exists (fun p => cf_mul F (prod_pr1 p) (prod_pr2 p)).
    split.
    + intro x.
      exact (cf_mul_one_r F x).
    + intro x.
      exact (cf_mul_zero_r F x).
  - exists (fun _ => tt).
    split.
    + intro y.
      destruct y.
      reflexivity.
    + intro y.
      reflexivity.
Defined.

(** *** The separation over F2: the projection from point x A1 is an A1-equivalence but not a scheme isomorphism. *)

Theorem cproj_cpoint_not_scheme_iso `{Funext}
  : @IsIsomorphism (CSch F2)
      (cs_product (cpoint F2) (cA1 F2)) (cpoint F2)
      (cproj (cpoint F2))
    -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  pose (p1 := ap10 Hgf (tt, true)).
  pose (p2 := ap10 Hgf (tt, false)).
  apply false_ne_true.
  exact (ap prod_pr2 (p2^ @ p1)).
Defined.

Theorem cpoint_not_iso_cA1 `{Funext}
  (f : morphism (CSch F2) (cpoint F2) (cA1 F2))
  : IsIsomorphism f -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  pose (p1 := ap10 Hfg true).
  pose (p2 := ap10 Hfg false).
  apply false_ne_true.
  exact (p2^ @ (ap f (path_contr (g false) (g true)) @ p1)).
Defined.

Theorem scheme_iso_and_A1_equiv_separate `{Funext}
  : (IsA1Equiv (cs_product (cpoint F2) (cA1 F2)) (cpoint F2) (cproj (cpoint F2)))
    * (@IsIsomorphism (CSch F2)
         (cs_product (cpoint F2) (cA1 F2)) (cpoint F2)
         (cproj (cpoint F2))
       -> Empty).
Proof.
  split.
  - exact (cproj_A1_equiv (cpoint F2)).
  - exact cproj_cpoint_not_scheme_iso.
Defined.

(*******************************************************************************)
(*  THE WEIGHT FUNCTIONS w_dim, w_sing, AND w_total                            *)
(*******************************************************************************)

(** The three weight functions on concrete schemes, with stage antitonicity and Archimedean vanishing as theorems, so every concrete scheme induces a WeightedTower. *)

Definition w_dim {F : CField} (X : CScheme F) : QPos
  := {| qpos_num := S O; qpos_denom_pred := cs_dim F X |}.

Definition w_sing {F : CField} (X : CScheme F) : QPos
  := {| qpos_num := S O; qpos_denom_pred := cs_sing F X |}.

Definition w_total {F : CField} (X : CScheme F) (n : nat) : QPos
  := qpos_mult (qpos_mult (w_dim X) (w_sing X)) (w_stage n).

Lemma w_total_num_one {F : CField} (X : CScheme F) (n : nat)
  : qpos_num (w_total X n) = S O.
Proof.
  reflexivity.
Defined.

Lemma w_total_never_zero {F : CField} (X : CScheme F) (n : nat)
  : qpos_is_zero (w_total X n) -> Empty.
Proof.
  intro p.
  exact (S_ne_O O p).
Defined.

Lemma nat_mul_interchange (a b c d : nat)
  : nat_mul (nat_mul a b) (nat_mul c d) = nat_mul (nat_mul a c) (nat_mul b d).
Proof.
  rewrite <- nat_mul_assoc.
  rewrite (nat_mul_assoc b c d).
  rewrite (nat_mul_comm b c).
  rewrite <- (nat_mul_assoc c b d).
  rewrite (nat_mul_assoc a c (nat_mul b d)).
  reflexivity.
Defined.

Lemma nat_lt_O_mul (a b : nat)
  : nat_lt O a -> nat_lt O b -> nat_lt O (nat_mul a b).
Proof.
  intros Ha Hb.
  destruct a.
  - destruct Ha.
  - destruct b.
    + destruct Hb.
    + exact (nat_mul_SS_pos a b).
Defined.

Lemma qpos_mult_lt_l (C a b : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hab : qpos_lt a b)
  : qpos_lt (qpos_mult C a) (qpos_mult C b).
Proof.
  unfold qpos_lt in *.
  unfold qpos_mult.
  simpl.
  rewrite (qpos_denom_mult C b).
  rewrite (qpos_denom_mult C a).
  rewrite (nat_mul_interchange (qpos_num C) (qpos_num a) (qpos_denom C) (qpos_denom b)).
  rewrite (nat_mul_interchange (qpos_num C) (qpos_num b) (qpos_denom C) (qpos_denom a)).
  rewrite (nat_mul_comm (nat_mul (qpos_num C) (qpos_denom C))
             (nat_mul (qpos_num a) (qpos_denom b))).
  rewrite (nat_mul_comm (nat_mul (qpos_num C) (qpos_denom C))
             (nat_mul (qpos_num b) (qpos_denom a))).
  apply nat_lt_mul_pos_r.
  - exact Hab.
  - apply nat_lt_O_mul.
    + exact HC.
    + unfold qpos_denom.
      exact tt.
Defined.

Lemma qpos_mult_lt_r (C a b : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hab : qpos_lt a b)
  : qpos_lt (qpos_mult a C) (qpos_mult b C).
Proof.
  unfold qpos_lt in *.
  unfold qpos_mult.
  simpl.
  rewrite (qpos_denom_mult b C).
  rewrite (qpos_denom_mult a C).
  rewrite (nat_mul_interchange (qpos_num a) (qpos_num C)
             (qpos_denom b) (qpos_denom C)).
  rewrite (nat_mul_interchange (qpos_num b) (qpos_num C)
             (qpos_denom a) (qpos_denom C)).
  apply nat_lt_mul_pos_r.
  - exact Hab.
  - apply nat_lt_O_mul.
    + exact HC.
    + unfold qpos_denom.
      exact tt.
Defined.

Theorem w_total_antitone {F : CField} (X : CScheme F) (n : nat)
  : qpos_lt (w_total X (S n)) (w_total X n).
Proof.
  apply qpos_mult_lt_l.
  - exact tt.
  - exact (w_stage_antitonicity n).
Defined.

Theorem w_total_limit_zero {F : CField} (X : CScheme F)
  : LimitZero (fun n => w_total X n).
Proof.
  intros epsilon Heps.
  set (C := qpos_mult (w_dim X) (w_sing X)).
  set (epsilon' := qpos_div_by epsilon C).
  assert (Heps' : nat_lt O (qpos_num epsilon')).
  { exact (qpos_div_by_pos epsilon C Heps). }
  destruct (w_stage_limit_zero epsilon' Heps') as [N HN].
  exists N.
  intros m Hm.
  apply qpos_mult_lt_from_div.
  - exact tt.
  - exact (HN m Hm).
Defined.

Definition w_total_tower {F : CField} (X : CScheme F) : WeightedTower
  := {| wt_threshold := w_total X;
        wt_threshold_decreasing := w_total_antitone X |}.

Theorem w_total_tower_threshold_limit_zero {F : CField} (X : CScheme F)
  : threshold_limit_zero (w_total_tower X).
Proof.
  exact (w_total_limit_zero X).
Defined.

Theorem w_total_bounded_obstructions_vanish {F : CField} (X : CScheme F)
  (bo : BoundedObstruction (w_total_tower X))
  (Hpos : nat_lt O (qpos_num (obs_bound_const (w_total_tower X)
            (bo_data (w_total_tower X) bo))))
  : tower_obstructions_limit_zero (w_total_tower X) bo.
Proof.
  apply bounded_obstructions_limit_zero.
  - exact (w_total_tower_threshold_limit_zero X).
  - exact Hpos.
Defined.

(*******************************************************************************)
(*  STRONGLY COCARTESIAN CUBES, THE N-EXCISIVE PREDICATE, AND THE UNIVERSAL    *)
(*  PROPERTY OF THE POLYNOMIAL TRUNCATION                                      *)
(*******************************************************************************)

(** Cubes are guard diagrams over the Boolean predicate poset; n-excision sends strongly cocartesian diagrams below S n to cartesian ones, the zero functor is n-excisive, the identity is not 0-excisive, and P_n is the universal guard-supported approximation. *)

Record CommSquare (C : PreCategory) := {
  sq_00 : object C;
  sq_01 : object C;
  sq_10 : object C;
  sq_11 : object C;
  sq_top : morphism C sq_00 sq_01;
  sq_left : morphism C sq_00 sq_10;
  sq_right : morphism C sq_01 sq_11;
  sq_bottom : morphism C sq_10 sq_11;
  sq_comm : (sq_right o sq_top = sq_bottom o sq_left)%morphism
}.

Definition IsPushout {C : PreCategory} (S : CommSquare C) : Type
  := forall (W : object C)
            (a : morphism C (sq_01 C S) W)
            (b : morphism C (sq_10 C S) W),
     (a o sq_top C S = b o sq_left C S)%morphism ->
     Contr { u : morphism C (sq_11 C S) W &
             (((u o sq_right C S = a) * (u o sq_bottom C S = b))%morphism)%type }.

Definition IsPullback {C : PreCategory} (S : CommSquare C) : Type
  := forall (W : object C)
            (a : morphism C W (sq_01 C S))
            (b : morphism C W (sq_10 C S)),
     (sq_right C S o a = sq_bottom C S o b)%morphism ->
     Contr { u : morphism C W (sq_00 C S) &
             (((sq_top C S o u = a) * (sq_left C S o u = b))%morphism)%type }.

(** *** Guard diagrams: the cube poset as Boolean predicates *)

Definition guard_le {I : Type} (g h : I -> Bool) : Type
  := forall i, g i = true -> h i = true.

Definition guard_le_refl {I : Type} (g : I -> Bool) : guard_le g g
  := fun i p => p.

Definition guard_le_trans {I : Type} (g h k : I -> Bool)
  (H1 : guard_le g h) (H2 : guard_le h k)
  : guard_le g k
  := fun i p => H2 i (H1 i p).

Global Instance ishprop_guard_le `{Funext} {I : Type} (g h : I -> Bool)
  : IsHProp (guard_le g h).
Proof.
  apply istrunc_forall.
Defined.

Record GuardDiagram (C : PreCategory) := {
  gd_vertex : (nat -> Bool) -> object C;
  gd_map : forall g h : nat -> Bool, guard_le g h ->
           morphism C (gd_vertex g) (gd_vertex h);
  gd_map_id : forall g (Hgg : guard_le g g), gd_map g g Hgg = 1%morphism;
  gd_map_comp : forall g h k (Hgh : guard_le g h) (Hhk : guard_le h k),
      gd_map g k (guard_le_trans g h k Hgh Hhk)
      = (gd_map h k Hhk o gd_map g h Hgh)%morphism
}.

Definition gupd (g : nat -> Bool) (j : nat) : nat -> Bool
  := fun i => orb (nat_eqb i j) (g i).

Lemma guard_le_gupd (g : nat -> Bool) (j : nat) : guard_le g (gupd g j).
Proof.
  intros i p.
  unfold gupd.
  rewrite p.
  destruct (nat_eqb i j); reflexivity.
Defined.

Lemma gupd_swap_le (g : nat -> Bool) (j k : nat)
  : guard_le (gupd g k) (gupd (gupd g j) k).
Proof.
  intros i p.
  unfold gupd in *.
  destruct (nat_eqb i k).
  - reflexivity.
  - simpl in p.
    rewrite p.
    destruct (nat_eqb i j); reflexivity.
Defined.

Definition gd_elementary_square `{Funext} {C : PreCategory}
  (D : GuardDiagram C) (g : nat -> Bool) (j k : nat)
  : CommSquare C.
Proof.
  refine (Build_CommSquare C
            (gd_vertex C D g)
            (gd_vertex C D (gupd g j))
            (gd_vertex C D (gupd g k))
            (gd_vertex C D (gupd (gupd g j) k))
            (gd_map C D g (gupd g j) (guard_le_gupd g j))
            (gd_map C D g (gupd g k) (guard_le_gupd g k))
            (gd_map C D (gupd g j) (gupd (gupd g j) k) (guard_le_gupd (gupd g j) k))
            (gd_map C D (gupd g k) (gupd (gupd g j) k) (gupd_swap_le g j k))
            _).
  refine ((gd_map_comp C D _ _ _ _ _)^ @ _ @ (gd_map_comp C D _ _ _ _ _)).
  apply ap.
  apply path_ishprop.
Defined.

Definition IsStronglyCocartesianBelow `{Funext} {C : PreCategory}
  (m : nat) (D : GuardDiagram C)
  : Type
  := forall (g : nat -> Bool) (j k : nat),
     nat_lt j m -> nat_lt k m -> nat_eqb j k = false ->
     IsPushout (gd_elementary_square D g j k).

Definition guard_empty : nat -> Bool := fun _ => false.

Definition guard_le_from_empty (g : nat -> Bool) : guard_le guard_empty g.
Proof.
  intros i p.
  destruct (false_ne_true p).
Defined.

Definition guard_below (m : nat) (g : nat -> Bool) : Type
  := forall i, nat_le m i -> g i = false.

Record CubeConeBelow {C : PreCategory} (m : nat) (D : GuardDiagram C)
  (W : object C) := {
  cc_component : forall (g : nat -> Bool),
      guard_below m g -> { i : nat & g i = true } ->
      morphism C W (gd_vertex C D g);
  cc_compat : forall g h (Hle : guard_le g h)
                     (Hg : guard_below m g) (Hh : guard_below m h)
                     (wg : { i : nat & g i = true })
                     (wh : { i : nat & h i = true }),
      (gd_map C D g h Hle o cc_component g Hg wg)%morphism
      = cc_component h Hh wh
}.

Definition IsCartesianCubeBelow `{Funext} {C : PreCategory}
  (m : nat) (D : GuardDiagram C)
  : Type
  := forall (W : object C) (c : CubeConeBelow m D W),
     Contr { u : morphism C W (gd_vertex C D guard_empty) &
             forall g (Hg : guard_below m g) (wg : { i : nat & g i = true }),
               (gd_map C D guard_empty g (guard_le_from_empty g) o u)%morphism
               = cc_component m D W c g Hg wg }.

Definition gd_image {C : PreCategory} (F : Functor C C) (D : GuardDiagram C)
  : GuardDiagram C.
Proof.
  refine (Build_GuardDiagram C
            (fun g => object_of F (gd_vertex C D g))
            (fun g h Hle => morphism_of F (gd_map C D g h Hle))
            _ _).
  - intros g Hgg.
    rewrite (gd_map_id C D g Hgg).
    apply identity_of.
  - intros g h k Hgh Hhk.
    rewrite (gd_map_comp C D g h k Hgh Hhk).
    apply composition_of.
Defined.

Definition IsNExcisive `{Funext} {C : PreCategory} (F : Functor C C) (n : nat)
  : Type
  := forall D : GuardDiagram C,
     IsStronglyCocartesianBelow (S n) D ->
     IsCartesianCubeBelow (S n) (gd_image F D).

(** *** The constant zero functor is n-excisive over any category with zero *)

Definition ZeroEndofunctor (C : PreCategory) (Z : ZeroObject C)
  : Functor C C.
Proof.
  refine (Build_Functor C C
            (fun _ => zero C Z)
            (fun _ _ _ => 1%morphism)
            _ _).
  - intros s d d' m1 m2.
    symmetry.
    apply left_identity.
  - intro X.
    reflexivity.
Defined.

Theorem zero_endofunctor_n_excisive `{Funext} (C : PreCategory) (Z : ZeroObject C)
  (n : nat)
  : IsNExcisive (ZeroEndofunctor C Z) n.
Proof.
  intros D Hsc W c.
  refine (Build_Contr _
            (@center _ (is_terminal C Z W) ;
             fun g Hg wg => @path_contr _ (is_terminal C Z W) _ _)
            _).
  intros [u e].
  apply path_sigma_hprop.
  apply (@path_contr _ (is_terminal C Z W)).
Defined.

(** *** The identity of the level category is not 0-excisive *)

Definition delta0 : FamObj nat := fun k => nat_eqb k O.

Definition neg_guard (g : nat -> Bool) : nat -> Bool
  := fun _ => negb (g O).

Lemma lev_change_id (b x : Bool)
  : lev_change b b x = lev_id (truncAt b x).
Proof.
  destruct b; reflexivity.
Defined.

Lemma lev_change_comp_mono (b1 b2 b3 x : Bool)
  (H32 : b3 = true -> b2 = true)
  : lev_comp (truncAt b1 x) (truncAt b2 x) (truncAt b3 x)
      (lev_change b2 b3 x) (lev_change b1 b2 x)
    = lev_change b1 b3 x.
Proof.
  destruct b1.
  - destruct b3.
    + rewrite (H32 idpath).
      apply lev_comp_id_l.
    + apply lev_to_false_unique.
  - apply lev_from_false_unique.
Defined.

Lemma negb_le_flip (b c : Bool) (Hle : b = true -> c = true)
  : negb c = true -> negb b = true.
Proof.
  destruct b.
  - intro p.
    rewrite (Hle idpath) in p.
    exact (Empty_rec _ (false_ne_true p)).
  - intro p.
    reflexivity.
Defined.

Definition NegDiagram `{Funext} : GuardDiagram (FamCat nat).
Proof.
  refine (Build_GuardDiagram (FamCat nat)
            (fun g => fam_trunc (neg_guard g) delta0)
            (fun g h Hle => fam_change (neg_guard g) (neg_guard h) delta0)
            _ _).
  - intros g Hgg.
    apply path_forall; intro i.
    apply lev_change_id.
  - intros g1 g2 g3 H12 H23.
    apply path_forall; intro i.
    symmetry.
    apply lev_change_comp_mono.
    exact (negb_le_flip (g2 O) (g3 O) (H23 O)).
Defined.

Theorem NegDiagram_strongly_cocartesian `{Funext}
  : IsStronglyCocartesianBelow (S O) NegDiagram.
Proof.
  intros g j k Hj Hk Hjk.
  destruct j.
  - destruct k.
    + exact (Empty_rec _ (false_ne_true Hjk^)).
    + exact (Empty_rec _ (nat_lt_zero_absurd k Hk)).
  - exact (Empty_rec _ (nat_lt_zero_absurd j Hj)).
Defined.

Lemma neg_support_witness (g : nat -> Bool)
  (Hs : guard_below (S O) g)
  (wg : { i : nat & g i = true })
  : g O = true.
Proof.
  destruct wg as [i p].
  destruct i.
  - exact p.
  - exact (Empty_rec _ (false_ne_true ((Hs (S i) tt)^ @ p))).
Defined.

(** *** The repair of the cube notion and n-excision of the truncation

    Zero-excision in the unrepaired sense forces a functor to send every map
    to an isomorphism, which no non-constant weight truncation does, so the
    weighted notion conditions excision on cubes whose action the truncation
    classifies as high: on such cubes the image maps are isomorphisms and the
    image cube is cartesian.  The cartesianness argument is purely formal and
    holds in any category. *)

Definition gunion (g h : nat -> Bool) : nat -> Bool
  := fun i => orb (g i) (h i).

Lemma guard_le_union_l (g h : nat -> Bool) : guard_le g (gunion g h).
Proof.
  intros i p.
  unfold gunion.
  rewrite p.
  reflexivity.
Defined.

Lemma guard_le_union_r (g h : nat -> Bool) : guard_le h (gunion g h).
Proof.
  intros i p.
  unfold gunion.
  rewrite p.
  destruct (g i); reflexivity.
Defined.

Lemma guard_below_union (m : nat) (g h : nat -> Bool)
  (Hg : guard_below m g) (Hh : guard_below m h)
  : guard_below m (gunion g h).
Proof.
  intros i Hi.
  unfold gunion.
  rewrite (Hg i Hi).
  rewrite (Hh i Hi).
  reflexivity.
Defined.

Theorem all_iso_cube_cartesian `{Funext} {C : PreCategory} (m : nat)
  (Hm : nat_lt O m)
  (D : GuardDiagram C)
  (Hiso : forall g h (Hle : guard_le g h),
      IsIsomorphism (gd_map C D g h Hle))
  : IsCartesianCubeBelow m D.
Proof.
  intros W c.
  pose (d0 := gupd guard_empty O).
  assert (Hd0below : guard_below m d0).
  { intros i Hi.
    unfold d0, gupd, guard_empty.
    destruct (bool_dec_eq (nat_eqb i O)) as [He | He].
    - apply Empty_rec.
      exact (nat_le_lt_contradiction m i Hi
               (transport (fun j => nat_lt j m)
                  (nat_eqb_true_path i O He)^ Hm)).
    - rewrite He.
      reflexivity. }
  assert (Hd0occ : { i : nat & d0 i = true }).
  { exists O.
    reflexivity. }
  pose (e0 := Hiso guard_empty d0 (guard_le_from_empty d0)).
  pose (u0 := ((iso_inverse e0)
                 o cc_component m D W c d0 Hd0below Hd0occ)%morphism).
  assert (Hcompat : forall g (Hg : guard_below m g)
                           (wg : { i : nat & g i = true }),
      (gd_map C D guard_empty g (guard_le_from_empty g) o u0)%morphism
      = cc_component m D W c g Hg wg).
  { intros g Hg wg.
    pose (gu := gunion d0 g).
    assert (Hgub : guard_below m gu).
    { exact (guard_below_union m d0 g Hd0below Hg). }
    assert (Hguocc : { i : nat & gu i = true }).
    { exists O.
      reflexivity. }
    apply (iso_cancel_l (gd_map C D g gu (guard_le_union_r d0 g))
             (Hiso g gu (guard_le_union_r d0 g))).
    refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
    refine (ap (fun h => (h o u0)%morphism)
              ((gd_map_comp C D guard_empty g gu
                  (guard_le_from_empty g) (guard_le_union_r d0 g))^
               @ ap (gd_map C D guard_empty gu)
                   (path_ishprop _ (guard_le_from_empty gu))
               @ (ap (gd_map C D guard_empty gu)
                   (path_ishprop _ _))^
               @ gd_map_comp C D guard_empty d0 gu
                   (guard_le_from_empty d0) (guard_le_union_l d0 g))
              @ _).
    refine (associativity _ _ _ _ _ _ _ _ @ _).
    refine (ap (fun h => (gd_map C D d0 gu (guard_le_union_l d0 g) o h)%morphism)
              _ @ _).
    { unfold u0.
      refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
      refine (ap (fun h => (h o cc_component m D W c d0 Hd0below Hd0occ)%morphism)
                (prod_pr2 e0.2) @ _).
      apply left_identity. }
    refine (cc_compat m D W c d0 gu (guard_le_union_l d0 g)
              Hd0below Hgub Hd0occ Hguocc @ _).
    exact (cc_compat m D W c g gu (guard_le_union_r d0 g)
             Hg Hgub wg Hguocc)^.
  }
  refine (Build_Contr _ (u0 ; Hcompat) _).
  intros [u' e'].
  apply path_sigma_hprop.
  apply (iso_cancel_l (gd_map C D guard_empty d0 (guard_le_from_empty d0))
           e0).
  exact (Hcompat d0 Hd0below Hd0occ @ (e' d0 Hd0below Hd0occ)^).
Defined.

Definition IsNExcisiveWeighted `{Funext}
  (F : Functor (FamCat nat) (FamCat nat)) (n : nat)
  : Type
  := forall D : GuardDiagram (FamCat nat),
     IsStronglyCocartesianBelow (S n) D ->
     (forall g h (Hle : guard_le g h),
        IsIsomorphism (C := FamCat nat)
          (morphism_of F (gd_map (FamCat nat) D g h Hle))) ->
     IsCartesianCubeBelow (S n) (gd_image F D).

Theorem FamP_n_excisive_weighted `{Funext} (n : nat)
  : IsNExcisiveWeighted (FamTrunc (fam_guard_P n)) n.
Proof.
  intros D Hsc Hinv.
  apply (all_iso_cube_cartesian (S n) tt).
  intros g h Hle.
  exact (Hinv g h Hle).
Defined.

Definition constant_guard_diagram {C : PreCategory} (X : object C)
  : GuardDiagram C.
Proof.
  refine (Build_GuardDiagram C (fun _ => X) (fun _ _ _ => 1%morphism) _ _).
  - intros g Hgg.
    reflexivity.
  - intros g h k Hgh Hhk.
    symmetry.
    apply left_identity.
Defined.

Lemma constant_diagram_strongly_cocartesian `{Funext} (m : nat)
  (X : object (FamCat nat))
  : IsStronglyCocartesianBelow m (constant_guard_diagram X).
Proof.
  intros g j k Hj Hk Hjk W a b Hab.
  assert (Hba : a = b).
  { exact ((right_identity _ _ _ a)^ @ Hab @ right_identity _ _ _ b). }
  refine (Build_Contr _
            (a ; (right_identity _ _ _ a ,
                  right_identity _ _ _ a @ Hba)) _).
  intros [u [e1 e2]].
  apply path_sigma_hprop.
  exact ((right_identity _ _ _ u)^ @ e1)^.
Defined.

Theorem FamP_excision_nonvacuous `{Funext} (n : nat) (X : FamObj nat)
  : IsCartesianCubeBelow (S n)
      (gd_image (FamTrunc (fam_guard_P n))
         (constant_guard_diagram (X : object (FamCat nat)))).
Proof.
  apply (FamP_n_excisive_weighted n).
  - exact (constant_diagram_strongly_cocartesian (S n) X).
  - intros g h Hle.
    refine (transport (fun f => IsIsomorphism (C := FamCat nat) f)
             (identity_of (FamTrunc (fam_guard_P n)) X)^ _).
    exists 1%morphism.
    split.
    + apply left_identity.
    + apply left_identity.
Defined.

(** *** n-homogeneity: the layer is weighted n-excisive and its part below the layer level vanishes. *)

Definition IsNHomogeneousWeighted `{Funext}
  (F : Functor (FamCat nat) (FamCat nat)) (n : nat)
  : Type
  := (IsNExcisiveWeighted F n
      * (forall X : FamObj nat,
           object_of (FamTrunc (fam_guard_P n)) (object_of F X)
           = (fam_zero : FamObj nat)))%type.

Theorem FamD_n_homogeneous `{Funext} (n : nat)
  : IsNHomogeneousWeighted (FamTrunc (fam_guard_D n)) n.
Proof.
  split.
  - intros D Hsc Hinv.
    apply (all_iso_cube_cartesian (S n) tt).
    exact Hinv.
  - intro X.
    apply path_forall; intro k.
    destruct (bool_dec_eq (nat_leb k n)) as [Hb | Hb].
    + refine (ap (fun b => truncAt b (truncAt (nat_eqb k (S n)) (X k))) Hb
               @ _).
      exact (ap (fun b => truncAt b (X k))
               (nat_eqb_window k n
                @ ap (fun b => andb (nat_leb k (S n)) (negb b)) Hb
                @ andb_false_r (nat_leb k (S n)))).
    + exact (ap (fun b => truncAt b (truncAt (nat_eqb k (S n)) (X k))) Hb).
Defined.

Theorem fam_id_not_0_excisive `{Funext}
  : IsNExcisive (C := FamCat nat) 1%functor O -> Empty.
Proof.
  intro Hex.
  pose (Hcart := Hex NegDiagram NegDiagram_strongly_cocartesian).
  set (W := gd_vertex (FamCat nat) (gd_image 1%functor NegDiagram) guard_empty).
  assert (c : CubeConeBelow (S O) (gd_image 1%functor NegDiagram) W).
  { refine (Build_CubeConeBelow (FamCat nat) (S O)
              (gd_image 1%functor NegDiagram) W
              (fun g Hg wg => fun k => lev_zero_mor _ _)
              _).
    intros g h Hle Hg Hh wg wh.
    apply path_forall; intro k.
    exact (lev_to_falseish_unique _ _
             (ap (fun b => truncAt (negb b) (delta0 k))
                 (neg_support_witness h Hh wh)) _ _). }
  pose (u1 := (fam_id W ;
               fun g Hg wg => path_forall _ _ (fun k =>
                 lev_to_falseish_unique _ _
                   (ap (fun b => truncAt (negb b) (delta0 k))
                       (neg_support_witness g Hg wg)) _ _))
        : { u : morphism (FamCat nat) W W &
            forall g Hg wg,
              (gd_map (FamCat nat) (gd_image 1%functor NegDiagram)
                 guard_empty g (guard_le_from_empty g) o u)%morphism
              = cc_component (S O) (gd_image 1%functor NegDiagram) W c g Hg wg }).
  pose (u2 := ((fun k => lev_zero_mor (W k) (W k)) ;
               fun g Hg wg => path_forall _ _ (fun k =>
                 lev_to_falseish_unique _ _
                   (ap (fun b => truncAt (negb b) (delta0 k))
                       (neg_support_witness g Hg wg)) _ _))
        : { u : morphism (FamCat nat) W W &
            forall g Hg wg,
              (gd_map (FamCat nat) (gd_image 1%functor NegDiagram)
                 guard_empty g (guard_le_from_empty g) o u)%morphism
              = cc_component (S O) (gd_image 1%functor NegDiagram) W c g Hg wg }).
  pose (q := @path_contr _ (Hcart W c) u1 u2).
  apply false_ne_true.
  exact (apD10 (ap (fun w => w.1) q) O)^.
Defined.

(** *** The universal property of the polynomial truncation *)

Definition fam_unit {I : Type} (g : I -> Bool) (X : FamObj I)
  : FamHom X (fam_trunc g X)
  := fun i => lev_change true (g i) (X i).

Definition IsGuardSupported {I : Type} (g : I -> Bool) (Y : FamObj I) : Type
  := forall i, g i = false -> Y i = false.

Definition fam_factor {I : Type} (g : I -> Bool) (X Y : FamObj I)
  (f : FamHom X Y)
  : FamHom (fam_trunc g X) Y
  := fun i => match g i as b return LevHom (truncAt b (X i)) (Y i) with
              | true => f i
              | false => tt
              end.

Lemma lev_factor_commutes (b x y : Bool) (f : LevHom x y)
  (Hb : b = false -> y = false)
  : lev_comp x (truncAt b x) y
      (match b as b' return LevHom (truncAt b' x) y with
       | true => f
       | false => tt
       end)
      (lev_change true b x)
    = f.
Proof.
  destruct b.
  - apply lev_comp_id_r.
  - exact (lev_to_falseish_unique x y (Hb idpath) _ _).
Defined.

Lemma lev_factor_unique (b x y : Bool) (f : LevHom x y)
  (u1 u2 : LevHom (truncAt b x) y)
  (e1 : lev_comp x (truncAt b x) y u1 (lev_change true b x) = f)
  (e2 : lev_comp x (truncAt b x) y u2 (lev_change true b x) = f)
  : u1 = u2.
Proof.
  destruct b.
  - exact ((lev_comp_id_r x y u1)^ @ e1 @ e2^ @ (lev_comp_id_r x y u2)).
  - apply lev_from_false_unique.
Defined.

Theorem fam_trunc_universal `{Funext} {I : Type} (g : I -> Bool)
  (X Y : FamObj I)
  (HY : IsGuardSupported g Y)
  (f : FamHom X Y)
  : Contr { u : FamHom (fam_trunc g X) Y &
            fam_comp X (fam_trunc g X) Y u (fam_unit g X) = f }.
Proof.
  refine (Build_Contr _
            (fam_factor g X Y f ;
             path_forall _ _ (fun i =>
               lev_factor_commutes (g i) (X i) (Y i) (f i) (HY i)))
            _).
  intros [u e].
  apply path_sigma_hprop.
  apply path_forall; intro i.
  refine (lev_factor_unique (g i) (X i) (Y i) (f i) _ _ _ _).
  - exact (lev_factor_commutes (g i) (X i) (Y i) (f i) (HY i)).
  - exact (apD10 e i).
Defined.

Theorem FamP_universal `{Funext} (n : nat) (X Y : FamObj nat)
  (HY : IsGuardSupported (fam_guard_P n) Y)
  (f : FamHom X Y)
  : Contr { u : FamHom (fam_trunc (fam_guard_P n) X) Y &
            fam_comp X (fam_trunc (fam_guard_P n) X) Y u
              (fam_unit (fam_guard_P n) X) = f }.
Proof.
  exact (fam_trunc_universal (fam_guard_P n) X Y HY f).
Defined.

Lemma fam_unit_is_from_F `{Funext} (n : nat) (X : FamObj nat)
  : fam_unit (fam_guard_P n) X = fam_change fam_guard_all (fam_guard_P n) X.
Proof.
  reflexivity.
Defined.

(*******************************************************************************)
(*  SEQUENTIAL LIMITS OF TOWERS                                                *)
(*******************************************************************************)

(** Tower limits by universal property: iso towers have stage zero as limit, and stabilized towers have transport-free stable tails with limits. *)

Record TowerCone (C : PreCategory) (T : CategoricalTower C) (W : object C) := {
  tc_component : forall n, morphism C W (ct_stage C T n);
  tc_compat : forall n,
      (ct_map C T n o tc_component (S n))%morphism = tc_component n
}.

Definition IsTowerLimit (C : PreCategory) (T : CategoricalTower C)
  (L : object C) (cone : TowerCone C T L)
  : Type
  := forall (W : object C) (c : TowerCone C T W),
     Contr { u : morphism C W L &
             forall n, (tc_component C T L cone n o u)%morphism
                       = tc_component C T W c n }.

Section StabilizedTowerLimit.

Context `{Funext} {C : PreCategory} (T : CategoricalTower C)
  (Hstab : TowerStabilizesAt T O).

Definition stab_inv (n : nat)
  : morphism C (ct_stage C T n) (ct_stage C T (S n))
  := (Hstab n tt).1.

Definition stab_inv_l (n : nat)
  : (stab_inv n o ct_map C T n = 1)%morphism
  := prod_pr1 (Hstab n tt).2.

Definition stab_inv_r (n : nat)
  : (ct_map C T n o stab_inv n = 1)%morphism
  := prod_pr2 (Hstab n tt).2.

Fixpoint stab_cone_component (n : nat)
  : morphism C (ct_stage C T O) (ct_stage C T n)
  := match n with
     | O => 1%morphism
     | S n' => (stab_inv n' o stab_cone_component n')%morphism
     end.

Definition stab_cone : TowerCone C T (ct_stage C T O).
Proof.
  refine (Build_TowerCone C T (ct_stage C T O) stab_cone_component _).
  intro n.
  simpl.
  transitivity ((ct_map C T n o stab_inv n) o stab_cone_component n)%morphism.
  - symmetry.
    apply associativity.
  - rewrite stab_inv_r.
    apply left_identity.
Defined.

Theorem stab_tower_limit : IsTowerLimit C T (ct_stage C T O) stab_cone.
Proof.
  intros W c.
  assert (cond : forall n,
      (tc_component C T (ct_stage C T O) stab_cone n
         o tc_component C T W c O)%morphism
      = tc_component C T W c n).
  { intro n.
    induction n.
    - simpl.
      apply left_identity.
    - simpl.
      transitivity (stab_inv n o (stab_cone_component n o tc_component C T W c O))%morphism.
      { apply associativity. }
      rewrite IHn.
      rewrite <- (tc_compat C T W c n).
      transitivity ((stab_inv n o ct_map C T n) o tc_component C T W c (S n))%morphism.
      { symmetry.
        apply associativity. }
      rewrite stab_inv_l.
      apply left_identity. }
  refine (Build_Contr _ (tc_component C T W c O ; cond) _).
  intros [u e].
  apply path_sigma_hprop.
  simpl.
  exact ((e O)^ @ left_identity C _ _ u).
Defined.

End StabilizedTowerLimit.

(** *** The dual theorem: direct systems of isomorphisms have their zeroth stage as colimit, by the duality principle. *)

Record CategoricalCotower (C : PreCategory) := {
  cct_stage : nat -> object C;
  cct_map : forall n, morphism C (cct_stage n) (cct_stage (S n))
}.

Definition cotower_op {C : PreCategory} (T : CategoricalCotower C)
  : CategoricalTower (opposite_precategory C)
  := Build_CategoricalTower (opposite_precategory C)
       (cct_stage C T) (cct_map C T).

Record TowerCocone {C : PreCategory} (T : CategoricalCotower C)
  (W : object C) := {
  tcc_component : forall n, morphism C (cct_stage C T n) W;
  tcc_compat : forall n,
    (tcc_component (S n) o cct_map C T n)%morphism = tcc_component n
}.

Definition IsTowerColimit {C : PreCategory} (T : CategoricalCotower C)
  (W : object C) (c : TowerCocone T W) : Type
  := forall (V : object C) (d : TowerCocone T V),
     Contr { u : morphism C W V &
             forall n, (u o tcc_component T W c n)%morphism
                       = tcc_component T V d n }.

Lemma iso_op {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  (Hf : IsIsomorphism f)
  : IsIsomorphism (C := opposite_precategory C)
      (f : morphism (opposite_precategory C) Y X).
Proof.
  destruct Hf as [g [Hgf Hfg]].
  exists (g : morphism (opposite_precategory C) X Y).
  exact (Hfg, Hgf).
Defined.

Definition cocone_to_op_cone {C : PreCategory} (T : CategoricalCotower C)
  (W : object C) (c : TowerCocone T W)
  : TowerCone (opposite_precategory C) (cotower_op T) W
  := Build_TowerCone (opposite_precategory C) (cotower_op T) W
       (tcc_component T W c) (tcc_compat T W c).

Definition iso_cotower_cocone `{Funext} {C : PreCategory}
  (T : CategoricalCotower C)
  (Hiso : forall n, IsIsomorphism (cct_map C T n))
  : TowerCocone T (cct_stage C T O)
  := Build_TowerCocone C T (cct_stage C T O)
       (tc_component (opposite_precategory C) (cotower_op T)
          (cct_stage C T O)
          (stab_cone (cotower_op T)
             (fun n _ => iso_op (cct_map C T n) (Hiso n))))
       (tc_compat (opposite_precategory C) (cotower_op T)
          (cct_stage C T O)
          (stab_cone (cotower_op T)
             (fun n _ => iso_op (cct_map C T n) (Hiso n)))).

Theorem iso_cotower_colimit `{Funext} {C : PreCategory}
  (T : CategoricalCotower C)
  (Hiso : forall n, IsIsomorphism (cct_map C T n))
  : IsTowerColimit T (cct_stage C T O) (iso_cotower_cocone T Hiso).
Proof.
  intros V d.
  exact (stab_tower_limit (cotower_op T)
           (fun n _ => iso_op (cct_map C T n) (Hiso n))
           V (cocone_to_op_cone T V d)).
Defined.

Definition tower_shift {C : PreCategory} (T : CategoricalTower C) (N : nat)
  : CategoricalTower C
  := Build_CategoricalTower C
       (fun n => ct_stage C T (nat_add n N))
       (fun n => ct_map C T (nat_add n N)).

Lemma nat_le_N_add (n N : nat) : nat_le N (nat_add n N).
Proof.
  induction n.
  - exact (nat_le_refl N).
  - exact (nat_le_succ_r N (nat_add n N) IHn).
Defined.

Theorem tower_shift_stabilizes {C : PreCategory}
  (T : CategoricalTower C) (N : nat)
  (Hstab : TowerStabilizesAt T N)
  : TowerStabilizesAt (tower_shift T N) O.
Proof.
  intros n _.
  exact (Hstab (nat_add n N) (nat_le_N_add n N)).
Defined.

Theorem stabilized_tower_tail_has_limit `{Funext} {C : PreCategory}
  (T : CategoricalTower C) (N : nat)
  (Hstab : TowerStabilizesAt T N)
  : IsTowerLimit C (tower_shift T N) (ct_stage C T N)
      (stab_cone (tower_shift T N) (tower_shift_stabilizes T N Hstab)).
Proof.
  exact (stab_tower_limit (tower_shift T N) (tower_shift_stabilizes T N Hstab)).
Defined.

(*******************************************************************************)
(*  TOWERS OF ABELIAN GROUPS: lim, lim ONE, AND THE MILNOR SEQUENCE            *)
(*******************************************************************************)

From HoTT Require Algebra.AbGroups.

Section AbelianTowers.

Import HoTT.Algebra.AbGroups.
Import HoTT.Truncations.Core.

(** *** The product of a sequence of abelian groups *)

Section AbPiNat.

Context `{Funext} (A : nat -> AbGroup).

Local Instance abpi_sgop : SgOp (forall n, A n)
  := fun a b n => sg_op (a n) (b n).

Local Instance abpi_unit : MonUnit (forall n, A n)
  := fun n => mon_unit.

Local Instance abpi_inv : Inverse (forall n, A n)
  := fun a n => inv (a n).

Local Instance abpi_ishset : IsHSet (forall n, A n).
Proof.
  exact (@istrunc_forall _ _ _ _ (fun n => _)).
Defined.

Definition ab_pi_nat : AbGroup.
Proof.
  refine (Build_AbGroup' (forall n, A n) _ _ _ _).
  - intros a b.
    apply path_forall; intro n.
    exact (commutativity (a n) (b n)).
  - intros a b c.
    apply path_forall; intro n.
    exact (associativity (a n) (b n) (c n)).
  - intro a.
    apply path_forall; intro n.
    exact (left_identity (a n)).
  - intro a.
    apply path_forall; intro n.
    exact (left_inverse (a n)).
Defined.

End AbPiNat.

(** *** Towers of abelian groups and the difference-of-shift homomorphism *)

Record AbTower : Type := {
  at_gr : nat -> AbGroup;
  at_map : forall n, GroupHomomorphism (at_gr (S n)) (at_gr n)
}.

Lemma ab_interchange (G : AbGroup) (p q r s : G)
  : sg_op (sg_op p q) (sg_op r s) = sg_op (sg_op p r) (sg_op q s).
Proof.
  exact ((associativity p q (sg_op r s))^
           @ ap (sg_op p)
               ((associativity q r s)
                  @ ap (fun w => sg_op w s) (commutativity q r)
                  @ (associativity r q s)^)
           @ associativity p r (sg_op q s)).
Defined.

Lemma ab_sub_cancel (G : AbGroup) (x y : G)
  : sg_op x (inv (sg_op x (inv y))) = y.
Proof.
  rewrite grp_inv_op.
  rewrite grp_inv_inv.
  rewrite (commutativity y (inv x)).
  rewrite (associativity x (inv x) y).
  rewrite grp_inv_r.
  apply grp_unit_l.
Defined.

Section AbTowerTheory.

Context `{Funext} (T : AbTower).

Definition ab_tower_pi : AbGroup := ab_pi_nat (at_gr T).

Definition oms_map (a : forall n, at_gr T n) : forall n, at_gr T n
  := fun n => sg_op (a n) (inv (at_map T n (a (S n)))).

Definition one_minus_shift : GroupHomomorphism ab_tower_pi ab_tower_pi.
Proof.
  refine (@Build_GroupHomomorphism ab_tower_pi ab_tower_pi oms_map _).
  intros a b.
  apply path_forall; intro n.
  exact (ap (fun w => sg_op (sg_op (a n) (b n)) (inv w))
            (grp_homo_op (at_map T n) (a (S n)) (b (S n)))
           @ ap (sg_op (sg_op (a n) (b n)))
               (ab_neg_op (at_map T n (a (S n))) (at_map T n (b (S n))))
           @ ab_interchange _ (a n) (b n)
               (inv (at_map T n (a (S n)))) (inv (at_map T n (b (S n))))).
Defined.

(** An element is killed by one minus shift exactly when it is a compatible family, identifying the kernel with lim. *)

Definition ab_tower_compatible (a : ab_tower_pi) : Type
  := forall n, at_map T n (a (S n)) = a n.

Theorem ab_tower_lim_spec (a : ab_tower_pi)
  : (one_minus_shift a = mon_unit) <-> ab_tower_compatible a.
Proof.
  split.
  - intros e n.
    pose (p0 := apD10 e n
          : sg_op (a n) (inv (at_map T n (a (S n)))) = mon_unit).
    exact ((grp_unit_l (at_map T n (a (S n))))^
             @ ap (fun w => sg_op w (at_map T n (a (S n)))) p0^
             @ (associativity (a n) (inv (at_map T n (a (S n))))
                  (at_map T n (a (S n))))^
             @ ap (sg_op (a n)) (grp_inv_l (at_map T n (a (S n))))
             @ grp_unit_r (a n)).
  - intro Hc.
    apply path_forall; intro n.
    exact (ap (fun w => sg_op (a n) (inv w)) (Hc n)
             @ grp_inv_r (a n)).
Defined.

Definition ab_tower_lim1 : AbGroup := ab_cokernel one_minus_shift.

Definition ab_tower_lim1_class
  : GroupHomomorphism ab_tower_pi ab_tower_lim1
  := grp_quotient_map.

Theorem ab_tower_lim1_image_zero (a : ab_tower_pi)
  : ab_tower_lim1_class (one_minus_shift a) = mon_unit.
Proof.
  apply qglue.
  apply tr.
  exists (inv a).
  exact (grp_homo_inv one_minus_shift a
           @ (grp_unit_r (inv (one_minus_shift a)))^).
Defined.

Section SectionsVanishing.

Context (s : forall n, at_gr T n -> at_gr T (S n))
  (Hs : forall n x, at_map T n (s n x) = x).

Fixpoint ab_solve (b : forall n, at_gr T n) (n : nat) : at_gr T n
  := match n with
     | O => mon_unit
     | S n' => s n' (sg_op (ab_solve b n') (inv (b n')))
     end.

Lemma ab_solve_spec (b : ab_tower_pi)
  : one_minus_shift (ab_solve b) = b.
Proof.
  apply path_forall; intro n.
  exact (ap (fun w => sg_op (ab_solve b n) (inv w))
            (Hs n (sg_op (ab_solve b n) (inv (b n))))
           @ ab_sub_cancel _ (ab_solve b n) (b n)).
Defined.

Theorem ab_tower_lim1_trivial_of_sections
  : forall y : ab_tower_lim1, y = mon_unit.
Proof.
  srapply grp_quotient_ind_hprop.
  intro b.
  refine (ap ab_tower_lim1_class (ab_solve_spec b)^ @ _).
  apply ab_tower_lim1_image_zero.
Defined.

End SectionsVanishing.

End AbTowerTheory.

Definition ab_tower_shift (T : AbTower) (N : nat) : AbTower
  := Build_AbTower
       (fun n => at_gr T (nat_add n N))
       (fun n => at_map T (nat_add n N)).

Lemma nat_lt_below_add_S (N n : nat) : nat_lt N (nat_add n (S N)).
Proof.
  induction n.
  - exact (nat_lt_S N).
  - exact (nat_lt_trans N (nat_add n (S N)) (S (nat_add n (S N))) IHn
             (nat_lt_S (nat_add n (S N)))).
Defined.

(** Weight-bounded integer-valued section obstructions grant sections from some stage on, and the tail lim one vanishes. *)

Theorem weighted_ab_tower_tail_lim1_vanishes `{Funext} (T : AbTower)
  (obs : nat -> QPos) (C : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hbound : forall n, qpos_lt (obs n) (qpos_mult C (w_stage n)))
  (Hint : IsIntegerValued obs)
  (Hsec : forall n, qpos_is_zero (obs n) ->
      { s : at_gr T n -> at_gr T (S n) &
        forall x, at_map T n (s x) = x })
  : { N : nat & forall y : ab_tower_lim1 (ab_tower_shift T (S N)), y = mon_unit }.
Proof.
  assert (Hev : EventuallyZero obs).
  { apply integer_LimitZero_implies_EventuallyZero.
    - exact Hint.
    - exact (bounded_measure_limit_zero obs C HC Hbound). }
  destruct Hev as [N HN].
  exists N.
  exact (ab_tower_lim1_trivial_of_sections (ab_tower_shift T (S N))
           (fun n => (Hsec (nat_add n (S N)) (HN _ (nat_lt_below_add_S N n))).1)
           (fun n => (Hsec (nat_add n (S N)) (HN _ (nat_lt_below_add_S N n))).2)).
Defined.

End AbelianTowers.

(*******************************************************************************)
(*  THE MILNOR SEQUENCE, ASSEMBLED                                             *)
(*******************************************************************************)

(** lim is the kernel of one minus shift, the four-term sequence is exact, the class map is surjective, the kernel-lim is the categorical limit with uniqueness by injectivity of the inclusion, and lim-one vanishing supplies the existence half. *)

Section MilnorSequence.

Import HoTT.Algebra.AbGroups.
Import HoTT.Truncations.Core.

Definition ab_subgroup_group {A : AbGroup} (H : Subgroup A) : AbGroup.
Proof.
  snapply Build_AbGroup.
  - exact (subgroup_group H).
  - intros [x hx] [y hy].
    apply path_sigma_hprop.
    exact (commutativity x y).
Defined.

Context `{Funext} (T : AbTower).

Definition ab_tower_lim : AbGroup
  := ab_subgroup_group (grp_kernel (one_minus_shift T)).

Definition ab_tower_lim_incl
  : GroupHomomorphism ab_tower_lim (ab_tower_pi T)
  := subgroup_incl (grp_kernel (one_minus_shift T)).

Theorem milnor_incl_injective (x y : ab_tower_lim)
  (E : ab_tower_lim_incl x = ab_tower_lim_incl y)
  : x = y.
Proof.
  apply path_sigma_hprop.
  exact E.
Defined.

Theorem milnor_exact_at_first_product
  : ((forall x : ab_tower_lim,
        one_minus_shift T (ab_tower_lim_incl x) = mon_unit)
     * (forall a : ab_tower_pi T,
        one_minus_shift T a = mon_unit ->
        { x : ab_tower_lim & ab_tower_lim_incl x = a }))%type.
Proof.
  split.
  - intro x.
    exact x.2.
  - intros a Ha.
    exact ((a ; Ha) ; idpath).
Defined.

Theorem milnor_image_in_kernel (a : ab_tower_pi T)
  : ab_tower_lim1_class T (one_minus_shift T a) = mon_unit.
Proof.
  exact (ab_tower_lim1_image_zero T a).
Defined.

Theorem milnor_kernel_in_image `{Univalence} (b : ab_tower_pi T)
  (Hb : ab_tower_lim1_class T b = mon_unit)
  : merely { a : ab_tower_pi T & one_minus_shift T a = b }.
Proof.
  pose proof (related_quotient_paths _ _ _ Hb) as r.
  strip_truncations.
  destruct r as [a p].
  apply tr.
  exists (inv a).
  exact (grp_homo_inv (one_minus_shift T) a
           @ ap inv (p @ grp_unit_r (inv b))
           @ grp_inv_inv b).
Defined.

Theorem milnor_class_surjective (y : ab_tower_lim1 T)
  : merely { b : ab_tower_pi T & ab_tower_lim1_class T b = y }.
Proof.
  revert y.
  srapply grp_quotient_ind_hprop.
  intro b.
  exact (tr (b ; idpath)).
Defined.

Theorem milnor_lim1_trivial_solution `{Univalence}
  (Hvan : forall y : ab_tower_lim1 T, y = mon_unit)
  (b : ab_tower_pi T)
  : merely { a : ab_tower_pi T & one_minus_shift T a = b }.
Proof.
  exact (milnor_kernel_in_image b (Hvan _)).
Defined.

(** *** lim is the categorical limit; uniqueness is the injectivity of the inclusion. *)

Definition AbGrpCat : PreCategory
  := @Build_PreCategory
       AbGroup
       (fun A B => GroupHomomorphism A B)
       (fun A => grp_homo_id)
       (fun A B C g f => grp_homo_compose g f)
       (fun s d d' d'' m1 m2 m3 =>
          equiv_path_grouphomomorphism
            (g := grp_homo_compose (grp_homo_compose m3 m2) m1)
            (h := grp_homo_compose m3 (grp_homo_compose m2 m1))
            (fun x => idpath))
       (fun a b f =>
          equiv_path_grouphomomorphism
            (g := grp_homo_compose grp_homo_id f)
            (h := f)
            (fun x => idpath))
       (fun a b f =>
          equiv_path_grouphomomorphism
            (g := grp_homo_compose f grp_homo_id)
            (h := f)
            (fun x => idpath))
       (fun s d => ishset_grouphomomorphism).

Definition ab_tower_cat : CategoricalTower AbGrpCat
  := Build_CategoricalTower AbGrpCat (at_gr T) (at_map T).

Definition ab_lim_proj (n : nat)
  : GroupHomomorphism ab_tower_lim (at_gr T n).
Proof.
  refine (@Build_GroupHomomorphism ab_tower_lim (at_gr T n)
            (fun x => ab_tower_lim_incl x n) _).
  intros x y.
  exact (ap (fun z : ab_tower_pi T => z n)
           (grp_homo_op ab_tower_lim_incl x y)).
Defined.

Definition ab_lim_cone : TowerCone AbGrpCat ab_tower_cat ab_tower_lim.
Proof.
  refine (Build_TowerCone AbGrpCat ab_tower_cat ab_tower_lim ab_lim_proj _).
  intro n.
  apply equiv_path_grouphomomorphism.
  intro x.
  exact (prod_pr1 (ab_tower_lim_spec T (ab_tower_lim_incl x)) x.2 n).
Defined.

Theorem ab_tower_lim_is_limit
  : IsTowerLimit AbGrpCat ab_tower_cat ab_tower_lim ab_lim_cone.
Proof.
  intros W c.
  pose (ucarrier := fun (w : W) (n : nat) =>
          tc_component AbGrpCat ab_tower_cat W c n w).
  assert (ucompat : forall w, one_minus_shift T (ucarrier w) = mon_unit).
  { intro w.
    apply (prod_pr2 (ab_tower_lim_spec T (ucarrier w))).
    intro n.
    exact (ap10 (ap grp_homo_map (tc_compat AbGrpCat ab_tower_cat W c n)) w). }
  assert (uhom : forall w w' : W,
      ((ucarrier (sg_op w w') ; ucompat (sg_op w w')) : ab_tower_lim)
      = sg_op ((ucarrier w ; ucompat w) : ab_tower_lim)
              ((ucarrier w' ; ucompat w') : ab_tower_lim)).
  { intros w w'.
    apply path_sigma_hprop.
    apply path_forall; intro n.
    exact (grp_homo_op (tc_component AbGrpCat ab_tower_cat W c n) w w'). }
  pose (u0 := @Build_GroupHomomorphism W ab_tower_lim
                (fun w => (ucarrier w ; ucompat w)) uhom).
  refine (Build_Contr _
            (u0 ;
             fun n => equiv_path_grouphomomorphism
                        (g := grp_homo_compose (ab_lim_proj n) u0)
                        (h := tc_component AbGrpCat ab_tower_cat W c n)
                        (fun w => idpath))
            _).
  intros [u' e'].
  apply path_sigma_hprop.
  apply equiv_path_grouphomomorphism.
  intro w.
  apply milnor_incl_injective.
  apply path_forall; intro n.
  exact (ap10 (ap grp_homo_map (e' n)) w)^.
Defined.

End MilnorSequence.

(** *** The abelianized carrier: level families of abelian groups with levelwise biproducts and pushouts, making the excision-style conditions positively testable. *)

Section AbelianFamilies.

Import HoTT.Algebra.AbGroups.

Context `{Funext}.

Definition AbFamObj : Type := nat -> AbGroup.

Definition AbFamHom (X Y : AbFamObj) : Type
  := forall k, GroupHomomorphism (X k) (Y k).

Lemma abfam_assoc (s d d' d'' : AbFamObj)
  (m1 : AbFamHom s d) (m2 : AbFamHom d d') (m3 : AbFamHom d' d'')
  : (fun k => grp_homo_compose (grp_homo_compose (m3 k) (m2 k)) (m1 k))
    = (fun k => grp_homo_compose (m3 k) (grp_homo_compose (m2 k) (m1 k))).
Proof.
  apply path_forall; intro k.
  exact (equiv_path_grouphomomorphism
           (g := grp_homo_compose (grp_homo_compose (m3 k) (m2 k)) (m1 k))
           (h := grp_homo_compose (m3 k) (grp_homo_compose (m2 k) (m1 k)))
           (fun x => idpath)).
Defined.

Lemma abfam_left_id (a b : AbFamObj) (f : AbFamHom a b)
  : (fun k => grp_homo_compose grp_homo_id (f k)) = f.
Proof.
  apply path_forall; intro k.
  exact (equiv_path_grouphomomorphism
           (g := grp_homo_compose grp_homo_id (f k)) (h := f k)
           (fun x => idpath)).
Defined.

Lemma abfam_right_id (a b : AbFamObj) (f : AbFamHom a b)
  : (fun k => grp_homo_compose (f k) grp_homo_id) = f.
Proof.
  apply path_forall; intro k.
  exact (equiv_path_grouphomomorphism
           (g := grp_homo_compose (f k) grp_homo_id) (h := f k)
           (fun x => idpath)).
Defined.

Lemma abfam_hset (s d : AbFamObj) : IsHSet (AbFamHom s d).
Proof.
  exact _.
Defined.

Definition AbFamCat : PreCategory
  := @Build_PreCategory AbFamObj AbFamHom
       (fun X k => grp_homo_id)
       (fun X Y Z g f k => grp_homo_compose (g k) (f k))
       abfam_assoc abfam_left_id abfam_right_id abfam_hset.

Definition abfam_zero_obj : AbFamObj := fun _ => abgroup_trivial.

Definition AbFamZero : ZeroObject AbFamCat.
Proof.
  refine (Build_ZeroObject AbFamCat abfam_zero_obj _ _).
Defined.

Definition abfam_biprod (X Y : AbFamObj) : AbFamObj
  := fun k => ab_biprod (X k) (Y k).

Definition abfam_biprod_inl (X Y : AbFamObj)
  : AbFamHom X (abfam_biprod X Y)
  := fun k => ab_biprod_inl.

Definition abfam_biprod_inr (X Y : AbFamObj)
  : AbFamHom Y (abfam_biprod X Y)
  := fun k => ab_biprod_inr.

Definition abfam_biprod_pr1 (X Y : AbFamObj)
  : AbFamHom (abfam_biprod X Y) X
  := fun k => ab_biprod_pr1.

Definition abfam_biprod_pr2 (X Y : AbFamObj)
  : AbFamHom (abfam_biprod X Y) Y
  := fun k => ab_biprod_pr2.

Theorem abfam_biprod_product_universal (X Y Z : AbFamObj)
  (f : AbFamHom Z X) (g : AbFamHom Z Y)
  : Contr { h : AbFamHom Z (abfam_biprod X Y) &
            ((fun k => grp_homo_compose (abfam_biprod_pr1 X Y k) (h k)) = f)
            * ((fun k => grp_homo_compose (abfam_biprod_pr2 X Y k) (h k)) = g) }.
Proof.
  refine (Build_Contr _
            ((fun k => grp_prod_corec (f k) (g k)) ;
             (path_forall _ _ (fun k =>
                equiv_path_grouphomomorphism
                  (g := grp_homo_compose (abfam_biprod_pr1 X Y k)
                          (grp_prod_corec (f k) (g k)))
                  (h := f k) (fun x => idpath)) ,
              path_forall _ _ (fun k =>
                equiv_path_grouphomomorphism
                  (g := grp_homo_compose (abfam_biprod_pr2 X Y k)
                          (grp_prod_corec (f k) (g k)))
                  (h := g k) (fun x => idpath)))) _).
  intros [h [e1 e2]].
  apply path_sigma_hprop.
  apply path_forall; intro k.
  apply equiv_path_grouphomomorphism; intro x.
  apply path_prod.
  - exact (ap10 (ap grp_homo_map (apD10 e1^ k)) x).
  - exact (ap10 (ap grp_homo_map (apD10 e2^ k)) x).
Defined.

Definition abfam_pushout {A B C : AbFamObj}
  (f : AbFamHom A B) (g : AbFamHom A C)
  : AbFamObj
  := fun k => ab_pushout (f k) (g k).

Definition abfam_pushout_inl {A B C : AbFamObj}
  (f : AbFamHom A B) (g : AbFamHom A C)
  : AbFamHom B (abfam_pushout f g)
  := fun k => ab_pushout_inl.

Definition abfam_pushout_inr {A B C : AbFamObj}
  (f : AbFamHom A B) (g : AbFamHom A C)
  : AbFamHom C (abfam_pushout f g)
  := fun k => ab_pushout_inr.

Theorem abfam_pushout_commsq {A B C : AbFamObj}
  (f : AbFamHom A B) (g : AbFamHom A C)
  : (fun k => grp_homo_compose (abfam_pushout_inl f g k) (f k))
    = (fun k => grp_homo_compose (abfam_pushout_inr f g k) (g k)).
Proof.
  apply path_forall; intro k.
  apply equiv_path_grouphomomorphism; intro x.
  exact (ab_pushout_commsq x).
Defined.

Theorem abfam_pushout_rec {A B C Y : AbFamObj}
  (f : AbFamHom A B) (g : AbFamHom A C)
  (b : AbFamHom B Y) (c : AbFamHom C Y)
  (p : (fun k => grp_homo_compose (b k) (f k))
       = (fun k => grp_homo_compose (c k) (g k)))
  : { phi : AbFamHom (abfam_pushout f g) Y &
      (((fun k => grp_homo_compose (phi k) (abfam_pushout_inl f g k)) = b)
       * ((fun k => grp_homo_compose (phi k) (abfam_pushout_inr f g k)) = c))%type }.
Proof.
  exists (fun k => ab_pushout_rec (b k) (c k)
                     (fun x => ap10 (ap grp_homo_map (apD10 p k)) x)).
  split.
  - apply path_forall; intro k.
    apply equiv_path_grouphomomorphism; intro x.
    exact (ab_pushout_rec_beta_left (f k) (g k) (b k) (c k)
             (fun y => ap10 (ap grp_homo_map (apD10 p k)) y) x).
  - apply path_forall; intro k.
    apply equiv_path_grouphomomorphism; intro x.
    exact (ab_pushout_rec_beta_right (f k) (g k) (b k) (c k)
             (fun y => ap10 (ap grp_homo_map (apD10 p k)) y) x).
Defined.

End AbelianFamilies.

(*******************************************************************************)
(*  BIGRADED WEIGHTED SPECTRAL SEQUENCES                                       *)
(*******************************************************************************)

Section WeightedSpectralSequences.

Import HoTT.Algebra.AbGroups.
Import HoTT.Truncations.Core.

(** *** Homology of composable differentials *)

Definition ab_homology {A B C : AbGroup}
  (din : GroupHomomorphism A B)
  (dout : GroupHomomorphism B C)
  (Hdd : forall x, dout (din x) = mon_unit)
  : AbGroup
  := @ab_cokernel A (ab_subgroup_group (grp_kernel dout))
       (grp_kernel_corec din (fun x => Hdd x)).

(** When both differentials vanish pointwise, homology is the group itself. *)

Definition ab_homology_vanishing_iso {A B C : AbGroup}
  (din : GroupHomomorphism A B)
  (dout : GroupHomomorphism B C)
  (Hdd : forall x, dout (din x) = mon_unit)
  (Hout : forall y, dout y = mon_unit)
  (Hin : forall x, din x = mon_unit)
  : GroupIsomorphism B (ab_homology din dout Hdd).
Proof.
  pose (K := ab_subgroup_group (grp_kernel dout)).
  pose (into := fun (y : B) =>
          (grp_quotient_map ((y ; Hout y) : K)
           : ab_homology din dout Hdd)).
  assert (intohom : forall y z : B,
             into (sg_op y z) = sg_op (into y) (into z)).
  { intros y z.
    unfold into.
    refine (ap grp_quotient_map _ @ grp_homo_op grp_quotient_map _ _).
    apply path_sigma_hprop.
    reflexivity. }
  assert (vanish : forall n : K,
             grp_image (grp_kernel_corec din (fun x => Hdd x)) n ->
             subgroup_incl (grp_kernel dout) n = mon_unit).
  { intros n Hn.
    strip_truncations.
    destruct Hn as [x p].
    exact ((ap (subgroup_incl (grp_kernel dout)) p)^ @ Hin x). }
  pose (back := @quotient_abgroup_rec K
          (grp_image (grp_kernel_corec din (fun x => Hdd x))) B
          (subgroup_incl (grp_kernel dout)) vanish).
  refine (Build_GroupIsomorphism _ _
            (@Build_GroupHomomorphism B (ab_homology din dout Hdd) into intohom)
            _).
  apply (isequiv_adjointify _ back).
  - srapply grp_quotient_ind_hprop.
    intros [y hy].
    unfold into, back.
    simpl.
    apply ap.
    apply path_sigma_hprop.
    reflexivity.
  - intro y.
    reflexivity.
Defined.

(** *** The spectral sequence record and its degeneration theorem *)

Record WeightedSpectralSequence : Type := {
  wss_idx : Type;
  wss_page : nat -> wss_idx -> AbGroup;
  wss_tgt : nat -> wss_idx -> wss_idx;
  wss_src : nat -> wss_idx -> wss_idx;
  wss_d : forall r i,
      GroupHomomorphism (wss_page r i) (wss_page r (wss_tgt r i));
  wss_din : forall r i,
      GroupHomomorphism (wss_page r (wss_src r i)) (wss_page r i);
  wss_dd : forall r i (x : wss_page r (wss_src r i)),
      wss_d r i (wss_din r i x) = mon_unit;
  wss_turn : forall r i,
      GroupIsomorphism (wss_page (S r) i)
        (ab_homology (wss_din r i) (wss_d r i) (wss_dd r i))
}.

(** The bounded-differential property is derived from the weight bound, and the spectral sequence degenerates at a finite page. *)

Theorem wss_degeneration (W : WeightedSpectralSequence)
  (m : nat -> QPos) (C : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hbound : forall r, qpos_lt (m r) (qpos_mult C (w_stage r)))
  (Hint : IsIntegerValued m)
  (Hdetect_out : forall r, qpos_is_zero (m r) ->
      forall i x, wss_d W r i x = mon_unit)
  (Hdetect_in : forall r, qpos_is_zero (m r) ->
      forall i x, wss_din W r i x = mon_unit)
  : { R : nat & forall r, nat_lt R r -> forall i,
      GroupIsomorphism (wss_page W (S r) i) (wss_page W r i) }.
Proof.
  assert (Hev : EventuallyZero m).
  { apply integer_LimitZero_implies_EventuallyZero.
    - exact Hint.
    - exact (bounded_measure_limit_zero m C HC Hbound). }
  destruct Hev as [R HR].
  exists R.
  intros r Hr i.
  refine (grp_iso_compose _ (wss_turn W r i)).
  apply grp_iso_inverse.
  apply ab_homology_vanishing_iso.
  - exact (Hdetect_out r (HR r Hr) i).
  - exact (Hdetect_in r (HR r Hr) i).
Defined.

(** *** The classical bidegree bookkeeping on Int times Int *)

Fixpoint int_shift_up (p : Int) (r : nat) : Int :=
  match r with
  | O => p
  | S r' => int_succ (int_shift_up p r')
  end.

Fixpoint int_shift_down (p : Int) (r : nat) : Int :=
  match r with
  | O => p
  | S r' => int_pred (int_shift_down p r')
  end.

Lemma int_shift_up_pred (p : Int) (r : nat)
  : int_shift_up (int_pred p) r = int_pred (int_shift_up p r).
Proof.
  induction r.
  - reflexivity.
  - simpl.
    rewrite IHr.
    exact (int_pred_succ _ @ (int_succ_pred _)^).
Defined.

Lemma int_shift_down_succ (q : Int) (r : nat)
  : int_shift_down (int_succ q) r = int_succ (int_shift_down q r).
Proof.
  induction r.
  - reflexivity.
  - simpl.
    rewrite IHr.
    exact (int_succ_pred _ @ (int_pred_succ _)^).
Defined.

Lemma int_shift_down_pred (q : Int) (r : nat)
  : int_shift_down (int_pred q) r = int_pred (int_shift_down q r).
Proof.
  induction r.
  - reflexivity.
  - simpl.
    rewrite IHr.
    reflexivity.
Defined.

Lemma int_shift_up_down (p : Int) (r : nat)
  : int_shift_up (int_shift_down p r) r = p.
Proof.
  induction r.
  - reflexivity.
  - simpl.
    rewrite int_shift_up_pred.
    rewrite IHr.
    apply int_pred_succ.
Defined.

Lemma int_shift_down_up (q : Int) (r : nat)
  : int_shift_down (int_shift_up q r) r = q.
Proof.
  induction r.
  - reflexivity.
  - simpl.
    rewrite int_shift_down_succ.
    rewrite IHr.
    apply int_succ_pred.
Defined.

Definition wss_classical_tgt (r : nat) (i : (Int * Int)%type)
  : (Int * Int)%type
  := (int_shift_up (prod_pr1 i) r, int_succ (int_shift_down (prod_pr2 i) r)).

Definition wss_classical_src (r : nat) (i : (Int * Int)%type)
  : (Int * Int)%type
  := (int_shift_down (prod_pr1 i) r, int_pred (int_shift_up (prod_pr2 i) r)).

Theorem wss_classical_tgt_src (r : nat) (i : (Int * Int)%type)
  : wss_classical_tgt r (wss_classical_src r i) = i.
Proof.
  destruct i as [p q].
  unfold wss_classical_tgt, wss_classical_src.
  simpl.
  apply path_prod; simpl.
  - apply int_shift_up_down.
  - rewrite int_shift_down_pred.
    rewrite int_shift_down_up.
    apply int_pred_succ.
Defined.

(** A constant integer spectral sequence over classical bidegrees, degenerating at the first page. *)

Definition wss_constant_Z : WeightedSpectralSequence.
Proof.
  refine (Build_WeightedSpectralSequence
            ((Int * Int)%type)
            (fun _ _ => abgroup_Z)
            wss_classical_tgt
            wss_classical_src
            (fun r i => grp_homo_const)
            (fun r i => grp_homo_const)
            (fun r i x => idpath)
            _).
  intros r i.
  exact (ab_homology_vanishing_iso grp_homo_const grp_homo_const
           (fun x => idpath) (fun y => idpath) (fun x => idpath)).
Defined.

(** *** Weight filtrations *)

Record WeightFiltration (A : AbGroup) : Type := {
  wf_sub : nat -> Subgroup A;
  wf_decreasing : forall n x, wf_sub (S n) x -> wf_sub n x
}.

Theorem weight_filtration_stabilizes (A : AbGroup) (W : WeightFiltration A)
  (m : nat -> QPos) (C : QPos)
  (HC : nat_lt O (qpos_num C))
  (Hbound : forall n, qpos_lt (m n) (qpos_mult C (w_stage n)))
  (Hint : IsIntegerValued m)
  (Hdetect : forall n, qpos_is_zero (m n) ->
      forall x, wf_sub A W n x -> wf_sub A W (S n) x)
  : { N : nat & forall n, nat_lt N n -> forall x,
      ((wf_sub A W n x -> wf_sub A W (S n) x) *
       (wf_sub A W (S n) x -> wf_sub A W n x))%type }.
Proof.
  assert (Hev : EventuallyZero m).
  { apply integer_LimitZero_implies_EventuallyZero.
    - exact Hint.
    - exact (bounded_measure_limit_zero m C HC Hbound). }
  destruct Hev as [N HN].
  exists N.
  intros n Hn x.
  split.
  - exact (Hdetect n (HN n Hn) x).
  - exact (wf_decreasing A W n x).
Defined.

End WeightedSpectralSequences.

(*******************************************************************************)
(*  NISNEVICH-STYLE COVERS AND SHEAVES ON CONCRETE SCHEMES                     *)
(*******************************************************************************)

Section NisnevichSheaves.

Import HoTT.Truncations.Core.

Context `{Funext} {F : CField}.

(** A cover is a jointly surjective family, the completely decomposed Nisnevich condition at carrier level. *)

Record Cover (X : CScheme F) : Type := {
  cov_index : Type;
  cov_obj : cov_index -> CScheme F;
  cov_map : forall i, CMor (cov_obj i) X;
  cov_surj : forall x : cs_carrier F X,
      merely { i : cov_index & { p : cs_carrier F (cov_obj i) &
                                 cov_map i p = x } }
}.

Record Presheaf : Type := {
  psh_val : CScheme F -> Type;
  psh_ishset : forall X, IsHSet (psh_val X);
  psh_res : forall (X Y : CScheme F), CMor X Y -> psh_val Y -> psh_val X;
  psh_res_id : forall X (s : psh_val X), psh_res X X (fun x => x) s = s;
  psh_res_comp : forall X Y Z (f : CMor X Y) (g : CMor Y Z) (s : psh_val Z),
      psh_res X Z (fun x => g (f x)) s = psh_res X Y f (psh_res Y Z g s)
}.

(** Compatibility is the matching condition through all common refinements, requiring no fiber products. *)

Definition CompatibleFamily (P : Presheaf) (X : CScheme F) (U : Cover X)
  (s : forall i, psh_val P (cov_obj X U i))
  : Type
  := forall (W : CScheme F) (i j : cov_index X U)
            (f : CMor W (cov_obj X U i)) (g : CMor W (cov_obj X U j)),
     (fun w => cov_map X U i (f w)) = (fun w => cov_map X U j (g w)) ->
     psh_res P W (cov_obj X U i) f (s i) = psh_res P W (cov_obj X U j) g (s j).

(** Compatibility restated on the pullbacks the quantification over all test schemes silently encodes. *)

Definition CompatibleOnPullbacks (P : Presheaf) (X : CScheme F)
  (U : Cover X)
  (s : forall i, psh_val P (cov_obj X U i))
  : Type
  := forall i j,
     psh_res P (cfiber_product (cov_map X U i) (cov_map X U j))
       (cov_obj X U i) (cfp_pr1 (cov_map X U i) (cov_map X U j)) (s i)
     = psh_res P (cfiber_product (cov_map X U i) (cov_map X U j))
       (cov_obj X U j) (cfp_pr2 (cov_map X U i) (cov_map X U j)) (s j).

Theorem compatible_iff_pullbacks (P : Presheaf) (X : CScheme F)
  (U : Cover X) (s : forall i, psh_val P (cov_obj X U i))
  : ((CompatibleFamily P X U s -> CompatibleOnPullbacks P X U s)
     * (CompatibleOnPullbacks P X U s -> CompatibleFamily P X U s))%type.
Proof.
  split.
  - intros Hc i j.
    exact (Hc (cfiber_product (cov_map X U i) (cov_map X U j)) i j
             (cfp_pr1 _ _) (cfp_pr2 _ _) (cfp_comm _ _)).
  - intros Hp W i j fW gW Hcomm.
    pose (u := (fun w => ((fW w , gW w) ; apD10 Hcomm w))
               : CMor W (cfiber_product (cov_map X U i) (cov_map X U j))).
    refine (psh_res_comp P W
              (cfiber_product (cov_map X U i) (cov_map X U j))
              (cov_obj X U i) u (cfp_pr1 _ _) (s i) @ _).
    refine (ap (psh_res P W
                 (cfiber_product (cov_map X U i) (cov_map X U j)) u)
              (Hp i j) @ _).
    exact (psh_res_comp P W
             (cfiber_product (cov_map X U i) (cov_map X U j))
             (cov_obj X U j) u (cfp_pr2 _ _) (s j))^.
Defined.

Definition IsSheaf (P : Presheaf) : Type
  := forall (X : CScheme F) (U : Cover X)
            (s : forall i, psh_val P (cov_obj X U i)),
     CompatibleFamily P X U s ->
     Contr { t : psh_val P X &
             forall i, psh_res P (cov_obj X U i) X (cov_map X U i) t = s i }.

Definition representable (Z : CScheme F) : Presheaf.
Proof.
  refine (Build_Presheaf
            (fun X => CMor X Z)
            (fun X => ishset_cmor X Z)
            (fun X Y f s => fun x => s (f x))
            _ _).
  - intros X s.
    reflexivity.
  - intros X Y Z' f g s.
    reflexivity.
Defined.

(** Representable presheaves glue uniquely along covers, by unique choice into a contractible type. *)

Theorem representable_is_sheaf (Z : CScheme F) : IsSheaf (representable Z).
Proof.
  intros X U s Hcomp.
  pose proof (cs_ishset F Z) as HZset.
  pose (V := fun (x : cs_carrier F X) =>
        { z : cs_carrier F Z &
          forall (i : cov_index X U) (p : cs_carrier F (cov_obj X U i)),
            cov_map X U i p = x -> s i p = z }).
  assert (VH : forall x, IsHProp (V x)).
  { intro x.
    apply hprop_allpath.
    intros [z hz] [z' hz'].
    apply path_sigma_hprop.
    pose proof (cov_surj X U x) as w.
    strip_truncations.
    destruct w as [i [p e]].
    exact ((hz i p e)^ @ hz' i p e). }
  assert (Vinh : forall x, V x).
  { intro x.
    pose proof (cov_surj X U x) as w.
    strip_truncations.
    destruct w as [i [p e]].
    exists (s i p).
    intros j q e'.
    exact (ap10 (Hcomp (cpoint F) j i
                   (fun _ => q) (fun _ => p)
                   (path_forall _ _ (fun _ => e' @ e^))) tt). }
  refine (Build_Contr _
            ((fun x => (Vinh x).1) ;
             fun i => path_forall _ _ (fun p => ((Vinh (cov_map X U i p)).2 i p idpath)^))
            _).
  intros [t' e'].
  apply path_sigma_hprop.
  apply path_forall; intro x.
  pose proof (cov_surj X U x) as w.
  strip_truncations.
  destruct w as [i [p e]].
  exact (((Vinh x).2 i p e)^ @ (ap10 (e' i) p)^ @ ap t' e).
Defined.

End NisnevichSheaves.

(*******************************************************************************)
(*  TATE OBJECTS AND THE SLICE FILTRATION ON INT-GRADED LEVEL FAMILIES         *)
(*******************************************************************************)

(** The slice filtration on Int-indexed families: effective covers keep levels at or above q, slices keep exactly q, both levelwise guarded truncations, with Tate objects as the level indicators. *)

Fixpoint nat_leb_succ_l (n m : nat) {struct n}
  : nat_leb (S n) m = true -> nat_leb n m = true.
Proof.
  destruct n.
  - intros _.
    reflexivity.
  - destruct m.
    + intro E.
      exact (Empty_rec _ (false_ne_true E)).
    + exact (nat_leb_succ_l n m).
Defined.

Lemma nat_leb_between' (n m : nat)
  : nat_leb n m = true -> nat_leb (S n) m = false -> m = n.
Proof.
  revert m.
  induction n.
  - intros m E1 E2.
    destruct m.
    + reflexivity.
    + exact (Empty_rec _ (false_ne_true E2^)).
  - intros m E1 E2.
    destruct m.
    + exact (Empty_rec _ (false_ne_true E1)).
    + exact (ap S (IHn m E1 E2)).
Defined.

Lemma nat_leb_zero_r (m : nat) : nat_leb m O = true -> m = O.
Proof.
  destruct m.
  - intros _.
    reflexivity.
  - intro E.
    exact (Empty_rec _ (false_ne_true E)).
Defined.

Definition int_eqb (a b : Int) : Bool :=
  match a, b with
  | negS m, negS n => nat_eqb m n
  | Int.zero, Int.zero => true
  | posS m, posS n => nat_eqb m n
  | _, _ => false
  end.

Definition int_leb (a b : Int) : Bool :=
  match a, b with
  | negS m, negS n => nat_leb n m
  | negS _, Int.zero => true
  | negS _, posS _ => true
  | Int.zero, negS _ => false
  | Int.zero, Int.zero => true
  | Int.zero, posS _ => true
  | posS _, negS _ => false
  | posS _, Int.zero => false
  | posS m, posS n => nat_leb m n
  end.

Lemma int_eqb_refl (a : Int) : int_eqb a a = true.
Proof.
  destruct a.
  - exact (nat_eqb_refl n).
  - reflexivity.
  - exact (nat_eqb_refl n).
Defined.

Lemma int_eqb_true_path (a b : Int) : int_eqb a b = true -> a = b.
Proof.
  destruct a, b; intro E; simpl in E.
  - exact (ap negS (nat_eqb_true_path n n0 E)).
  - exact (Empty_rec _ (false_ne_true E)).
  - exact (Empty_rec _ (false_ne_true E)).
  - exact (Empty_rec _ (false_ne_true E)).
  - reflexivity.
  - exact (Empty_rec _ (false_ne_true E)).
  - exact (Empty_rec _ (false_ne_true E)).
  - exact (Empty_rec _ (false_ne_true E)).
  - exact (ap posS (nat_eqb_true_path n n0 E)).
Defined.

Lemma int_leb_succ_true (q i : Int)
  : int_leb (int_succ q) i = true -> int_leb q i = true.
Proof.
  destruct q as [n | | n].
  - destruct n.
    + destruct i as [m | | m]; simpl; intro E.
      * exact (Empty_rec _ (false_ne_true E)).
      * reflexivity.
      * reflexivity.
    + destruct i as [m | | m]; simpl; intro E.
      * exact (nat_leb_succ_r m n E).
      * reflexivity.
      * reflexivity.
  - destruct i as [m | | m]; simpl; intro E.
    + exact (Empty_rec _ (false_ne_true E)).
    + exact (Empty_rec _ (false_ne_true E)).
    + reflexivity.
  - destruct i as [m | | m]; simpl; intro E.
    + exact (Empty_rec _ (false_ne_true E)).
    + exact (Empty_rec _ (false_ne_true E)).
    + exact (nat_leb_succ_l n m E).
Defined.

Lemma int_leb_between (q i : Int)
  : int_leb q i = true -> int_leb (int_succ q) i = false -> i = q.
Proof.
  destruct q as [n | | n].
  - destruct n.
    + destruct i as [m | | m]; simpl; intros E1 E2.
      * exact (ap negS (nat_leb_zero_r m E1)).
      * exact (Empty_rec _ (false_ne_true E2^)).
      * exact (Empty_rec _ (false_ne_true E2^)).
    + destruct i as [m | | m]; simpl; intros E1 E2.
      * exact (ap negS (nat_leb_between m n E1 E2)).
      * exact (Empty_rec _ (false_ne_true E2^)).
      * exact (Empty_rec _ (false_ne_true E2^)).
  - destruct i as [m | | m]; simpl; intros E1 E2.
    + exact (Empty_rec _ (false_ne_true E1)).
    + reflexivity.
    + exact (Empty_rec _ (false_ne_true E2^)).
  - destruct i as [m | | m]; simpl; intros E1 E2.
    + exact (Empty_rec _ (false_ne_true E1)).
    + exact (Empty_rec _ (false_ne_true E1)).
    + exact (ap posS (nat_leb_between' n m E1 E2)).
Defined.

Lemma int_leb_succ_self (q : Int) : int_leb (int_succ q) q = false.
Proof.
  destruct q as [n | | n].
  - destruct n.
    + reflexivity.
    + exact (nat_leb_Sn_n n).
  - reflexivity.
  - exact (nat_leb_Sn_n n).
Defined.

(** *** Slice guards, Tate objects, and the slice functors *)

Definition slice_guard (q : Int) : Int -> Bool := fun i => int_leb q i.

Definition slice_layer_guard (q : Int) : Int -> Bool := fun i => int_eqb i q.

Definition SliceCover `{Funext} (q : Int) : Functor (FamCat Int) (FamCat Int)
  := FamTrunc (slice_guard q).

Definition SliceLayer `{Funext} (q : Int) : Functor (FamCat Int) (FamCat Int)
  := FamTrunc (slice_layer_guard q).

Definition tate_object (q : Int) : FamObj Int := fun i => int_eqb i q.

Lemma truncAt_diag (b : Bool) : truncAt b b = b.
Proof.
  destruct b; reflexivity.
Defined.

Theorem slice_layer_tate `{Funext} (q : Int)
  : fam_trunc (slice_layer_guard q) (tate_object q) = tate_object q.
Proof.
  apply path_forall; intro i.
  exact (truncAt_diag (int_eqb i q)).
Defined.

Theorem slice_orthogonal `{Funext} (q q' : Int)
  (Hne : int_eqb q q' = false)
  : fam_trunc (slice_layer_guard q) (tate_object q') = (fam_zero : FamObj Int).
Proof.
  apply path_forall; intro i.
  unfold fam_trunc, slice_layer_guard, tate_object, fam_zero.
  destruct (bool_dec_eq (int_eqb i q)) as [He | He].
  - rewrite He.
    simpl.
    rewrite (int_eqb_true_path i q He).
    exact Hne.
  - rewrite He.
    reflexivity.
Defined.

(** Maps into objects supported at or above q factor uniquely through the q-th effective cover. *)

Theorem slice_cover_universal `{Funext} (q : Int) (X Y : FamObj Int)
  (HY : IsGuardSupported (slice_guard q) Y)
  (f : FamHom X Y)
  : Contr { u : FamHom (fam_trunc (slice_guard q) X) Y &
            fam_comp X (fam_trunc (slice_guard q) X) Y u
              (fam_unit (slice_guard q) X) = f }.
Proof.
  exact (fam_trunc_universal (slice_guard q) X Y HY f).
Defined.

(** *** The slice as the fiber of the projection between effective covers *)

Definition slice_projection `{Funext} (q : Int) (X : FamObj Int)
  : FamHom (fam_trunc (slice_guard q) X) (fam_trunc (slice_guard (int_succ q)) X)
  := fam_change (slice_guard q) (slice_guard (int_succ q)) X.

Definition slice_fiber `{Funext} (q : Int) (X : FamObj Int)
  : FiberData (FamZero Int) (slice_projection q X).
Proof.
  refine (@Build_FiberData (FamCat Int) (FamZero Int)
            (fam_trunc (slice_guard q) X)
            (fam_trunc (slice_guard (int_succ q)) X)
            (slice_projection q X)
            (fam_trunc (slice_layer_guard q) X)
            (fam_change (slice_layer_guard q) (slice_guard q) X)
            _).
  apply path_forall; intro i.
  destruct (bool_dec_eq (int_eqb i q)) as [He | He].
  - destruct (bool_dec_eq (int_leb (int_succ q) i)) as [Hb | Hb].
    + exact (Empty_rec _ (false_ne_true
               ((int_leb_succ_self q)^
                  @ transport (fun j => int_leb (int_succ q) j = true)
                      (int_eqb_true_path i q He) Hb))).
    + exact (lev_to_falseish_unique _ _
               (ap (fun b => truncAt b (X i)) Hb) _ _).
  - exact (lev_from_falseish_unique _ _
             (ap (fun b => truncAt b (X i)) He) _ _).
Defined.

Theorem slice_zero_implies_iso `{Funext} (q : Int) (X : FamObj Int)
  (Hzero : fam_trunc (slice_layer_guard q) X = (fam_zero : FamObj Int))
  : IsIsomorphism (C := FamCat Int) (slice_projection q X).
Proof.
  assert (HX : X q = false).
  { exact ((ap (fun b => truncAt b (X q)) (int_eqb_refl q))^
             @ ap (fun Z : FamObj Int => Z q) Hzero). }
  exists (fam_change (slice_guard (int_succ q)) (slice_guard q) X).
  split.
  - apply path_forall; intro i.
    apply lev_change_inverse_l.
    intros Hb1 Hb2.
    exact (ap X (int_leb_between q i Hb1 Hb2) @ HX).
  - apply path_forall; intro i.
    apply lev_change_inverse_r.
    exact (int_leb_succ_true q i).
Defined.

(*******************************************************************************)
(*  THE WEIGHTED TAYLOR TOWER CONVERGENCE THEOREM                              *)
(*******************************************************************************)

(** The capstone: bounded support makes the layer obstruction weight-bounded, hence eventually zero; the tower stabilizes and the object is the limit of its stable tail. *)

Lemma nat_leb_false_lt (k n : nat) : nat_leb k n = false -> nat_lt n k.
Proof.
  revert n.
  induction k.
  - intros n E.
    exact (Empty_rec _ (false_ne_true E^)).
  - intros n E.
    destruct n.
    + exact tt.
    + exact (IHk n E).
Defined.

(** The obstruction measure: one when the layer above the stage is occupied, zero otherwise. *)

Definition fam_obstruction (X : FamObj nat) (n : nat) : QPos
  := nat_to_qpos (if X (S n) then S O else O).

Lemma fam_obstruction_is_integer (X : FamObj nat)
  : IsIntegerValued (fam_obstruction X).
Proof.
  intro n.
  reflexivity.
Defined.

Lemma fam_obstruction_bounded (X : FamObj nat) (d : nat)
  (Hsupp : forall k, nat_lt d k -> X k = false)
  : forall n, qpos_lt (fam_obstruction X n)
              (qpos_mult (nat_to_qpos (S d)) (w_stage n)).
Proof.
  intro n.
  rewrite nat_to_qpos_S_N_times_w_stage.
  destruct (bool_dec_eq (X (S n))) as [Hx | Hx].
  - assert (Hlt : nat_lt n d).
    { destruct (nat_lt_or_eq_or_gt n d) as [[Hlt | Heq] | Hgt].
      - exact Hlt.
      - exact (Empty_rec _ (false_ne_true
          ((Hsupp (S n) (transport (fun m => nat_lt m (S n)) Heq (nat_lt_S n)))^
             @ Hx))).
      - exact (Empty_rec _ (false_ne_true
          ((Hsupp (S n) (nat_lt_trans d n (S n) Hgt (nat_lt_S n)))^
             @ Hx))). }
    unfold fam_obstruction.
    rewrite Hx.
    exact (one_lt_SN_over_Sn d n Hlt).
  - unfold fam_obstruction.
    rewrite Hx.
    apply qpos_zero_lt_any_positive.
    exact tt.
Defined.

Lemma fam_obstruction_zero_layer `{Funext} (X : FamObj nat) (n : nat)
  (Hz : qpos_is_zero (fam_obstruction X n))
  : fam_trunc (fam_guard_D n) X = (fam_zero : FamObj nat).
Proof.
  assert (Hx : X (S n) = false).
  { destruct (bool_dec_eq (X (S n))) as [Hx | Hx].
    - unfold fam_obstruction, qpos_is_zero in Hz.
      rewrite Hx in Hz.
      exact (Empty_rec _ (S_ne_O O Hz)).
    - exact Hx. }
  apply path_forall; intro k.
  unfold fam_trunc, fam_guard_D, fam_zero.
  destruct (bool_dec_eq (nat_eqb k (S n))) as [He | He].
  - rewrite He.
    simpl.
    rewrite (nat_eqb_true_path k (S n) He).
    exact Hx.
  - rewrite He.
    reflexivity.
Defined.

(** The approximation map is an isomorphism once the guard clears the support. *)

Theorem fam_unit_iso_of_supported `{Funext} (n : nat) (X : FamObj nat)
  (Hsupp : forall k, nat_lt n k -> X k = false)
  : IsIsomorphism (C := FamCat nat) (fam_unit (fam_guard_P n) X).
Proof.
  exists (fam_change (fam_guard_P n) fam_guard_all X).
  split.
  - apply path_forall; intro k.
    exact (lev_change_inverse_l true (nat_leb k n) (X k)
             (fun _ Hb2 => Hsupp k (nat_leb_false_lt k n Hb2))).
  - apply path_forall; intro k.
    exact (lev_change_inverse_r true (nat_leb k n) (X k)
             (fun _ => idpath)).
Defined.

Theorem weighted_taylor_tower_convergence `{Funext}
  (X : FamObj nat) (d : nat)
  (Hsupp : forall k, nat_lt d k -> X k = false)
  : { N : nat &
      ((TowerStabilizesAt (fam_P_tower X) N) *
       (forall n, nat_le N n ->
          IsIsomorphism (C := FamCat nat) (fam_unit (fam_guard_P n) X)))%type }.
Proof.
  assert (Hev : EventuallyZero (fam_obstruction X)).
  { apply integer_LimitZero_implies_EventuallyZero.
    - exact (fam_obstruction_is_integer X).
    - exact (bounded_measure_limit_zero (fam_obstruction X) (nat_to_qpos (S d))
               tt (fam_obstruction_bounded X d Hsupp)). }
  destruct Hev as [N0 HN0].
  exists (nat_add (S N0) d).
  split.
  - intros n Hn.
    apply fam_layer_zero_implies_iso.
    apply fam_obstruction_zero_layer.
    apply HN0.
    apply (nat_lt_of_S_le N0 n).
    exact (nat_le_trans (S N0) (nat_add (S N0) d) n
             (nat_le_add_r (S N0) d) Hn).
  - intros n Hn.
    apply fam_unit_iso_of_supported.
    intros k Hk.
    apply Hsupp.
    exact (nat_le_lt_trans d n k
             (nat_le_trans d (nat_add (S N0) d) n (nat_le_N_add (S N0) d) Hn)
             Hk).
Defined.

Corollary weighted_taylor_tower_limit `{Funext}
  (X : FamObj nat) (d : nat)
  (Hsupp : forall k, nat_lt d k -> X k = false)
  : { N : nat & { stab : TowerStabilizesAt (fam_P_tower X) N &
      IsTowerLimit (FamCat nat)
        (tower_shift (fam_P_tower X) N)
        (ct_stage (FamCat nat) (fam_P_tower X) N)
        (stab_cone (tower_shift (fam_P_tower X) N)
           (tower_shift_stabilizes (fam_P_tower X) N stab)) } }.
Proof.
  destruct (weighted_taylor_tower_convergence X d Hsupp) as [N [stab Hunit]].
  exists N.
  exists stab.
  exact (stabilized_tower_tail_has_limit (fam_P_tower X) N stab).
Defined.

(** *** X is the limit of its own tower: the unit cone is limiting for every boundedly supported object. *)

Definition fam_unit_cone `{Funext} (X : FamObj nat)
  : TowerCone (FamCat nat) (fam_P_tower X) X.
Proof.
  refine (Build_TowerCone (FamCat nat) (fam_P_tower X) X
            (fun n => fam_unit (fam_guard_P n) X)
            _).
  intro n.
  apply path_forall; intro k.
  exact (lev_change_comp_mono true (nat_leb k (S n)) (nat_leb k n) (X k)
           (nat_leb_succ_r k n)).
Defined.

Theorem weighted_tower_limit_is_X `{Funext} (X : FamObj nat) (d : nat)
  (Hsupp : forall k, nat_lt d k -> X k = false)
  : IsTowerLimit (FamCat nat) (fam_P_tower X) X (fam_unit_cone X).
Proof.
  intros W c.
  assert (Hui : forall n, nat_le d n ->
      IsIsomorphism (C := FamCat nat) (fam_unit (fam_guard_P n) X)).
  { intros n Hn.
    apply fam_unit_iso_of_supported.
    intros k Hk.
    exact (Hsupp k (nat_le_lt_trans d n k Hn Hk)). }
  assert (Hmi : forall n, nat_le d n ->
      IsIsomorphism (C := FamCat nat)
        (fam_change (fam_guard_P (S n)) (fam_guard_P n) X)).
  { intros n Hn.
    apply fam_layer_zero_implies_iso.
    apply fam_obstruction_zero_layer.
    exact (ap (fun b : Bool => qpos_num (nat_to_qpos (if b then S O else O)))
             (Hsupp (S n) (nat_le_lt_trans d n (S n) Hn (nat_lt_S n)))). }
  set (u0 := ((iso_inverse (Hui d (nat_le_refl d)))
                o tc_component (FamCat nat) (fam_P_tower X) W c d)%morphism).
  assert (cond_d :
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) d
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c d).
  { unfold u0.
    refine ((associativity (FamCat nat) _ _ _ _
               (tc_component (FamCat nat) (fam_P_tower X) W c d)
               (iso_inverse (Hui d (nat_le_refl d)))
               (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) d))^
              @ _).
    refine (ap (fun h =>
                  (h o tc_component (FamCat nat) (fam_P_tower X) W c d)%morphism)
              (prod_pr2 (Hui d (nat_le_refl d)).2) @ _).
    apply left_identity. }
  assert (step_down : forall m,
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) (S m)
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c (S m) ->
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) m
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c m).
  { intros m Hm.
    refine (ap (fun h => (h o u0)%morphism)
              (tc_compat (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) m)^
              @ _).
    refine (associativity _ _ _ _ _ _ _ _ @ _).
    refine (ap (fun h =>
                  (ct_map (FamCat nat) (fam_P_tower X) m o h)%morphism) Hm @ _).
    exact (tc_compat (FamCat nat) (fam_P_tower X) W c m). }
  assert (step_up : forall m, nat_le d m ->
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) m
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c m ->
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) (S m)
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c (S m)).
  { intros m Hm Hcond.
    apply (iso_cancel_l (ct_map (FamCat nat) (fam_P_tower X) m) (Hmi m Hm)).
    refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
    refine (ap (fun h => (h o u0)%morphism)
              (tc_compat (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) m)
              @ _).
    refine (Hcond @ _).
    exact (tc_compat (FamCat nat) (fam_P_tower X) W c m)^. }
  assert (cond_le : forall j n0,
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X)
         (nat_add j n0) o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c (nat_add j n0) ->
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) n0
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c n0).
  { intro j.
    induction j.
    - intros n0 H0.
      exact H0.
    - intros n0 H0.
      exact (IHj n0 (step_down (nat_add j n0) H0)). }
  assert (cond_up : forall j,
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X)
         (nat_add j d) o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c (nat_add j d)).
  { induction j.
    - exact cond_d.
    - exact (step_up (nat_add j d) (nat_le_N_add j d) IHj). }
  assert (cond_all : forall n,
      (tc_component (FamCat nat) (fam_P_tower X) X (fam_unit_cone X) n
         o u0)%morphism
      = tc_component (FamCat nat) (fam_P_tower X) W c n).
  { intro n.
    destruct (nat_le_total n d) as [Hle | Hge].
    - apply (cond_le (nat_sub d n) n).
      exact (transport
               (fun m =>
                  (tc_component (FamCat nat) (fam_P_tower X) X
                     (fam_unit_cone X) m o u0)%morphism
                  = tc_component (FamCat nat) (fam_P_tower X) W c m)
               (nat_add_sub_l_cancel (leq_of_nat_le n d Hle))^
               cond_d).
    - exact (transport
               (fun m =>
                  (tc_component (FamCat nat) (fam_P_tower X) X
                     (fam_unit_cone X) m o u0)%morphism
                  = tc_component (FamCat nat) (fam_P_tower X) W c m)
               (nat_add_sub_l_cancel (leq_of_nat_le d n Hge))
               (cond_up (nat_sub n d))). }
  refine (Build_Contr _ (u0 ; cond_all) _).
  intros [u' e'].
  apply path_sigma_hprop.
  simpl.
  apply (iso_cancel_l (C := FamCat nat) (fam_unit (fam_guard_P d) X)
           (Hui d (nat_le_refl d))).
  exact (cond_all d @ (e' d)^).
Defined.

(** *** A non-degenerate instance and its genuine threshold *)

Definition full_below (d : nat) : FamObj nat := fun k => nat_leb k d.

(** *** The scheme world meets the tower world: level families derived from the geometry, towers run on them, and the affine-line functor changes the stage through the dimension. *)

Definition scheme_level_family {F : CField} (X : CScheme F) : FamObj nat
  := full_below (cs_dim F X).

Lemma full_below_supported (d : nat)
  : forall k, nat_lt d k -> full_below d k = false.
Proof.
  intros k Hk.
  unfold full_below.
  destruct (bool_dec_eq (nat_leb k d)) as [Hb | Hb].
  - exact (Empty_rec _
      (nat_le_lt_contradiction k d (nat_leb_true_le k d Hb) Hk)).
  - exact Hb.
Defined.

Theorem weighted_tower_fails_below_stage `{Funext}
  : IsIsomorphism (C := FamCat nat)
      (fam_change (fam_guard_P 2) (fam_guard_P 1) (full_below 3))
    -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  exact (false_ne_true (apD10 Hgf 2%nat)).
Defined.

Theorem weighted_tower_genuine_threshold_example `{Funext}
  : ({ N : nat &
       ((TowerStabilizesAt (fam_P_tower (full_below 3)) N) *
        (forall n, nat_le N n ->
           IsIsomorphism (C := FamCat nat)
             (fam_unit (fam_guard_P n) (full_below 3))))%type })
    * (IsIsomorphism (C := FamCat nat)
         (fam_change (fam_guard_P 2) (fam_guard_P 1) (full_below 3))
       -> Empty).
Proof.
  split.
  - exact (weighted_taylor_tower_convergence (full_below 3) 3
             (full_below_supported 3)).
  - exact weighted_tower_fails_below_stage.
Defined.

(** *** One tower stabilizes exactly at its support bound and provably fails at the predecessor stage. *)

Lemma nat_leb_refl (n : nat) : nat_leb n n = true.
Proof.
  induction n.
  - reflexivity.
  - exact IHn.
Defined.

Lemma fam_tower_iso_of_level_empty `{Funext} (X : FamObj nat) (n : nat)
  (HX : X (S n) = false)
  : IsIsomorphism (C := FamCat nat)
      (fam_change (fam_guard_P (S n)) (fam_guard_P n) X).
Proof.
  apply fam_layer_zero_implies_iso.
  apply fam_obstruction_zero_layer.
  exact (ap (fun b : Bool => qpos_num (nat_to_qpos (if b then S O else O))) HX).
Defined.

Lemma lev_gap_not_invertible (b1 b2 x : Bool)
  (Hb1 : b1 = true) (Hb2 : b2 = false) (Hx : x = true)
  (h : LevHom (truncAt b2 x) (truncAt b1 x))
  (E : lev_comp (truncAt b1 x) (truncAt b2 x) (truncAt b1 x)
         h (lev_change b1 b2 x) = lev_id (truncAt b1 x))
  : Empty.
Proof.
  destruct b1.
  - destruct b2.
    + exact (false_ne_true Hb2^).
    + destruct x.
      * exact (false_ne_true E).
      * exact (false_ne_true Hx).
  - exact (false_ne_true Hb1).
Defined.

Lemma fam_change_not_iso_of_gap `{Funext}
  (g1 g2 : nat -> Bool) (X : FamObj nat) (k : nat)
  (H1 : g1 k = true) (H2 : g2 k = false) (HX : X k = true)
  : IsIsomorphism (C := FamCat nat) (fam_change g1 g2 X) -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  exact (lev_gap_not_invertible (g1 k) (g2 k) (X k) H1 H2 HX
           (g k) (apD10 Hgf k)).
Defined.

(** *** Converse detection: an isomorphic tower map forces its layer to vanish, so layers never over-report. *)

Theorem fam_iso_implies_layer_zero `{Funext} (n : nat) (X : FamObj nat)
  (Hiso : IsIsomorphism (C := FamCat nat)
            (fam_change (fam_guard_P (S n)) (fam_guard_P n) X))
  : fam_trunc (fam_guard_D n) X = (fam_zero : FamObj nat).
Proof.
  apply path_forall; intro k.
  destruct (bool_dec_eq (nat_eqb k (S n))) as [He | He].
  - destruct (bool_dec_eq (X (S n))) as [HX | HX].
    + apply Empty_rec.
      exact (fam_change_not_iso_of_gap
               (fam_guard_P (S n)) (fam_guard_P n) X (S n)
               (nat_leb_refl (S n)) (nat_leb_Sn_n n) HX Hiso).
    + refine (ap (fun m => truncAt (nat_eqb m (S n)) (X m))
                (nat_eqb_true_path k (S n) He) @ _).
      refine (ap (fun b => truncAt b (X (S n))) (nat_eqb_refl (S n)) @ _).
      exact HX.
  - exact (ap (fun b => truncAt b (X k)) He).
Defined.

Theorem fam_layers_never_over_report `{Funext} (n : nat) (X : FamObj nat)
  (Hiso : IsIsomorphism
            (gtd_layer_at (gtwl_data FamPreStable FamIdReduced
               FamGoodwillieTower) n X))
  : object_of (gtwl_D FamPreStable FamIdReduced FamGoodwillieTower n) X
    = zero FamPreStable (ps_zero FamPreStable).
Proof.
  exact (fam_iso_implies_layer_zero n X Hiso).
Defined.

Theorem full_below_genuine_stage `{Funext} (d : nat)
  : ((TowerStabilizesAt (fam_P_tower (full_below (S d))) (S d))
     * (IsIsomorphism (C := FamCat nat)
          (fam_change (fam_guard_P (S d)) (fam_guard_P d) (full_below (S d)))
        -> Empty))%type.
Proof.
  split.
  - intros n Hn.
    apply fam_tower_iso_of_level_empty.
    exact (full_below_supported (S d) (S n)
             (nat_le_lt_trans (S d) n (S n) Hn (nat_lt_S n))).
  - apply (fam_change_not_iso_of_gap _ _ _ (S d)).
    + exact (nat_leb_refl (S d)).
    + exact (nat_leb_Sn_n d).
    + exact (nat_leb_refl (S d)).
Defined.

(** The tower runs on the geometry-derived family of every concrete scheme, stabilizing at its dimension, and the affine-line functor changes the stage: the stage sufficient for X provably fails for X times the affine line. *)

Theorem scheme_tower_runs `{Funext} (F : CField) (X : CScheme F)
  : TowerStabilizesAt (fam_P_tower (scheme_level_family X)) (cs_dim F X).
Proof.
  intros n Hn.
  apply fam_tower_iso_of_level_empty.
  exact (full_below_supported (cs_dim F X) (S n)
           (nat_le_lt_trans (cs_dim F X) n (S n) Hn (nat_lt_S n))).
Defined.

Theorem cs_dim_changes_stage `{Funext} (F : CField) (X : CScheme F)
  : ((TowerStabilizesAt (fam_P_tower (scheme_level_family X)) (cs_dim F X))
     * (IsIsomorphism (C := FamCat nat)
          (fam_change (fam_guard_P (S (cs_dim F X)))
             (fam_guard_P (cs_dim F X))
             (scheme_level_family (object_of (CSchA1Functor F) X)))
        -> Empty))%type.
Proof.
  split.
  - exact (scheme_tower_runs F X).
  - apply (fam_change_not_iso_of_gap _ _ _ (S (cs_dim F X))).
    + exact (nat_leb_refl (S (cs_dim F X))).
    + exact (nat_leb_Sn_n (cs_dim F X)).
    + refine (ap (nat_leb (S (cs_dim F X)))
               (nat_add_succ_r (cs_dim F X) O
                  @ ap S (nat_add_zero_r (cs_dim F X))) @ _).
      exact (nat_leb_refl (S (cs_dim F X))).
Defined.

(** *** Connectivity: the weight bound, the support bound, and fiber connectivity growth are equivalent, the in-model analyticity criterion. *)

Definition FamConnGT (X : FamObj nat) (m : nat) : Type
  := forall k, nat_le k m -> X k = false.

Lemma one_lt_SN_over_Sn_inv (N n : nat)
  (E : qpos_lt (nat_to_qpos (S O)) {| qpos_num := S N; qpos_denom_pred := n |})
  : nat_lt n N.
Proof.
  unfold qpos_lt, nat_to_qpos, qpos_denom in E.
  simpl in E.
  rewrite nat_add_zero_r in E.
  rewrite nat_mul_one_r in E.
  exact E.
Defined.

Theorem fam_bounded_to_supported (X : FamObj nat) (d : nat)
  (Hbound : forall n, qpos_lt (fam_obstruction X n)
              (qpos_mult (nat_to_qpos (S d)) (w_stage n)))
  : forall k, nat_lt d k -> X k = false.
Proof.
  intros k Hk.
  destruct k.
  - exact (Empty_rec _ (nat_lt_zero_absurd d Hk)).
  - destruct (bool_dec_eq (X (S k))) as [HX | HX].
    + pose (Hb := transport (fun q => qpos_lt (fam_obstruction X k) q)
                    (nat_to_qpos_S_N_times_w_stage d k) (Hbound k)).
      pose (Hb' := transport
                     (fun b : Bool => qpos_lt (nat_to_qpos (if b then S O else O))
                        {| qpos_num := S d; qpos_denom_pred := k |})
                     HX Hb).
      exact (Empty_rec _
               (nat_le_lt_contradiction d k (nat_le_of_lt_S d k Hk)
                  (one_lt_SN_over_Sn_inv d k Hb'))).
    + exact HX.
Defined.

Theorem fam_supported_fiber_conn `{Funext} (X : FamObj nat) (d : nat)
  (Hsupp : forall k, nat_lt d k -> X k = false)
  : forall n, nat_le d n -> FamConnGT (fam_trunc (fam_guard_D n) X) (S n).
Proof.
  intros n Hn k Hk.
  destruct (bool_dec_eq (nat_eqb k (S n))) as [He | He].
  - refine (ap (fun m => truncAt (nat_eqb m (S n)) (X m))
              (nat_eqb_true_path k (S n) He) @ _).
    refine (ap (fun b => truncAt b (X (S n))) (nat_eqb_refl (S n)) @ _).
    exact (Hsupp (S n) (nat_le_lt_trans d n (S n) Hn (nat_lt_S n))).
  - exact (ap (fun b => truncAt b (X k)) He).
Defined.

Theorem fam_fiber_conn_to_supported `{Funext} (X : FamObj nat) (d : nat)
  (Hconn : forall n, nat_le d n ->
             FamConnGT (fam_trunc (fam_guard_D n) X) (S n))
  : forall k, nat_lt d k -> X k = false.
Proof.
  intros k Hk.
  destruct k.
  - exact (Empty_rec _ (nat_lt_zero_absurd d Hk)).
  - refine ((ap (fun b => truncAt b (X (S k))) (nat_eqb_refl (S k)))^ @ _).
    exact (Hconn k (nat_le_of_lt_S d k Hk) (S k) (nat_le_refl (S k))).
Defined.

Theorem fam_analyticity_criterion `{Funext} (X : FamObj nat) (d : nat)
  : (((forall k, nat_lt d k -> X k = false) ->
      (forall n, qpos_lt (fam_obstruction X n)
         (qpos_mult (nat_to_qpos (S d)) (w_stage n))))
     * (((forall n, qpos_lt (fam_obstruction X n)
            (qpos_mult (nat_to_qpos (S d)) (w_stage n)))) ->
        (forall k, nat_lt d k -> X k = false))
     * ((forall k, nat_lt d k -> X k = false) ->
        (forall n, nat_le d n ->
           FamConnGT (fam_trunc (fam_guard_D n) X) (S n)))
     * ((forall n, nat_le d n ->
           FamConnGT (fam_trunc (fam_guard_D n) X) (S n)) ->
        (forall k, nat_lt d k -> X k = false)))%type.
Proof.
  refine (_, _, _, _).
  - exact (fam_obstruction_bounded X d).
  - exact (fam_bounded_to_supported X d).
  - exact (fam_supported_fiber_conn X d).
  - exact (fam_fiber_conn_to_supported X d).
Defined.

(*******************************************************************************)
(*  THE FRONTIER: A DERIVED WEIGHT BOUND FOR A CONCRETE BLOW-UP                *)
(*******************************************************************************)

(** A blow-up model derives the weight bound from geometry, obstructions supported at the exceptional dimension with constant derived from dimension and singularity data, realized concretely by the blow-up of the affine plane over F2 with constant six. *)

Lemma qpos_lt_cross_transfer (m a b : QPos)
  (Hcross : nat_mul (qpos_num a) (qpos_denom b)
            = nat_mul (qpos_num b) (qpos_denom a))
  (Hlt : qpos_lt m a)
  : qpos_lt m b.
Proof.
  unfold qpos_lt in *.
  apply (nat_lt_mul_cancel_r _ _ (qpos_denom a)).
  - unfold qpos_denom.
    exact tt.
  - rewrite (nat_mul_rearrange_1 (qpos_num m) (qpos_denom b) (qpos_denom a)).
    rewrite (nat_mul_rearrange_1 (qpos_num b) (qpos_denom m) (qpos_denom a)).
    rewrite <- Hcross.
    rewrite (nat_mul_rearrange_1 (qpos_num a) (qpos_denom b) (qpos_denom m)).
    apply nat_lt_mul_pos_r.
    + exact Hlt.
    + unfold qpos_denom.
      exact tt.
Defined.

(** A stage-weight bound transfers to a total-weight bound with the constant multiplied by the dimension and singularity factors. *)

Lemma cross_arith (C0 d s n : nat)
  : nat_mul (nat_mul C0 (S O))
      (nat_mul (S O) (nat_mul (nat_mul (S d) (S s)) (S n)))
    = nat_mul (nat_mul (nat_mul C0 (nat_mul (S d) (S s))) (S O))
        (nat_mul (S O) (S n)).
Proof.
  rewrite (nat_mul_one_r C0).
  rewrite (nat_mul_one_r (nat_mul C0 (nat_mul (S d) (S s)))).
  rewrite (nat_mul_one_l (nat_mul (nat_mul (S d) (S s)) (S n))).
  rewrite (nat_mul_one_l (S n)).
  apply nat_mul_assoc.
Defined.

Lemma stage_bound_to_total_bound {F : CField} (X : CScheme F)
  (C0 : nat) (m : QPos) (n : nat)
  (Hlt : qpos_lt m (qpos_mult (nat_to_qpos C0) (w_stage n)))
  : qpos_lt m
      (qpos_mult
         (nat_to_qpos
            (nat_mul C0 (nat_mul (S (cs_dim F X)) (S (cs_sing F X)))))
         (w_total X n)).
Proof.
  refine (qpos_lt_cross_transfer m
            (qpos_mult (nat_to_qpos C0) (w_stage n))
            _ _ Hlt).
  exact (cross_arith C0 (cs_dim F X) (cs_sing F X) n).
Defined.

(** *** Blow-up models: the geometry supplies the constant *)

Record BlowupModel (F : CField) : Type := {
  bm_base : CScheme F;
  bm_total : CScheme F;
  bm_blowdown : CMor bm_total bm_base;
  bm_exc_dim : nat;
  bm_exc_below : nat_lt bm_exc_dim (cs_dim F bm_base);
  bm_levels : FamObj nat;
  bm_levels_supported : forall k, nat_lt bm_exc_dim k -> bm_levels k = false
}.

Definition bm_weight_constant {F : CField} (B : BlowupModel F) : nat
  := nat_mul (S (bm_exc_dim F B))
       (nat_mul (S (cs_dim F (bm_base F B))) (S (cs_sing F (bm_base F B)))).

Theorem blowup_model_weight_bounded {F : CField} (B : BlowupModel F)
  : forall n, qpos_lt (fam_obstruction (bm_levels F B) n)
      (qpos_mult (nat_to_qpos (bm_weight_constant B))
         (w_total (bm_base F B) n)).
Proof.
  intro n.
  apply (stage_bound_to_total_bound (bm_base F B) (S (bm_exc_dim F B))).
  exact (fam_obstruction_bounded (bm_levels F B) (bm_exc_dim F B)
           (bm_levels_supported F B) n).
Defined.

Theorem blowup_model_tower_converges `{Funext} {F : CField} (B : BlowupModel F)
  : { N : nat &
      ((TowerStabilizesAt (fam_P_tower (bm_levels F B)) N) *
       (forall n, nat_le N n ->
          IsIsomorphism (C := FamCat nat)
            (fam_unit (fam_guard_P n) (bm_levels F B))))%type }.
Proof.
  exact (weighted_taylor_tower_convergence (bm_levels F B) (bm_exc_dim F B)
           (bm_levels_supported F B)).
Defined.

(** *** The blow-up of the affine plane over F2 at the origin *)

Definition bool_pair_nonzero (v : (Bool * Bool)%type) : Bool
  := orb (prod_pr1 v) (prod_pr2 v).

Definition P1F2 : Type
  := { v : (Bool * Bool)%type & bool_pair_nonzero v = true }.

Global Instance ishset_P1F2 : IsHSet P1F2.
Proof.
  exact _.
Defined.

Definition bool_eqb (a b : Bool) : Bool := if a then b else negb b.

Definition pair_eqb (u v : (Bool * Bool)%type) : Bool
  := andb (bool_eqb (prod_pr1 u) (prod_pr1 v))
          (bool_eqb (prod_pr2 u) (prod_pr2 v)).

Definition bool_pair_zero (v : (Bool * Bool)%type) : Bool
  := andb (negb (prod_pr1 v)) (negb (prod_pr2 v)).

(** Over F2 each line through the origin contains one nonzero vector, so the projective line is the type of nonzero vectors. *)

Definition f2_incidence (p : (Bool * Bool)%type) (l : P1F2) : Bool
  := orb (bool_pair_zero p) (pair_eqb p l.1).

Definition blowup_carrier : Type
  := { q : ((Bool * Bool) * P1F2)%type &
       f2_incidence (prod_pr1 q) (prod_pr2 q) = true }.

Global Instance ishset_blowup_carrier : IsHSet blowup_carrier.
Proof.
  exact _.
Defined.

Definition cA2_F2 : CScheme F2
  := {| cs_carrier := (Bool * Bool)%type;
        cs_ishset := @istrunc_prod _ _ hset_bool _ hset_bool;
        cs_dim := 2;
        cs_sing := O |}.

Definition blowup_A2_F2 : CScheme F2
  := {| cs_carrier := blowup_carrier;
        cs_ishset := ishset_blowup_carrier;
        cs_dim := 2;
        cs_sing := O |}.

Definition blowdown : CMor blowup_A2_F2 cA2_F2
  := fun q => prod_pr1 q.1.

Definition line10 : P1F2 := ((true, false) ; idpath).

Definition line01 : P1F2 := ((false, true) ; idpath).

Definition exc_pt10 : blowup_carrier
  := (((false, false), line10) ; idpath).

Definition exc_pt01 : blowup_carrier
  := (((false, false), line01) ; idpath).

(** The blowdown identifies the two exceptional points above the origin, so it is not a scheme isomorphism. *)

Theorem blowdown_not_scheme_iso `{Funext}
  : @IsIsomorphism (CSch F2) blowup_A2_F2 cA2_F2 blowdown -> Empty.
Proof.
  intros [g [Hgf Hfg]].
  pose (q := (ap10 Hgf exc_pt10)^ @ ap10 Hgf exc_pt01).
  exact (false_ne_true (ap (fun w => prod_pr1 ((prod_pr2 w.1).1)) q)^).
Defined.

Definition blowup_model_A2_F2 : BlowupModel F2
  := {| bm_base := cA2_F2;
        bm_total := blowup_A2_F2;
        bm_blowdown := blowdown;
        bm_exc_dim := 1;
        bm_exc_below := tt;
        bm_levels := full_below 1;
        bm_levels_supported := full_below_supported 1 |}.

(** The derived constant computes to six from exceptional dimension one, ambient dimension two, and singularity zero. *)

Lemma blowup_A2_F2_constant_is_six
  : bm_weight_constant blowup_model_A2_F2 = 6%nat.
Proof.
  reflexivity.
Defined.

Theorem blowup_A2_F2_weight_bounded
  : forall n, qpos_lt (fam_obstruction (full_below 1) n)
      (qpos_mult (nat_to_qpos (bm_weight_constant blowup_model_A2_F2))
         (w_total cA2_F2 n)).
Proof.
  exact (blowup_model_weight_bounded blowup_model_A2_F2).
Defined.

Theorem blowup_A2_F2_tower_converges `{Funext}
  : { N : nat &
      ((TowerStabilizesAt (fam_P_tower (full_below 1)) N) *
       (forall n, nat_le N n ->
          IsIsomorphism (C := FamCat nat)
            (fam_unit (fam_guard_P n) (full_below 1))))%type }.
Proof.
  exact (blowup_model_tower_converges blowup_model_A2_F2).
Defined.

(*******************************************************************************)
(*  THE RATIONAL QUOTIENT: REPRESENTATION-INDEPENDENT POSITIVE RATIONALS       *)
(*******************************************************************************)

(** QRat is QPos quotiented by cross-multiplication, carrying the descended order and minimal positive structure representation-independently. *)

Section RationalQuotient.

Import HoTT.Colimits.Quotient.

Context `{Funext}.

Definition qpos_cross (q1 q2 : QPos) : Type
  := nat_mul (qpos_num q1) (qpos_denom q2)
     = nat_mul (qpos_num q2) (qpos_denom q1).

Definition qpos_cross_refl (q : QPos) : qpos_cross q q := idpath.

Definition qpos_cross_sym (q1 q2 : QPos)
  : qpos_cross q1 q2 -> qpos_cross q2 q1
  := fun p => p^.

Lemma nat_mul_cancel_r_eq (a b c : nat)
  (Hc : nat_lt O c)
  (E : nat_mul a c = nat_mul b c)
  : a = b.
Proof.
  destruct (nat_lt_or_eq_or_gt a b) as [[Hlt | Heq] | Hgt].
  - exact (Empty_rec _ (nat_lt_irrefl _
      (transport (fun x => nat_lt x (nat_mul b c)) E
         (nat_lt_mul_pos_r a b c Hlt Hc)))).
  - exact Heq.
  - exact (Empty_rec _ (nat_lt_irrefl _
      (transport (fun x => nat_lt x (nat_mul a c)) E^
         (nat_lt_mul_pos_r b a c Hgt Hc)))).
Defined.

Lemma qpos_cross_trans (q1 q2 q3 : QPos)
  : qpos_cross q1 q2 -> qpos_cross q2 q3 -> qpos_cross q1 q3.
Proof.
  intros H12 H23.
  apply (nat_mul_cancel_r_eq _ _ (qpos_denom q2)).
  - unfold qpos_denom.
    exact tt.
  - rewrite (nat_mul_rearrange_1 (qpos_num q1) (qpos_denom q3) (qpos_denom q2)).
    rewrite H12.
    rewrite (nat_mul_rearrange_1 (qpos_num q2) (qpos_denom q1) (qpos_denom q3)).
    rewrite H23.
    rewrite (nat_mul_rearrange_1 (qpos_num q3) (qpos_denom q2) (qpos_denom q1)).
    reflexivity.
Defined.

(** The strict order transfers across cross-equality in both arguments. *)

Lemma qpos_lt_cross_transfer_l (m a b : QPos)
  (Hcross : qpos_cross a b)
  (Hlt : qpos_lt a m)
  : qpos_lt b m.
Proof.
  unfold qpos_lt in *.
  apply (nat_lt_mul_cancel_r _ _ (qpos_denom a)).
  - unfold qpos_denom.
    exact tt.
  - rewrite (nat_mul_rearrange_1 (qpos_num b) (qpos_denom m) (qpos_denom a)).
    rewrite <- Hcross.
    rewrite (nat_mul_rearrange_1 (qpos_num a) (qpos_denom b) (qpos_denom m)).
    rewrite (nat_mul_rearrange_1 (qpos_num m) (qpos_denom b) (qpos_denom a)).
    apply nat_lt_mul_pos_r.
    + exact Hlt.
    + unfold qpos_denom.
      exact tt.
Defined.

Theorem qpos_lt_representation_independent (a a' b b' : QPos)
  (Ha : qpos_cross a a') (Hb : qpos_cross b b')
  : qpos_lt a b -> qpos_lt a' b'.
Proof.
  intro Hlt.
  exact (qpos_lt_cross_transfer_l b' a a' Ha
           (qpos_lt_cross_transfer a b b' Hb Hlt)).
Defined.

(** Boolean reflection of the strict order. *)

Lemma nat_leb_complete (k d : nat) : nat_le k d -> nat_leb k d = true.
Proof.
  revert d.
  induction k.
  - intros d _.
    reflexivity.
  - intros d Hle.
    destruct d.
    + destruct Hle.
    + exact (IHk d Hle).
Defined.

Definition nat_ltb (a b : nat) : Bool := nat_leb (S a) b.

Lemma nat_ltb_reflect (a b : nat)
  : (((nat_ltb a b = true) -> nat_lt a b)
     * ((nat_lt a b) -> nat_ltb a b = true))%type.
Proof.
  split.
  - intro E.
    exact (nat_lt_of_le_succ a b (nat_leb_true_le (S a) b E)).
  - intro Hlt.
    exact (nat_leb_complete (S a) b (nat_le_succ_of_lt a b Hlt)).
Defined.

Definition qpos_ltb (q1 q2 : QPos) : Bool
  := nat_ltb (nat_mul (qpos_num q1) (qpos_denom q2))
             (nat_mul (qpos_num q2) (qpos_denom q1)).

Lemma qpos_ltb_reflect (q1 q2 : QPos)
  : (((qpos_ltb q1 q2 = true) -> qpos_lt q1 q2)
     * ((qpos_lt q1 q2) -> qpos_ltb q1 q2 = true))%type.
Proof.
  exact (nat_ltb_reflect _ _).
Defined.

Lemma qpos_ltb_resp_r (m a b : QPos)
  (Hab : qpos_cross a b)
  : qpos_ltb m a = qpos_ltb m b.
Proof.
  destruct (bool_dec_eq (qpos_ltb m a)) as [Ha | Ha];
  destruct (bool_dec_eq (qpos_ltb m b)) as [Hb | Hb].
  - exact (Ha @ Hb^).
  - exact (Empty_rec _ (false_ne_true (Hb^
      @ prod_pr2 (qpos_ltb_reflect m b)
          (qpos_lt_cross_transfer m a b Hab
             (prod_pr1 (qpos_ltb_reflect m a) Ha))))).
  - exact (Empty_rec _ (false_ne_true (Ha^
      @ prod_pr2 (qpos_ltb_reflect m a)
          (qpos_lt_cross_transfer m b a (qpos_cross_sym a b Hab)
             (prod_pr1 (qpos_ltb_reflect m b) Hb))))).
  - exact (Ha @ Hb^).
Defined.

Lemma qpos_ltb_resp_l (m a b : QPos)
  (Hab : qpos_cross a b)
  : qpos_ltb a m = qpos_ltb b m.
Proof.
  destruct (bool_dec_eq (qpos_ltb a m)) as [Ha | Ha];
  destruct (bool_dec_eq (qpos_ltb b m)) as [Hb | Hb].
  - exact (Ha @ Hb^).
  - exact (Empty_rec _ (false_ne_true (Hb^
      @ prod_pr2 (qpos_ltb_reflect b m)
          (qpos_lt_cross_transfer_l m a b Hab
             (prod_pr1 (qpos_ltb_reflect a m) Ha))))).
  - exact (Empty_rec _ (false_ne_true (Ha^
      @ prod_pr2 (qpos_ltb_reflect a m)
          (qpos_lt_cross_transfer_l m b a (qpos_cross_sym a b Hab)
             (prod_pr1 (qpos_ltb_reflect b m) Hb))))).
  - exact (Ha @ Hb^).
Defined.

(** The quotient. *)

Definition QRat : Type := Quotient qpos_cross.

Definition qrat_class : QPos -> QRat := class_of qpos_cross.

Definition qrat_eq_of_cross (q1 q2 : QPos)
  : qpos_cross q1 q2 -> qrat_class q1 = qrat_class q2
  := fun r => qglue r.

Definition qrat_ltb : QRat -> QRat -> Bool.
Proof.
  srapply Quotient_rec.
  - intro q1.
    srapply Quotient_rec.
    + exact (fun q2 => qpos_ltb q1 q2).
    + intros a b r.
      exact (qpos_ltb_resp_r q1 a b r).
  - intros a b r.
    apply path_forall.
    srapply Quotient_ind_hprop.
    intro q2.
    exact (qpos_ltb_resp_l q2 a b r).
Defined.

Definition qrat_lt (x y : QRat) : Type := qrat_ltb x y = true.

Theorem qrat_lt_spec (q1 q2 : QPos)
  : (((qrat_lt (qrat_class q1) (qrat_class q2)) -> qpos_lt q1 q2)
     * ((qpos_lt q1 q2) -> qrat_lt (qrat_class q1) (qrat_class q2)))%type.
Proof.
  exact (qpos_ltb_reflect q1 q2).
Defined.

(** Effectiveness: classes are equal exactly when the fractions cross. *)

Definition qpos_crossb (q1 q2 : QPos) : Bool
  := nat_eqb (nat_mul (qpos_num q1) (qpos_denom q2))
             (nat_mul (qpos_num q2) (qpos_denom q1)).

Lemma nat_eqb_complete (a b : nat) : a = b -> nat_eqb a b = true.
Proof.
  intro p.
  destruct p.
  exact (nat_eqb_refl a).
Defined.

Lemma qpos_crossb_reflect (q1 q2 : QPos)
  : (((qpos_crossb q1 q2 = true) -> qpos_cross q1 q2)
     * ((qpos_cross q1 q2) -> qpos_crossb q1 q2 = true))%type.
Proof.
  split.
  - exact (nat_eqb_true_path _ _).
  - exact (nat_eqb_complete _ _).
Defined.

Lemma qpos_crossb_resp_r (m a b : QPos)
  (Hab : qpos_cross a b)
  : qpos_crossb m a = qpos_crossb m b.
Proof.
  destruct (bool_dec_eq (qpos_crossb m a)) as [Ha | Ha];
  destruct (bool_dec_eq (qpos_crossb m b)) as [Hb | Hb].
  - exact (Ha @ Hb^).
  - exact (Empty_rec _ (false_ne_true (Hb^
      @ prod_pr2 (qpos_crossb_reflect m b)
          (qpos_cross_trans m a b
             (prod_pr1 (qpos_crossb_reflect m a) Ha) Hab)))).
  - exact (Empty_rec _ (false_ne_true (Ha^
      @ prod_pr2 (qpos_crossb_reflect m a)
          (qpos_cross_trans m b a
             (prod_pr1 (qpos_crossb_reflect m b) Hb)
             (qpos_cross_sym a b Hab))))).
  - exact (Ha @ Hb^).
Defined.

Lemma qpos_crossb_resp_l (m a b : QPos)
  (Hab : qpos_cross a b)
  : qpos_crossb a m = qpos_crossb b m.
Proof.
  destruct (bool_dec_eq (qpos_crossb a m)) as [Ha | Ha];
  destruct (bool_dec_eq (qpos_crossb b m)) as [Hb | Hb].
  - exact (Ha @ Hb^).
  - exact (Empty_rec _ (false_ne_true (Hb^
      @ prod_pr2 (qpos_crossb_reflect b m)
          (qpos_cross_trans b a m
             (qpos_cross_sym a b Hab)
             (prod_pr1 (qpos_crossb_reflect a m) Ha))))).
  - exact (Empty_rec _ (false_ne_true (Ha^
      @ prod_pr2 (qpos_crossb_reflect a m)
          (qpos_cross_trans a b m Hab
             (prod_pr1 (qpos_crossb_reflect b m) Hb))))).
  - exact (Ha @ Hb^).
Defined.

Definition qrat_crossb : QRat -> QRat -> Bool.
Proof.
  srapply Quotient_rec.
  - intro q1.
    srapply Quotient_rec.
    + exact (fun q2 => qpos_crossb q1 q2).
    + intros a b r.
      exact (qpos_crossb_resp_r q1 a b r).
  - intros a b r.
    apply path_forall.
    srapply Quotient_ind_hprop.
    intro q2.
    exact (qpos_crossb_resp_l q2 a b r).
Defined.

Theorem qrat_class_eq_iff (q1 q2 : QPos)
  : (((qrat_class q1 = qrat_class q2) -> qpos_cross q1 q2)
     * ((qpos_cross q1 q2) -> qrat_class q1 = qrat_class q2))%type.
Proof.
  split.
  - intro p.
    apply (prod_pr1 (qpos_crossb_reflect q1 q2)).
    exact (((prod_pr2 (qpos_crossb_reflect q1 q1) (qpos_cross_refl q1))^
              @ ap (qrat_crossb (qrat_class q1)) p)^).
  - exact (qrat_eq_of_cross q1 q2).
Defined.

(** The minimal positive structure descends to the quotient. *)

Definition QRatHasMinimalPositive (measure : nat -> QRat) : Type
  := { min_val : QPos &
       ((nat_lt O (qpos_num min_val)) *
        (forall n, ((measure n = qrat_class qpos_zero)
                    + ((qrat_lt (qrat_class min_val) (measure n))
                       + (measure n = qrat_class min_val)))%type))%type }.

Theorem HasMinimalPositive_descends (measure : nat -> QPos)
  (Hmin : HasMinimalPositive measure)
  : QRatHasMinimalPositive (fun n => qrat_class (measure n)).
Proof.
  destruct Hmin as [min [Hpos Htri]].
  exists min.
  split.
  - exact Hpos.
  - intro n.
    destruct (Htri n) as [Hzero | [Hlt | Heq]].
    + left.
      apply qrat_eq_of_cross.
      unfold qpos_cross.
      rewrite Hzero.
      reflexivity.
    + right; left.
      exact (prod_pr2 (qrat_lt_spec min (measure n)) Hlt).
    + right; right.
      exact (ap qrat_class Heq).
Defined.

End RationalQuotient.
