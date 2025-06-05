Require Import Reals. (* For the real numbers R, basic operations, R_scope *)
Require Import Coq.Reals.RIneq. (* For real number inequality lemmas *)
Require Import Coq.Arith.PeanoNat. (* For natural numbers (nat), S, O, basic nat properties. *)
Require Import Coq.micromega.Lra. (* For the lra tactic (linear real arithmetic). *)

Open Scope R_scope.

Definition nat_to_R (n : nat) : R := INR n.

Record MotivicSpace : Type := mkMotivicSpace {
  underlying_type : Type;    (* Abstract placeholder *)
  dimension : nat;            (* Dimension of the space *)
  sing_metric : nat           (* A natural number metric quantifying singularity *)
}.

Definition sing_complexity (X : MotivicSpace) : nat :=
  sing_metric X.

Definition w_dim (X : MotivicSpace) : R :=
  /(1 + nat_to_R (dimension X)).

Definition w_sing (X : MotivicSpace) : R :=
  /(1 + nat_to_R (sing_complexity X)).
Definition w_stage (n : nat) : R :=
  /(1 + nat_to_R n).

Definition w_total (X : MotivicSpace) (n : nat) : R :=
  w_dim X * w_sing X * w_stage n. 

Lemma w_dim_positive : forall X : MotivicSpace, 0 < w_dim X.
Proof.
  intros X. unfold w_dim. apply Rinv_0_lt_compat.
  apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | apply pos_INR].
Qed.

Lemma w_sing_positive : forall X : MotivicSpace, 0 < w_sing X.
Proof.
  intros X. unfold w_sing. apply Rinv_0_lt_compat.
  apply Rplus_lt_le_0_compat.
  - apply Rlt_0_1.
  - unfold sing_complexity. apply pos_INR.
Qed.

Lemma w_stage_positive : forall n : nat, 0 < w_stage n.
Proof.
  intros n. unfold w_stage. apply Rinv_0_lt_compat.
  apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | apply pos_INR].
Qed.

Lemma w_total_positive : forall (X : MotivicSpace) (n : nat), 0 < w_total X n.
Proof.
  intros X n. unfold w_total.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [apply w_dim_positive | apply w_sing_positive].
  - apply w_stage_positive.
Qed.

Lemma w_dim_antitone : forall X Y : MotivicSpace,
  (dimension X <= dimension Y)%nat -> w_dim Y <= w_dim X.
Proof.
  intros X Y Hdim_le. unfold w_dim, nat_to_R. apply Rinv_le_contravar.
  - apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | apply pos_INR].
  - apply Rplus_le_compat_l. apply le_INR; exact Hdim_le.
Qed.

Lemma w_sing_antitone : forall X Y : MotivicSpace,
  (sing_complexity X <= sing_complexity Y)%nat -> w_sing Y <= w_sing X.
Proof.
  intros X Y Hsing_le. unfold w_sing, nat_to_R. apply Rinv_le_contravar.
  - apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | unfold sing_complexity; apply pos_INR].
  - apply Rplus_le_compat_l. apply le_INR; exact Hsing_le.
Qed.

Lemma w_stage_antitone : forall n m : nat,
  (n <= m)%nat -> w_stage m <= w_stage n.
Proof.
  intros n m Hnm_le. unfold w_stage, nat_to_R. apply Rinv_le_contravar.
  - apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | apply pos_INR].
  - apply Rplus_le_compat_l. apply le_INR; exact Hnm_le.
Qed.

Lemma w_dim_mul_w_sing_antitone : forall X Y : MotivicSpace,
  (dimension X <= dimension Y)%nat ->
  (sing_complexity X <= sing_complexity Y)%nat ->
  w_dim Y * w_sing Y <= w_dim X * w_sing X.
Proof.
  intros X Y Hdim_le Hsing_le.
  assert (H_w_dim_Y_le_X : w_dim Y <= w_dim X) by (apply w_dim_antitone; exact Hdim_le).
  assert (H_w_sing_Y_le_X : w_sing Y <= w_sing X) by (apply w_sing_antitone; exact Hsing_le).
  assert (w_dim_X_pos: 0 < w_dim X) by (apply w_dim_positive).
  assert (w_sing_Y_pos: 0 < w_sing Y) by (apply w_sing_positive).
  apply Rle_trans with (r2 := w_dim X * w_sing Y).
  - apply Rmult_le_compat_r; [apply Rlt_le, w_sing_Y_pos | apply H_w_dim_Y_le_X].
  - apply Rmult_le_compat_l; [apply Rlt_le, w_dim_X_pos | apply H_w_sing_Y_le_X].
Qed.

Lemma w_total_antitone : forall X_old X_new : MotivicSpace,
  forall n_old n_new : nat,
  (dimension X_old <= dimension X_new)%nat ->
  (sing_complexity X_old <= sing_complexity X_new)%nat ->
  (n_old <= n_new)%nat ->
  w_total X_new n_new <= w_total X_old n_old.
Proof.
  intros X_old X_new n_old n_new Hdim_le Hsing_le Hn_le. unfold w_total.
  assert (H_geom_prod_antitone : w_dim X_new * w_sing X_new <= w_dim X_old * w_sing X_old)
    by (apply w_dim_mul_w_sing_antitone; assumption).
  assert (H_stage_antitone : w_stage n_new <= w_stage n_old)
    by (apply w_stage_antitone; assumption).
  assert (Product_geom_old_pos : 0 < w_dim X_old * w_sing X_old)
    by (apply Rmult_lt_0_compat; [apply w_dim_positive | apply w_sing_positive]).
  assert (Stage_new_pos : 0 < w_stage n_new) by (apply w_stage_positive).
  apply Rle_trans with (r2 := (w_dim X_old * w_sing X_old) * w_stage n_new).
  - apply Rmult_le_compat_r; [apply Rlt_le, Stage_new_pos | exact H_geom_prod_antitone].
  - apply Rmult_le_compat_l; [apply Rlt_le, Product_geom_old_pos | exact H_stage_antitone].
Qed.

(* Tower Structure and Obstruction Definitions *)
Record PolyApprox : Type := mkPolyApprox {
  poly_approx_space : MotivicSpace;
  poly_approx_stage : nat;
  poly_approx_dim_bound : nat;
  poly_approx_sing_bound : nat
}.

Record WeightedTowerStage : Type := mkWeightedTowerStage {
  wts_poly_approx : PolyApprox;
  wts_factor        : R;
  wts_factor_is_positive : 0 < wts_factor
}.

Definition WeightedMotivicTaylorTower := nat -> WeightedTowerStage.

Definition ObstructionMeasure : Type := R.
Definition ObstructionMeasureSeq : Type := nat -> ObstructionMeasure.

Definition NthLayerMeasure (T : WeightedMotivicTaylorTower) (n : nat) : ObstructionMeasure :=
  match n with
  | O =>
    let pa0 := wts_poly_approx (T O) in
    INR (poly_approx_dim_bound pa0) + INR (poly_approx_sing_bound pa0)
  | S m =>
    let pa_Sm := wts_poly_approx (T (S m)) in
    let pa_m  := wts_poly_approx (T m) in
    Rabs (INR (poly_approx_dim_bound pa_Sm) - INR (poly_approx_dim_bound pa_m)) +
    Rabs (INR (poly_approx_sing_bound pa_Sm) - INR (poly_approx_sing_bound pa_m))
  end.

Definition RecursiveObstructionBoundHolds (T : WeightedMotivicTaylorTower) : Prop :=
  forall n : nat,
    NthLayerMeasure T (S n) <= NthLayerMeasure T n * wts_factor (T n).

Fixpoint CumulativeStageFactorProduct (T : WeightedMotivicTaylorTower) (n : nat) : R :=
  match n with
  | O => 1
  | S k => CumulativeStageFactorProduct T k * wts_factor (T k)
  end.

Lemma CumulativeStageFactorProduct_S (T : WeightedMotivicTaylorTower) (k : nat) :
  CumulativeStageFactorProduct T (S k) = CumulativeStageFactorProduct T k * wts_factor (T k).
Proof.
  simpl. reflexivity.
Qed.

Lemma wts_factor_nonnegative (s : WeightedTowerStage) :
  0 <= wts_factor s.
Proof.
  apply Rlt_le. (* Goal becomes: 0 < wts_factor s *)
  apply (wts_factor_is_positive s). (* Applies the proof term (wts_factor_is_positive s) *)
Qed.

Lemma IteratedObstructionBound (T : WeightedMotivicTaylorTower) :
  RecursiveObstructionBoundHolds T ->
  forall n : nat,
    NthLayerMeasure T n <= NthLayerMeasure T O * CumulativeStageFactorProduct T n.
Proof.
  intros H_recursive_bound n.
  induction n as [| k IHk].
  - (* Base Case: n = 0 *)
    simpl.
    rewrite Rmult_1_r.
    apply Rle_refl.
  - (* Inductive Step: Assume true for k, prove for S k *)
    assert (H_step_bound : NthLayerMeasure T (S k) <= NthLayerMeasure T k * wts_factor (T k))
      by (apply H_recursive_bound).

    apply Rle_trans with (r2 := NthLayerMeasure T k * wts_factor (T k)).
    + (* First part of transitivity *)
      exact H_step_bound.
    + (* Second part of transitivity *)
      rewrite CumulativeStageFactorProduct_S.
      rewrite <- (Rmult_assoc (NthLayerMeasure T O) (CumulativeStageFactorProduct T k) (wts_factor (T k))).
      
      assert (H_factor_nonnegative : 0 <= wts_factor (T k))
        by (apply (wts_factor_nonnegative (T k))).
      
      apply Rmult_le_compat_r. (* Common factor is wts_factor (T k) *)
      -- (* First subgoal (presented by Coq): 0 <= wts_factor (T k) *)
         exact H_factor_nonnegative.
      -- (* Second subgoal (presented by Coq): NthLayerMeasure T k <= NthLayerMeasure T O * CumulativeStageFactorProduct T k *)
         exact IHk.
Qed.

Definition TowerUsesGeometricWeights (T : WeightedMotivicTaylorTower) : Prop :=
  forall k : nat,
    let X_k := poly_approx_space (wts_poly_approx (T k)) in
    wts_factor (T k) = w_total X_k k.
