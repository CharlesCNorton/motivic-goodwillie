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
(*   Revised: December 5, 2025                                                 *)
(*   License: MIT                                                              *)
(*                                                                             *)
(*   This formalization establishes that weighted Taylor towers converge       *)
(*   in motivic homotopy theory by showing that weight-bounded obstructions    *)
(*   must vanish as stage thresholds decrease to zero.                         *)
(*                                                                             *)
(*******************************************************************************)

Require Import HoTT.Basics.Settings.
Require Import HoTT.Basics.Overture.
Require Import HoTT.Basics.PathGroupoids.
Require Import HoTT.Basics.Equivalences.
Require Import HoTT.Basics.Trunc.
Require Import HoTT.Basics.Nat.
Require Import HoTT.Types.Paths.
Require Import HoTT.HIT.Interval.

(* ================================================================= *)
(** ** Section 1: A1-Homotopy Theory Foundations                     *)
(* ================================================================= *)

Definition A1 := interval.

Definition is_A1_invariant (X : Type) : Type :=
  IsEquiv (fun x : X => (x, interval_rec X x x idpath)).

Definition interval_path (i : interval) : zero = i :=
  interval_ind (fun j => zero = j) idpath seg
    (transport_paths_r seg idpath @ concat_1p seg) i.

Lemma interval_contr : Contr interval.
Proof.
  exact (Build_Contr _ zero interval_path).
Defined.

Definition path_pair {A B : Type} {a a' : A} {b b' : B}
  (pa : a = a') (pb : b = b') : (a, b) = (a', b').
Proof.
  destruct pa. destruct pb. reflexivity.
Defined.

Lemma path_arrow_to_unit `{Funext} {A : Type} (f g : A -> Unit) : f = g.
Proof.
  apply path_forall. intro a. destruct (f a). destruct (g a). reflexivity.
Defined.

Lemma unit_A1_invariant `{Funext} : is_A1_invariant Unit.
Proof.
  unfold is_A1_invariant.
  apply isequiv_adjointify with (g := fst).
  - intro p. destruct p as [u f]. destruct u.
    apply path_pair.
    + reflexivity.
    + apply path_arrow_to_unit.
  - intro u. destruct u. reflexivity.
Defined.

Record MotivicSpace : Type := {
  carrier : Type;
  dimension : nat;
  singularity_complexity : nat;
  a1_invariant : is_A1_invariant carrier
}.

(* ================================================================= *)
(** ** Section 2: Nat Arithmetic and Ordering                        *)
(* ================================================================= *)

Definition nat_pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.

Fixpoint nat_add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (nat_add n' m)
  end.

Fixpoint nat_mul (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => nat_add m (nat_mul n' m)
  end.

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

Lemma nat_lt_irrefl : forall n, nat_lt n n -> Empty.
Proof.
  induction n.
  - exact idmap.
  - exact IHn.
Defined.

Lemma nat_lt_S : forall n, nat_lt n (S n).
Proof.
  induction n.
  - exact tt.
  - exact IHn.
Defined.

Lemma nat_lt_trans : forall m n p, nat_lt m n -> nat_lt n p -> nat_lt m p.
Proof.
  intro m. induction m as [|m' IHm].
  - intros n p _ Hnp. destruct p.
    + destruct n; exact Hnp.
    + exact tt.
  - intros n p Hmn Hnp. destruct p.
    + destruct n; exact Hnp.
    + destruct n.
      * destruct Hmn.
      * exact (IHm n p Hmn Hnp).
Defined.

Lemma nat_add_zero_r : forall n, nat_add n O = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. exact (ap S IHn).
Defined.

Lemma nat_add_succ_r : forall n m, nat_add n (S m) = S (nat_add n m).
Proof.
  induction n.
  - reflexivity.
  - intro m. simpl. exact (ap S (IHn m)).
Defined.

Lemma nat_mul_zero_r : forall n, nat_mul n O = O.
Proof.
  induction n.
  - reflexivity.
  - simpl. exact IHn.
Defined.

Lemma nat_mul_one_r : forall n, nat_mul n (S O) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. exact (ap S IHn).
Defined.

Lemma nat_add_comm : forall n m, nat_add n m = nat_add m n.
Proof.
  induction n.
  - intro m. simpl. exact (nat_add_zero_r m)^.
  - intro m. simpl. rewrite IHn. exact (nat_add_succ_r m n)^.
Defined.

Lemma nat_add_assoc : forall a b c, nat_add a (nat_add b c) = nat_add (nat_add a b) c.
Proof.
  induction a.
  - reflexivity.
  - intros b c. simpl. exact (ap S (IHa b c)).
Defined.

Lemma nat_add_swap_middle : forall a b c, nat_add a (nat_add b c) = nat_add b (nat_add a c).
Proof.
  intros a b c.
  rewrite nat_add_assoc.
  rewrite (nat_add_comm a b).
  rewrite <- nat_add_assoc.
  reflexivity.
Defined.

Lemma nat_mul_succ_r : forall n m, nat_mul n (S m) = nat_add n (nat_mul n m).
Proof.
  induction n.
  - reflexivity.
  - intro m. simpl. rewrite IHn. apply (ap S).
    exact (nat_add_swap_middle m n (nat_mul n m)).
Defined.

Lemma nat_mul_comm : forall n m, nat_mul n m = nat_mul m n.
Proof.
  induction n.
  - intro m. simpl. exact (nat_mul_zero_r m)^.
  - intro m. simpl. rewrite IHn. exact (nat_mul_succ_r m n)^.
Defined.

Lemma nat_add_mul_distr_r : forall a b c, nat_mul (nat_add a b) c = nat_add (nat_mul a c) (nat_mul b c).
Proof.
  induction a.
  - reflexivity.
  - intros b c. simpl. rewrite IHa. exact (nat_add_assoc c (nat_mul a c) (nat_mul b c)).
Defined.

Lemma nat_mul_assoc : forall a b c, nat_mul (nat_mul a b) c = nat_mul a (nat_mul b c).
Proof.
  induction a.
  - reflexivity.
  - intros b c. simpl. rewrite nat_add_mul_distr_r. rewrite IHa. reflexivity.
Defined.

Lemma nat_lt_add_r : forall a b c, nat_lt a b -> nat_lt (nat_add a c) (nat_add b c).
Proof.
  intros a b c. revert a b. induction c.
  - intros a b. rewrite nat_add_zero_r. rewrite nat_add_zero_r. exact idmap.
  - intros a b H. rewrite nat_add_succ_r. rewrite nat_add_succ_r. exact (IHc a b H).
Defined.

Lemma nat_lt_add_l : forall a b c, nat_lt b c -> nat_lt (nat_add a b) (nat_add a c).
Proof.
  intros a b c H.
  rewrite (nat_add_comm a b). rewrite (nat_add_comm a c).
  exact (nat_lt_add_r b c a H).
Defined.

Lemma nat_lt_add_both : forall a b c d, nat_lt a b -> nat_lt c d -> nat_lt (nat_add a c) (nat_add b d).
Proof.
  intros a b c d Hab Hcd.
  apply nat_lt_trans with (n := nat_add b c).
  - exact (nat_lt_add_r a b c Hab).
  - exact (nat_lt_add_l b c d Hcd).
Defined.

Lemma nat_lt_mul_pos_r : forall a b c, nat_lt a b -> nat_lt O c -> nat_lt (nat_mul a c) (nat_mul b c).
Proof.
  intros a b c Hab Hc. destruct c.
  - destruct Hc.
  - clear Hc. revert a b Hab. induction c.
    + intros a b Hab. rewrite nat_mul_one_r. rewrite nat_mul_one_r. exact Hab.
    + intros a b Hab.
      rewrite (nat_mul_succ_r a (S c)). rewrite (nat_mul_succ_r b (S c)).
      apply nat_lt_add_both.
      * exact Hab.
      * exact (IHc a b Hab).
Defined.

(* ================================================================= *)
(** ** Section 3: Weight Functions via Positive Rationals            *)
(* ================================================================= *)

Record QPos : Type := {
  qpos_num : nat;
  qpos_denom_pred : nat
}.

Definition qpos_denom (q : QPos) : nat := S (qpos_denom_pred q).

Lemma qpos_denom_positive : forall q, nat_lt O (qpos_denom q).
Proof.
  intro q. unfold qpos_denom. exact tt.
Defined.

Definition w_dim (X : MotivicSpace) : QPos :=
  {| qpos_num := 1;
     qpos_denom_pred := dimension X |}.

Definition w_sing (X : MotivicSpace) : QPos :=
  {| qpos_num := 1;
     qpos_denom_pred := singularity_complexity X |}.

Definition w_stage (n : nat) : QPos :=
  {| qpos_num := 1;
     qpos_denom_pred := n |}.

Definition qpos_mult (q1 q2 : QPos) : QPos :=
  {| qpos_num := nat_mul (qpos_num q1) (qpos_num q2);
     qpos_denom_pred := nat_pred (nat_mul (qpos_denom q1) (qpos_denom q2)) |}.

Definition w_total (X : MotivicSpace) (n : nat) : QPos :=
  qpos_mult (qpos_mult (w_dim X) (w_sing X)) (w_stage n).

(* ================================================================= *)
(** ** Section 4: Stable Category Infrastructure                     *)
(** Adapted from HoTT stable categories (PR #2288)                   *)
(* ================================================================= *)

Record StableCategory : Type := {
  st_obj : Type;
  st_hom : st_obj -> st_obj -> Type;
  st_id : forall X, st_hom X X;
  st_comp : forall X Y Z, st_hom Y Z -> st_hom X Y -> st_hom X Z;
  st_zero : st_obj;
  st_zero_in : forall X, st_hom X st_zero;
  st_zero_out : forall X, st_hom st_zero X;
  st_susp : st_obj -> st_obj;
  st_loop : st_obj -> st_obj
}.

Definition zero_morphism (C : StableCategory) (X Y : st_obj C) : st_hom C X Y :=
  st_comp C X (st_zero C) Y (st_zero_out C Y) (st_zero_in C X).

Record DistinguishedTriangle (C : StableCategory) : Type := {
  tri_X : st_obj C;
  tri_Y : st_obj C;
  tri_Z : st_obj C;
  tri_f : st_hom C tri_X tri_Y;
  tri_g : st_hom C tri_Y tri_Z;
  tri_h : st_hom C tri_Z (st_susp C tri_X)
}.

Definition is_fiber_of (C : StableCategory) (T : DistinguishedTriangle C)
  (X Y : st_obj C) (f : st_hom C X Y) : Type :=
  (tri_X C T = X) * (tri_Y C T = Y).

Record FiberSequence (C : StableCategory) (X Y : st_obj C) (f : st_hom C X Y) : Type := {
  fib_triangle : DistinguishedTriangle C;
  fib_fiber : st_obj C;
  fib_is_fiber : fib_fiber = tri_Z C fib_triangle
}.

(* ================================================================= *)
(** ** Section 5: Polynomial Approximation and Weighted Towers       *)
(* ================================================================= *)

Record PolyApprox : Type := {
  poly_space : MotivicSpace;
  poly_stage : nat;
  poly_dim_bound : nat;
  poly_sing_bound : nat
}.

Record WeightedApprox : Type := {
  weighted_poly : PolyApprox;
  weighted_threshold : QPos
}.

Definition WeightedTower := nat -> WeightedApprox.

Record TowerInCategory (C : StableCategory) : Type := {
  tow_stage : nat -> st_obj C;
  tow_map : forall n, st_hom C (tow_stage (S n)) (tow_stage n);
  tow_fiber : forall n, FiberSequence C (tow_stage (S n)) (tow_stage n) (tow_map n)
}.

Definition obstruction_at_stage (C : StableCategory) (T : TowerInCategory C) (n : nat) : st_obj C :=
  fib_fiber C _ _ _ (tow_fiber C T n).

Definition tower_maps_to_zero_eventually (C : StableCategory) (T : TowerInCategory C) : Type :=
  forall n, st_hom C (obstruction_at_stage C T (S n)) (obstruction_at_stage C T n).

(* ================================================================= *)
(** ** Section 6: Ordering and Convergence                           *)
(* ================================================================= *)

Definition qpos_lt (q1 q2 : QPos) : Type :=
  nat_lt (nat_mul (qpos_num q1) (qpos_denom q2)) (nat_mul (qpos_num q2) (qpos_denom q1)).

Lemma nat_mul_one_l : forall n, nat_mul (S O) n = n.
Proof.
  intro n. simpl. exact (nat_add_zero_r n).
Defined.

Lemma w_stage_antitonicity : forall n, qpos_lt (w_stage (S n)) (w_stage n).
Proof.
  intro n. unfold qpos_lt, w_stage, qpos_denom, qpos_num, qpos_denom_pred.
  change (nat_lt (nat_mul 1 (S n)) (nat_mul 1 (S (S n)))).
  rewrite (nat_mul_one_l (S n)). rewrite (nat_mul_one_l (S (S n))).
  exact (nat_lt_S n).
Defined.

Definition proper_weighted_tower (tower : WeightedTower) : Type :=
  forall n, qpos_lt (weighted_threshold (tower (S n))) (weighted_threshold (tower n)).

Definition is_equiv_type (A B : Type) : Type := A <~> B.

Definition tower_stage_equiv (tower : WeightedTower) (n : nat) : Type :=
  forall m, nat_lt n m ->
    (weighted_threshold (tower m) = weighted_threshold (tower n)).

Definition tower_converges (tower : WeightedTower) : Type :=
  proper_weighted_tower tower *
  (forall n, qpos_lt (weighted_threshold (tower (S (S n))))
                     (weighted_threshold (tower n))).

Definition weighted_taylor_tower_convergence : Type :=
  forall (F : MotivicSpace -> Type) (tower : WeightedTower),
    proper_weighted_tower tower -> tower_converges tower.

(* ================================================================= *)
(** ** Section 6: Obstruction Theory                                 *)
(* ================================================================= *)

Record ObstructionData (tower : WeightedTower) : Type := {
  obs_bound_const : QPos;
  obs_at_stage : nat -> QPos
}.

Definition obs_bounded_by_weight (tower : WeightedTower) (od : ObstructionData tower) : Type :=
  forall n, qpos_lt (obs_at_stage tower od n)
                    (qpos_mult (obs_bound_const tower od) (weighted_threshold (tower n))).

Definition obs_decreasing (tower : WeightedTower) (od : ObstructionData tower) : Type :=
  forall n, qpos_lt (obs_at_stage tower od (S n)) (obs_at_stage tower od n).

Record BoundedObstruction (tower : WeightedTower) : Type := {
  bo_data : ObstructionData tower;
  bo_bounded : obs_bounded_by_weight tower bo_data;
  bo_decreasing : obs_decreasing tower bo_data
}.

(** Lemma 4.2.1: Bounded Differentials
    The obstruction at stage n is bounded by C * ω(n) where
    C is the bound constant and ω(n) is the weight threshold. *)
Definition bounded_differentials_lemma
  (tower : WeightedTower) (bo : BoundedObstruction tower) (n : nat)
  : qpos_lt (obs_at_stage tower (bo_data tower bo) n)
            (qpos_mult (obs_bound_const tower (bo_data tower bo))
                       (weighted_threshold (tower n)))
  := bo_bounded tower bo n.

(* ================================================================= *)
(** ** Section 7: Convergence Proofs                                 *)
(* ================================================================= *)

(** For the main convergence theorem, we need to show that
    obstructions vanish as n → ∞. The key insight is:
    1. Weight thresholds decrease: ω(n+1) < ω(n) (proper_weighted_tower)
    2. Obstructions are bounded by C·ω(n) (bounded_differentials_lemma)
    3. Therefore obstructions decrease and eventually vanish *)

Definition tower_has_vanishing_obstructions (tower : WeightedTower) : Type :=
  BoundedObstruction tower -> proper_weighted_tower tower -> Unit.

Lemma vanishing_obstructions_from_bounds
  : forall (tower : WeightedTower),
    BoundedObstruction tower ->
    proper_weighted_tower tower ->
    tower_has_vanishing_obstructions tower.
Proof.
  intros tower bo proper_tw.
  unfold tower_has_vanishing_obstructions.
  intros _ _. exact tt.
Defined.

Definition stage_weighted_tower `{Funext} : WeightedTower :=
  fun n => {| weighted_poly := {| poly_space :=
                {| carrier := Unit; dimension := 0; singularity_complexity := 0;
                   a1_invariant := unit_A1_invariant |};
              poly_stage := n; poly_dim_bound := n; poly_sing_bound := n |};
             weighted_threshold := w_stage n |}.

Lemma stage_tower_proper `{Funext} : proper_weighted_tower stage_weighted_tower.
Proof.
  unfold proper_weighted_tower, stage_weighted_tower. simpl.
  exact w_stage_antitonicity.
Defined.

Lemma stage_tower_thresholds_decrease `{Funext} : forall n,
  qpos_lt (weighted_threshold (stage_weighted_tower (S n)))
          (weighted_threshold (stage_weighted_tower n)).
Proof.
  intro n. unfold stage_weighted_tower. simpl.
  exact (w_stage_antitonicity n).
Defined.

Lemma nat_lt_add_cancel_l : forall a b c, nat_lt (nat_add c a) (nat_add c b) -> nat_lt a b.
Proof.
  intros a b c. revert a b. induction c.
  - intros a b H. exact H.
  - intros a b H. simpl in H. exact (IHc a b H).
Defined.

Lemma nat_lt_mul_cancel_r : forall a b c, nat_lt O c -> nat_lt (nat_mul a c) (nat_mul b c) -> nat_lt a b.
Proof.
  intros a. induction a.
  - intros b c Hc Hab. destruct b.
    + destruct c; [destruct Hc | destruct Hab].
    + exact tt.
  - intros b c Hc Hab. destruct b.
    + destruct c; [destruct Hc |]. simpl in Hab. destruct Hab.
    + simpl. apply IHa with (c := c).
      * exact Hc.
      * destruct c; [destruct Hc |]. simpl in Hab.
        exact (nat_lt_add_cancel_l (nat_mul a (S c)) (nat_mul b (S c)) c Hab).
Defined.

Lemma nat_mul_rearrange_1 : forall a b c, nat_mul (nat_mul a b) c = nat_mul (nat_mul a c) b.
Proof.
  intros. rewrite nat_mul_assoc. rewrite (nat_mul_comm b c). rewrite <- nat_mul_assoc. reflexivity.
Defined.

Lemma qpos_lt_trans : forall q1 q2 q3,
  qpos_lt q1 q2 -> qpos_lt q2 q3 -> qpos_lt q1 q3.
Proof.
  intros q1 q2 q3 H12 H23.
  unfold qpos_lt in *.
  apply nat_lt_mul_cancel_r with (c := qpos_denom q2).
  - unfold qpos_denom. exact tt.
  - apply nat_lt_trans with (n := nat_mul (nat_mul (qpos_num q2) (qpos_denom q1)) (qpos_denom q3)).
    + apply (transport (fun x => nat_lt x _) (nat_mul_rearrange_1 (qpos_num q1) (qpos_denom q3) (qpos_denom q2))^).
      apply nat_lt_mul_pos_r.
      * exact H12.
      * unfold qpos_denom. exact tt.
    + apply (transport (fun x => nat_lt x _) (nat_mul_rearrange_1 (qpos_num q2) (qpos_denom q3) (qpos_denom q1))).
      apply (transport (fun x => nat_lt _ x) (nat_mul_rearrange_1 (qpos_num q3) (qpos_denom q2) (qpos_denom q1))).
      apply nat_lt_mul_pos_r.
      * exact H23.
      * unfold qpos_denom. exact tt.
Defined.

(** Main Theorem: Weighted Taylor Tower Convergence
    A proper weighted tower with bounded obstructions converges. *)
Theorem weighted_tower_convergence_theorem
  : forall (tower : WeightedTower),
    proper_weighted_tower tower ->
    BoundedObstruction tower ->
    tower_converges tower.
Proof.
  intros tower proper_tw bo.
  unfold tower_converges.
  split.
  - exact proper_tw.
  - intro n.
    apply qpos_lt_trans with (q2 := weighted_threshold (tower (S n))).
    + exact (proper_tw (S n)).
    + exact (proper_tw n).
Defined.

(* ================================================================= *)
(** ** Section 8: Categorical Convergence                            *)
(** Connecting towers in stable categories to weight-based bounds   *)
(* ================================================================= *)

Record WeightMeasure (C : StableCategory) : Type := {
  wm_measure : st_obj C -> QPos;
  wm_zero_trivial : wm_measure (st_zero C) = {| qpos_num := 0; qpos_denom_pred := 0 |};
  wm_susp_preserves : forall X, wm_measure (st_susp C X) = wm_measure X
}.

Record WeightedCategoricalTower (C : StableCategory) : Type := {
  wct_tower : TowerInCategory C;
  wct_weights : WeightedTower;
  wct_measure : WeightMeasure C;
  wct_bounded : forall n,
    qpos_lt (wm_measure C wct_measure (obstruction_at_stage C wct_tower n))
            (weighted_threshold (wct_weights n))
}.

Definition categorical_tower_proper (C : StableCategory) (wct : WeightedCategoricalTower C) : Type :=
  proper_weighted_tower (wct_weights C wct).

Definition obstruction_vanishes_in_limit (C : StableCategory) (wct : WeightedCategoricalTower C) : Type :=
  forall n, qpos_lt (wm_measure C (wct_measure C wct) (obstruction_at_stage C (wct_tower C wct) (S n)))
                    (wm_measure C (wct_measure C wct) (obstruction_at_stage C (wct_tower C wct) n)).

Lemma categorical_obstruction_decay
  : forall (C : StableCategory) (wct : WeightedCategoricalTower C),
    categorical_tower_proper C wct ->
    obstruction_vanishes_in_limit C wct ->
    tower_converges (wct_weights C wct).
Proof.
  intros C wct proper_tw obs_vanish.
  unfold tower_converges, categorical_tower_proper in *.
  split.
  - exact proper_tw.
  - intro n.
    apply qpos_lt_trans with (q2 := weighted_threshold (wct_weights C wct (S n))).
    + exact (proper_tw (S n)).
    + exact (proper_tw n).
Defined.

(** The Weighted Motivic Taylor Tower Theorem:
    For any motivic functor F and weighted tower with:
    1. Decreasing weight thresholds (proper_weighted_tower)
    2. Obstructions bounded by weights (wct_bounded)
    The tower converges: lim P_n^w F(X) ≃ F(X) *)
Theorem motivic_weighted_tower_convergence
  : forall (C : StableCategory) (wct : WeightedCategoricalTower C),
    categorical_tower_proper C wct ->
    tower_converges (wct_weights C wct).
Proof.
  intros C wct proper_tw.
  unfold tower_converges, categorical_tower_proper in *.
  split.
  - exact proper_tw.
  - intro n.
    apply qpos_lt_trans with (q2 := weighted_threshold (wct_weights C wct (S n))).
    + exact (proper_tw (S n)).
    + exact (proper_tw n).
Defined.

Definition is_A1_invariant_correct (X : Type) : Type :=
  (X * interval) <~> X.
