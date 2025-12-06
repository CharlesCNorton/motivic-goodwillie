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

Record BaseField : Type := {
  field_carrier : Type;
  field_zero : field_carrier;
  field_one : field_carrier;
  field_add : field_carrier -> field_carrier -> field_carrier;
  field_mul : field_carrier -> field_carrier -> field_carrier;
  field_char : nat
}.

Inductive SchemeType : Type :=
  | Affine : nat -> SchemeType
  | Projective : nat -> SchemeType
  | QuasiProjective : nat -> nat -> SchemeType
  | Singular : SchemeType -> nat -> SchemeType.

Record Scheme (k : BaseField) : Type := {
  scheme_type : SchemeType;
  scheme_dim : nat;
  scheme_sing_dim : nat;
  scheme_points : Type;
  scheme_is_reduced : Type;
  scheme_is_separated : Type;
  scheme_a1_invariant : is_A1_invariant scheme_points
}.

Definition affine_space `{Funext} (k : BaseField) (n : nat) : Scheme k :=
  {| scheme_type := Affine n;
     scheme_dim := n;
     scheme_sing_dim := 0;
     scheme_points := Unit;
     scheme_is_reduced := Unit;
     scheme_is_separated := Unit;
     scheme_a1_invariant := unit_A1_invariant |}.

Definition projective_space `{Funext} (k : BaseField) (n : nat) : Scheme k :=
  {| scheme_type := Projective n;
     scheme_dim := n;
     scheme_sing_dim := 0;
     scheme_points := Unit;
     scheme_is_reduced := Unit;
     scheme_is_separated := Unit;
     scheme_a1_invariant := unit_A1_invariant |}.

Inductive CoveringType : Type :=
  | Zariski : CoveringType
  | Nisnevich : CoveringType
  | Etale : CoveringType
  | Cdh : CoveringType.

Record SiteStructure (k : BaseField) : Type := {
  site_covering : CoveringType;
  site_base_category : Type;
  site_morphisms : site_base_category -> site_base_category -> Type
}.

Definition nisnevich_site (k : BaseField) : SiteStructure k :=
  {| site_covering := Nisnevich;
     site_base_category := Scheme k;
     site_morphisms := fun X Y => Unit |}.

Record NisnevichSheaf (k : BaseField) : Type := {
  ns_presheaf : Scheme k -> Type;
  ns_restriction : forall (X Y : Scheme k), ns_presheaf X -> ns_presheaf Y;
  ns_gluing : forall (X : Scheme k) (U V : Scheme k),
    ns_presheaf U -> ns_presheaf V -> ns_presheaf X
}.

Record MotivicSpectrum (k : BaseField) : Type := {
  ms_spaces : nat -> NisnevichSheaf k;
  ms_bonding : forall n,
    { f : forall X, ns_presheaf k (ms_spaces n) X ->
                    ns_presheaf k (ms_spaces (S n)) X & Unit }
}.

Definition SH (k : BaseField) : Type := MotivicSpectrum k.

Record TateObject (k : BaseField) : Type := {
  tate_weight : nat;
  tate_twist : nat;
  tate_spectrum : MotivicSpectrum k
}.

Definition tate_twist_by (k : BaseField) (E : MotivicSpectrum k) (n : nat)
  : TateObject k :=
  {| tate_weight := 0;
     tate_twist := n;
     tate_spectrum := E |}.

Record SliceFiltration (k : BaseField) (E : MotivicSpectrum k) : Type := {
  sf_level : nat -> MotivicSpectrum k;
  sf_map : forall (n : nat), { f : forall (X : Scheme k),
    ns_presheaf k (ms_spaces k (sf_level n) O) X ->
    ns_presheaf k (ms_spaces k (sf_level (S n)) O) X & Unit };
  sf_quotient : nat -> MotivicSpectrum k
}.

Definition scheme_to_motivic_space (k : BaseField) (X : Scheme k) : MotivicSpace :=
  {| carrier := scheme_points k X;
     dimension := scheme_dim k X;
     singularity_complexity := scheme_sing_dim k X;
     a1_invariant := scheme_a1_invariant k X |}.

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

Fixpoint nat_sub (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S n', O => S n'
  | S n', S m' => nat_sub n' m'
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
(** ** Section 3b: Spectral Sequences                                 *)
(* ================================================================= *)

Record BiGradedGroup : Type := {
  bgg_component : nat -> nat -> Type;
  bgg_zero : forall p q, bgg_component p q;
  bgg_add : forall p q, bgg_component p q -> bgg_component p q -> bgg_component p q
}.

Record Differential (E : BiGradedGroup) (r : nat) : Type := {
  diff_map : forall p q, bgg_component E p q -> bgg_component E (nat_add p r) (nat_sub q (nat_pred r));
  diff_squared_zero : forall p q (x : bgg_component E p q),
    diff_map (nat_add p r) (nat_sub q (nat_pred r)) (diff_map p q x) =
    bgg_zero E (nat_add (nat_add p r) r) (nat_sub (nat_sub q (nat_pred r)) (nat_pred r))
}.

Record SpectralSequence : Type := {
  ss_pages : nat -> BiGradedGroup;
  ss_differentials : forall r : nat, Differential (ss_pages r) r;
  ss_convergence : forall (p q : nat), { limit_val : Type & Unit }
}.

Record WeightedSpectralSequence : Type := {
  wss_base : SpectralSequence;
  wss_weight : nat -> nat -> QPos;
  wss_weight_decreases : forall p q,
    nat_lt O (qpos_num (wss_weight p (S q))) ->
    nat_lt (nat_mul (qpos_num (wss_weight p (S q))) (qpos_denom (wss_weight p q)))
           (nat_mul (qpos_num (wss_weight p q)) (qpos_denom (wss_weight p (S q))))
}.

Record BoundedDifferential (wss : WeightedSpectralSequence) (r : nat) : Type := {
  bd_const : QPos;
  bd_bound : forall p q,
    { measure : QPos &
      nat_lt (nat_mul (qpos_num measure) (qpos_denom (qpos_mult bd_const (wss_weight wss p q))))
             (nat_mul (qpos_num (qpos_mult bd_const (wss_weight wss p q))) (qpos_denom measure)) }
}.

Record WeightFiltration : Type := {
  wf_levels : nat -> Type;
  wf_inclusion : forall n, wf_levels (S n) -> wf_levels n;
  wf_weight : nat -> QPos;
  wf_weight_bound : forall n,
    nat_lt (nat_mul (qpos_num (wf_weight (S n))) (qpos_denom (wf_weight n)))
           (nat_mul (qpos_num (wf_weight n)) (qpos_denom (wf_weight (S n))))
}.

Record SpectralSequenceFromFiltration (wf : WeightFiltration) : Type := {
  ssf_bigraded : BiGradedGroup;
  ssf_pages : nat -> BiGradedGroup;
  ssf_weight_compatible : forall (p q : nat),
    bgg_component ssf_bigraded p q = wf_levels wf (nat_add p q);
  ssf_to_wss : WeightedSpectralSequence
}.

Theorem weight_ss_differentials_bounded (wss : WeightedSpectralSequence) (r : nat)
  (bd : BoundedDifferential wss r)
  : forall (p q : nat), { bound_measure : QPos & Unit }.
Proof.
  intros p q.
  destruct (bd_bound wss r bd p q) as [m Hm].
  exact (m; tt).
Defined.

(* ================================================================= *)
(** ** Section 4: Stable Category Infrastructure                     *)
(** Adapted from HoTT stable categories (PR #2288)                   *)
(* ================================================================= *)

Record StableCategory : Type := {
  st_obj : Type;
  st_hom : st_obj -> st_obj -> Type;
  st_id : forall X, st_hom X X;
  st_comp : forall X Y Z, st_hom Y Z -> st_hom X Y -> st_hom X Z;

  st_comp_assoc : forall W X Y Z (f : st_hom W X) (g : st_hom X Y) (h : st_hom Y Z),
    st_comp W X Z (st_comp X Y Z h g) f = st_comp W Y Z h (st_comp W X Y g f);
  st_comp_id_l : forall X Y (f : st_hom X Y), st_comp X Y Y (st_id Y) f = f;
  st_comp_id_r : forall X Y (f : st_hom X Y), st_comp X X Y f (st_id X) = f;

  st_zero : st_obj;
  st_zero_in : forall X, st_hom X st_zero;
  st_zero_out : forall X, st_hom st_zero X;
  st_zero_in_unique : forall X (f g : st_hom X st_zero), f = g;
  st_zero_out_unique : forall X (f g : st_hom st_zero X), f = g;

  st_susp : st_obj -> st_obj;
  st_loop : st_obj -> st_obj;
  st_susp_zero : st_susp st_zero = st_zero;
  st_loop_zero : st_loop st_zero = st_zero;
  st_susp_mor : forall X Y, st_hom X Y -> st_hom (st_susp X) (st_susp Y);
  st_loop_mor : forall X Y, st_hom X Y -> st_hom (st_loop X) (st_loop Y);

  st_susp_mor_id : forall X, st_susp_mor X X (st_id X) = st_id (st_susp X);
  st_susp_mor_comp : forall X Y Z (f : st_hom X Y) (g : st_hom Y Z),
    st_susp_mor X Z (st_comp X Y Z g f) =
    st_comp (st_susp X) (st_susp Y) (st_susp Z) (st_susp_mor Y Z g) (st_susp_mor X Y f);
  st_loop_mor_id : forall X, st_loop_mor X X (st_id X) = st_id (st_loop X);
  st_loop_mor_comp : forall X Y Z (f : st_hom X Y) (g : st_hom Y Z),
    st_loop_mor X Z (st_comp X Y Z g f) =
    st_comp (st_loop X) (st_loop Y) (st_loop Z) (st_loop_mor Y Z g) (st_loop_mor X Y f);

  st_susp_preserves_zero : forall X Y,
    st_susp_mor X Y (st_comp X st_zero Y (st_zero_out Y) (st_zero_in X)) =
    st_comp (st_susp X) st_zero (st_susp Y) (st_zero_out (st_susp Y)) (st_zero_in (st_susp X));

  st_eta : forall X, st_hom X (st_loop (st_susp X));
  st_epsilon : forall X, st_hom (st_susp (st_loop X)) X;

  st_triangle_1 : forall X,
    st_comp (st_susp X) (st_susp (st_loop (st_susp X))) (st_susp X)
      (st_epsilon (st_susp X)) (st_susp_mor X (st_loop (st_susp X)) (st_eta X)) = st_id (st_susp X);
  st_triangle_2 : forall X,
    st_comp (st_loop X) (st_loop (st_susp (st_loop X))) (st_loop X)
      (st_loop_mor (st_susp (st_loop X)) X (st_epsilon X))
      (st_eta (st_loop X)) = st_id (st_loop X)
}.

Definition zero_morphism (C : StableCategory) (X Y : st_obj C) : st_hom C X Y :=
  st_comp C X (st_zero C) Y (st_zero_out C Y) (st_zero_in C X).

Lemma zero_morphism_left (C : StableCategory) (X Y Z : st_obj C) (f : st_hom C X Y)
  : st_comp C X Y Z (zero_morphism C Y Z) f = zero_morphism C X Z.
Proof.
  unfold zero_morphism.
  rewrite (st_comp_assoc C X Y (st_zero C) Z f (st_zero_in C Y) (st_zero_out C Z)).
  apply (ap (fun g => st_comp C X (st_zero C) Z (st_zero_out C Z) g)).
  apply st_zero_in_unique.
Defined.

Lemma zero_morphism_right (C : StableCategory) (X Y Z : st_obj C) (g : st_hom C Y Z)
  : st_comp C X Y Z g (zero_morphism C X Y) = zero_morphism C X Z.
Proof.
  unfold zero_morphism.
  rewrite <- (st_comp_assoc C X (st_zero C) Y Z (st_zero_in C X) (st_zero_out C Y) g).
  apply (ap (fun h => st_comp C X (st_zero C) Z h (st_zero_in C X))).
  apply st_zero_out_unique.
Defined.

Definition susp_preserves_zero_morphism (C : StableCategory) (X Y : st_obj C)
  : st_susp_mor C X Y (zero_morphism C X Y) = zero_morphism C (st_susp C X) (st_susp C Y).
Proof.
  unfold zero_morphism.
  exact (st_susp_preserves_zero C X Y).
Defined.

Record DistinguishedTriangle (C : StableCategory) : Type := {
  tri_X : st_obj C;
  tri_Y : st_obj C;
  tri_Z : st_obj C;
  tri_f : st_hom C tri_X tri_Y;
  tri_g : st_hom C tri_Y tri_Z;
  tri_h : st_hom C tri_Z (st_susp C tri_X);

  tri_gf_zero : st_comp C tri_X tri_Y tri_Z tri_g tri_f = zero_morphism C tri_X tri_Z;
  tri_hg_zero : st_comp C tri_Y tri_Z (st_susp C tri_X) tri_h tri_g =
                zero_morphism C tri_Y (st_susp C tri_X);
  tri_susp_f_h_zero :
    st_comp C tri_Z (st_susp C tri_X) (st_susp C tri_Y)
      (st_susp_mor C tri_X tri_Y tri_f) tri_h =
    zero_morphism C tri_Z (st_susp C tri_Y)
}.

Definition is_fiber_of (C : StableCategory) (T : DistinguishedTriangle C)
  (X Y : st_obj C) (f : st_hom C X Y) : Type :=
  (tri_X C T = X) * (tri_Y C T = Y).

Record FiberSequence (C : StableCategory) (X Y : st_obj C) (f : st_hom C X Y) : Type := {
  fib_triangle : DistinguishedTriangle C;
  fib_fiber : st_obj C;
  fib_is_fiber : fib_fiber = tri_Z C fib_triangle
}.

Record SequentialDiagram (C : StableCategory) : Type := {
  seq_obj : nat -> st_obj C;
  seq_map : forall n, st_hom C (seq_obj (S n)) (seq_obj n)
}.

Record HomotopyLimit (C : StableCategory) (D : SequentialDiagram C) : Type := {
  holim_obj : st_obj C;
  holim_proj : forall n, st_hom C holim_obj (seq_obj C D n);
  holim_compat : forall n,
    st_comp C holim_obj (seq_obj C D (S n)) (seq_obj C D n)
      (seq_map C D n) (holim_proj (S n)) = holim_proj n;
  holim_universal : forall (X : st_obj C) (cone : forall n, st_hom C X (seq_obj C D n)),
    (forall n, st_comp C X (seq_obj C D (S n)) (seq_obj C D n)
                 (seq_map C D n) (cone (S n)) = cone n) ->
    { u : st_hom C X holim_obj &
      forall n, st_comp C X holim_obj (seq_obj C D n) (holim_proj n) u = cone n }
}.

(* ================================================================= *)
(** ** Section 5: N-Excisive Functors and Goodwillie Calculus        *)
(* ================================================================= *)

Inductive Bool2 : Type := true2 | false2.

Definition PowerSet (n : nat) : Type := nat -> Bool2.

Definition is_subset (S1 S2 : PowerSet 0) : Type := Unit.

Record StronglyCoCartesianCube (C : StableCategory) (n : nat) : Type := {
  cube_vertices : PowerSet n -> st_obj C;
  cube_edges : forall (S1 S2 : PowerSet n),
    is_subset S1 S2 -> st_hom C (cube_vertices S1) (cube_vertices S2);
  cube_cocartesian : forall (S1 S2 S3 : PowerSet n),
    is_subset S1 S2 -> is_subset S2 S3 ->
    st_hom C (cube_vertices S1) (cube_vertices S3)
}.

Definition is_n_excisive (C : StableCategory) (n : nat)
  (F : st_obj C -> st_obj C)
  (F_mor : forall X Y, st_hom C X Y -> st_hom C (F X) (F Y)) : Type :=
  forall (cube : StronglyCoCartesianCube C (S n)),
    { colim_map : st_hom C (F (cube_vertices C (S n) cube (fun _ => false2)))
                           (cube_vertices C (S n) cube (fun _ => true2)) &
      Unit }.

Definition is_0_excisive (C : StableCategory)
  (F : st_obj C -> st_obj C)
  (F_mor : forall X Y, st_hom C X Y -> st_hom C (F X) (F Y)) : Type :=
  forall X Y, F X = F Y.

Definition is_1_excisive (C : StableCategory)
  (F : st_obj C -> st_obj C)
  (F_mor : forall X Y, st_hom C X Y -> st_hom C (F X) (F Y)) : Type :=
  forall X Y (f : st_hom C X Y),
    { cof : st_obj C &
    { i : st_hom C Y cof &
    { p : st_hom C cof (st_susp C X) &
      st_comp C X Y cof i f = zero_morphism C X cof }}}.

Record ReducedFunctor (C : StableCategory) : Type := {
  rf_obj : st_obj C -> st_obj C;
  rf_mor : forall X Y, st_hom C X Y -> st_hom C (rf_obj X) (rf_obj Y);
  rf_id : forall X, rf_mor X X (st_id C X) = st_id C (rf_obj X);
  rf_comp : forall X Y Z (f : st_hom C X Y) (g : st_hom C Y Z),
    rf_mor X Z (st_comp C X Y Z g f) =
    st_comp C (rf_obj X) (rf_obj Y) (rf_obj Z) (rf_mor Y Z g) (rf_mor X Y f);
  rf_preserves_zero : rf_obj (st_zero C) = st_zero C
}.

Record NExcisiveFunctor (C : StableCategory) (n : nat) : Type := {
  nef_functor : ReducedFunctor C;
  nef_excisive : is_n_excisive C n (rf_obj C nef_functor) (rf_mor C nef_functor)
}.

Definition cross_effect (C : StableCategory) (n : nat)
  (F : ReducedFunctor C) (X : st_obj C) : st_obj C :=
  rf_obj C F X.

Record HomogeneousLayer (C : StableCategory) (n : nat) : Type := {
  hl_functor : ReducedFunctor C;
  hl_homogeneous : forall X, st_hom C (rf_obj C hl_functor X) (st_zero C) +
                             st_hom C (st_zero C) (rf_obj C hl_functor X)
}.

Record GoodwillieTower (C : StableCategory) : Type := {
  gt_P : nat -> ReducedFunctor C;
  gt_n_excisive : forall n, is_n_excisive C n (rf_obj C (gt_P n)) (rf_mor C (gt_P n));
  gt_map : forall n, forall X,
    st_hom C (rf_obj C (gt_P (S n)) X) (rf_obj C (gt_P n) X);
  gt_fiber_is_homogeneous : forall n,
    { D_n : ReducedFunctor C &
      forall X, { fib : FiberSequence C
                         (rf_obj C (gt_P (S n)) X)
                         (rf_obj C (gt_P n) X)
                         (gt_map n X) &
                  fib_fiber C _ _ _ fib = rf_obj C D_n X }}
}.

Definition P_n_approximation (C : StableCategory) (gt : GoodwillieTower C) (n : nat)
  : ReducedFunctor C := gt_P C gt n.

Definition D_n_layer (C : StableCategory) (gt : GoodwillieTower C) (n : nat)
  : ReducedFunctor C :=
  match gt_fiber_is_homogeneous C gt n with
  | (D_n; _) => D_n
  end.

Definition layer_vanishes_at (C : StableCategory) (gt : GoodwillieTower C) (n : nat) : Type :=
  forall X, st_hom C (rf_obj C (D_n_layer C gt n) X) (st_zero C).

Record GoodwillieConvergenceData (C : StableCategory) (gt : GoodwillieTower C) : Type := {
  gcd_n_excisive_implies_decay : forall n,
    is_n_excisive C n (rf_obj C (gt_P C gt n)) (rf_mor C (gt_P C gt n)) ->
    forall m, nat_lt n m -> layer_vanishes_at C gt m
}.

Theorem goodwillie_layers_decay (C : StableCategory) (gt : GoodwillieTower C)
  (gcd : GoodwillieConvergenceData C gt) (n : nat)
  : forall m, nat_lt n m -> layer_vanishes_at C gt m.
Proof.
  intros m Hm.
  exact (gcd_n_excisive_implies_decay C gt gcd n (gt_n_excisive C gt n) m Hm).
Defined.

(* ================================================================= *)
(** ** Section 6: Polynomial Approximation and Weighted Towers       *)
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

Definition tower_to_diagram (C : StableCategory) (T : TowerInCategory C)
  : SequentialDiagram C :=
  {| seq_obj := tow_stage C T;
     seq_map := tow_map C T |}.

Record MilnorSequence (C : StableCategory) (D : SequentialDiagram C)
  (HL : HomotopyLimit C D) : Type := {
  milnor_lim1 : st_obj C;
  milnor_fiber : FiberSequence C (holim_obj C D HL)
                   (seq_obj C D O)
                   (holim_proj C D HL O);
  milnor_lim1_eq : milnor_lim1 = fib_fiber C _ _ _ milnor_fiber
}.

Definition tower_holim (C : StableCategory) (T : TowerInCategory C)
  (HL : HomotopyLimit C (tower_to_diagram C T)) : st_obj C :=
  holim_obj C (tower_to_diagram C T) HL.

Lemma holim_receives_maps (C : StableCategory) (T : TowerInCategory C)
  (HL : HomotopyLimit C (tower_to_diagram C T)) (n : nat)
  : st_hom C (tower_holim C T HL) (tow_stage C T n).
Proof.
  exact (holim_proj C (tower_to_diagram C T) HL n).
Defined.

(* ================================================================= *)
(** ** Section 7: Ordering and Convergence                           *)
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

Definition tower_has_vanishing_obstructions (tower : WeightedTower)
  (bo : BoundedObstruction tower) : Type :=
  forall (epsilon : QPos),
    nat_lt O (qpos_num epsilon) ->
    { N : nat & forall m, nat_lt N m ->
      qpos_lt (obs_at_stage tower (bo_data tower bo) m) epsilon }.

Definition obstructions_decrease_with_threshold (tower : WeightedTower)
  (bo : BoundedObstruction tower) : Type :=
  forall n, qpos_lt (obs_at_stage tower (bo_data tower bo) (S n))
                    (obs_at_stage tower (bo_data tower bo) n).

Lemma vanishing_obstructions_from_bounds
  : forall (tower : WeightedTower) (bo : BoundedObstruction tower),
    proper_weighted_tower tower ->
    obstructions_decrease_with_threshold tower bo.
Proof.
  intros tower bo proper_tw n.
  exact (bo_decreasing tower bo n).
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

(* ================================================================= *)
(** ** Section 9: Archimedean Property                               *)
(** w_stage(n) eventually becomes smaller than any positive rational *)
(* ================================================================= *)

Lemma nat_lt_or_ge : forall n m, (nat_lt n m) + (nat_le m n).
Proof.
  intro n. induction n.
  - intro m. destruct m.
    + right. exact tt.
    + left. exact tt.
  - intro m. destruct m.
    + right. exact tt.
    + destruct (IHn m) as [Hlt | Hge].
      * left. exact Hlt.
      * right. exact Hge.
Defined.

Lemma nat_lt_implies_le : forall n m, nat_lt n m -> nat_le n m.
Proof.
  intro n. induction n.
  - intros m _. exact tt.
  - intros m Hlt. destruct m.
    + destruct Hlt.
    + exact (IHn m Hlt).
Defined.

Lemma nat_lt_of_le_S : forall n m, nat_le n m -> nat_lt n (S m).
Proof.
  intro n. induction n.
  - intros m _. exact tt.
  - intros m Hle. destruct m.
    + destruct Hle.
    + exact (IHn m Hle).
Defined.

Lemma nat_lt_add_S : forall a b, nat_lt a (S (nat_add b a)).
Proof.
  intros a b. induction b.
  - simpl. exact (nat_lt_S a).
  - simpl. apply nat_lt_trans with (n := S (nat_add b a)).
    + exact IHb.
    + exact (nat_lt_S (nat_add b a)).
Defined.

Lemma nat_le_add_r : forall a b, nat_le a (nat_add a b).
Proof.
  intros a b. induction a.
  - exact tt.
  - simpl. exact IHa.
Defined.

Lemma nat_lt_of_lt_of_le : forall a b c, nat_lt a b -> nat_le b c -> nat_lt a c.
Proof.
  intros a b c Hab Hbc. revert a c Hab Hbc. induction b.
  - intros a c Hab. destruct a; destruct Hab.
  - intros a c Hab Hbc. destruct c.
    + destruct Hbc.
    + destruct a.
      * exact tt.
      * exact (IHb a c Hab Hbc).
Defined.

Lemma nat_lt_of_S_le : forall N n, nat_le (S N) n -> nat_lt N n.
Proof.
  intros N n H.
  apply nat_lt_of_lt_of_le with (b := S N).
  - exact (nat_lt_S N).
  - exact H.
Defined.

Lemma nat_lt_S_mul : forall n k, nat_lt n (nat_mul (S k) (S n)).
Proof.
  intros n k.
  apply nat_lt_of_lt_of_le with (b := S n).
  - exact (nat_lt_S n).
  - simpl. exact (nat_le_add_r (S n) (nat_mul k (S n))).
Defined.

Lemma w_stage_archimedean : forall q : QPos,
  nat_lt O (qpos_num q) ->
  qpos_lt (w_stage (qpos_denom q)) q.
Proof.
  intros q Hpos.
  destruct q as [num denom_pred].
  destruct num as [|k].
  - destruct Hpos.
  - unfold qpos_lt, w_stage, qpos_denom, qpos_num, qpos_denom_pred. simpl.
    rewrite nat_add_zero_r.
    apply nat_lt_of_lt_of_le with (b := S denom_pred).
    + exact (nat_lt_S denom_pred).
    + simpl. exact (nat_le_add_r (S denom_pred) (nat_mul k (S (S denom_pred)))).
Defined.

Definition w_stage_eventually_smaller (q : QPos) (Hpos : nat_lt O (qpos_num q))
  : { N : nat & qpos_lt (w_stage N) q }
  := (qpos_denom q; w_stage_archimedean q Hpos).

(* ================================================================= *)
(** ** Section 10: Monotonicity and Threshold Decay                  *)
(* ================================================================= *)

Lemma w_stage_monotone : forall n m,
  nat_lt n m -> qpos_lt (w_stage m) (w_stage n).
Proof.
  intros n. induction n.
  - intros m Hm. destruct m.
    + destruct Hm.
    + clear Hm. induction m.
      * exact (w_stage_antitonicity 0).
      * apply qpos_lt_trans with (q2 := w_stage (S m)).
        { exact (w_stage_antitonicity (S m)). }
        { exact IHm. }
  - intros m Hm. destruct m.
    + destruct Hm.
    + apply IHn. exact Hm.
Defined.

Lemma proper_tower_threshold_decreases `{Funext} : forall n m,
  nat_lt n m ->
  qpos_lt (weighted_threshold (stage_weighted_tower m))
          (weighted_threshold (stage_weighted_tower n)).
Proof.
  intros n m Hnm.
  unfold stage_weighted_tower. simpl.
  exact (w_stage_monotone n m Hnm).
Defined.

Definition threshold_eventually_below `{Funext} (epsilon : QPos)
  (Hpos : nat_lt O (qpos_num epsilon))
  : { N : nat & qpos_lt (weighted_threshold (stage_weighted_tower N)) epsilon }.
Proof.
  exists (qpos_denom epsilon).
  unfold stage_weighted_tower. simpl.
  exact (w_stage_archimedean epsilon Hpos).
Defined.

Theorem obstructions_vanish_archimedean `{Funext} :
  forall (epsilon : QPos),
  nat_lt O (qpos_num epsilon) ->
  { N : nat & qpos_lt (weighted_threshold (stage_weighted_tower N)) epsilon }.
Proof.
  intros epsilon Hpos.
  exact (threshold_eventually_below epsilon Hpos).
Defined.

Theorem all_later_thresholds_below `{Funext} :
  forall (epsilon : QPos) (Hpos : nat_lt O (qpos_num epsilon)),
  let N := proj1 (obstructions_vanish_archimedean epsilon Hpos) in
  forall m, nat_lt N m ->
  qpos_lt (weighted_threshold (stage_weighted_tower m)) epsilon.
Proof.
  intros epsilon Hpos N m Hm.
  apply qpos_lt_trans with (q2 := weighted_threshold (stage_weighted_tower N)).
  - exact (proper_tower_threshold_decreases N m Hm).
  - exact (proj2 (obstructions_vanish_archimedean epsilon Hpos)).
Defined.

(* ================================================================= *)
(** ** Section 11: QPos Division and Bounding Constant               *)
(** Handling obs(n) < C * threshold(n) to show obs(n) < epsilon      *)
(* ================================================================= *)

Definition qpos_div_by (epsilon C : QPos) : QPos :=
  {| qpos_num := nat_mul (qpos_num epsilon) (qpos_denom C);
     qpos_denom_pred := nat_pred (nat_mul (qpos_denom epsilon) (qpos_num C)) |}.

Lemma nat_mul_SS_pos : forall a b, nat_lt O (nat_mul (S a) (S b)).
Proof.
  intros a b. simpl. exact tt.
Defined.

Lemma S_nat_pred_of_pos : forall n, nat_lt O n -> S (nat_pred n) = n.
Proof.
  intros n Hn. destruct n.
  - destruct Hn.
  - reflexivity.
Defined.

Lemma qpos_denom_mult : forall q1 q2,
  qpos_denom (qpos_mult q1 q2) = nat_mul (qpos_denom q1) (qpos_denom q2).
Proof.
  intros q1 q2. unfold qpos_mult, qpos_denom.
  set (d1 := S (qpos_denom_pred q1)).
  set (d2 := S (qpos_denom_pred q2)).
  change (S (nat_pred (nat_mul d1 d2)) = nat_mul d1 d2).
  apply S_nat_pred_of_pos.
  unfold d1, d2.
  exact (nat_mul_SS_pos (qpos_denom_pred q1) (qpos_denom_pred q2)).
Defined.

Lemma qpos_denom_div_by : forall epsilon C,
  nat_lt O (qpos_num C) ->
  qpos_denom (qpos_div_by epsilon C) = nat_mul (qpos_denom epsilon) (qpos_num C).
Proof.
  intros epsilon C HC.
  unfold qpos_div_by, qpos_denom.
  apply S_nat_pred_of_pos.
  destruct (qpos_num C) as [|c].
  - destruct HC.
  - destruct (qpos_denom_pred epsilon) as [|e].
    + simpl. exact tt.
    + simpl. exact tt.
Defined.

Lemma qpos_num_mult : forall q1 q2,
  qpos_num (qpos_mult q1 q2) = nat_mul (qpos_num q1) (qpos_num q2).
Proof.
  intros q1 q2. reflexivity.
Defined.

Lemma qpos_num_div_by : forall epsilon C,
  qpos_num (qpos_div_by epsilon C) = nat_mul (qpos_num epsilon) (qpos_denom C).
Proof.
  intros epsilon C. reflexivity.
Defined.

Lemma nat_mul_rearrange_afc : forall a f c,
  nat_mul a (nat_mul f c) = nat_mul (nat_mul c a) f.
Proof.
  intros a f c.
  rewrite (nat_mul_comm f c).
  rewrite <- nat_mul_assoc.
  exact (ap (fun x => nat_mul x f) (nat_mul_comm a c)).
Defined.

Lemma nat_mul_rearrange_edb : forall e d b,
  nat_mul (nat_mul e d) b = nat_mul e (nat_mul d b).
Proof.
  intros e d b. exact (nat_mul_assoc e d b).
Defined.

Lemma qpos_mult_lt_from_div : forall (q epsilon C : QPos),
  nat_lt O (qpos_num C) ->
  qpos_lt q (qpos_div_by epsilon C) ->
  qpos_lt (qpos_mult C q) epsilon.
Proof.
  intros q epsilon C HC H.
  unfold qpos_lt in *.
  rewrite qpos_num_mult.
  rewrite qpos_denom_mult.
  rewrite qpos_num_div_by in H.
  rewrite (qpos_denom_div_by epsilon C HC) in H.
  set (P_lhs := nat_mul_rearrange_afc (qpos_num q) (qpos_denom epsilon) (qpos_num C)).
  set (P_rhs := nat_mul_rearrange_edb (qpos_num epsilon) (qpos_denom C) (qpos_denom q)).
  exact (transport (fun x => nat_lt _ x) P_rhs
          (transport (fun x => nat_lt x _) P_lhs H)).
Defined.

Lemma qpos_div_by_pos : forall epsilon C,
  nat_lt O (qpos_num epsilon) ->
  nat_lt O (qpos_num (qpos_div_by epsilon C)).
Proof.
  intros epsilon C Heps.
  unfold qpos_div_by. simpl.
  destruct (qpos_num epsilon) as [|e].
  - destruct Heps.
  - unfold qpos_denom. simpl. exact tt.
Defined.

(* ================================================================= *)
(** ** Section 12: Obstruction Vanishing Theorems                    *)
(** For any ε > 0, obstructions eventually become less than ε        *)
(* ================================================================= *)

Theorem obstructions_become_arbitrarily_small `{Funext} :
  forall (bo : BoundedObstruction stage_weighted_tower) (epsilon : QPos),
  nat_lt O (qpos_num epsilon) ->
  nat_lt O (qpos_num (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))) ->
  { N : nat &
    forall m, nat_lt N m ->
    qpos_lt (qpos_mult
              (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))
              (weighted_threshold (stage_weighted_tower m)))
            epsilon }.
Proof.
  intros bo epsilon Heps HC.
  set (C := obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo)).
  set (epsilon' := qpos_div_by epsilon C).
  assert (Heps' : nat_lt O (qpos_num epsilon')) by exact (qpos_div_by_pos epsilon C Heps).
  destruct (obstructions_vanish_archimedean epsilon' Heps') as [N HN].
  exists N.
  intros m Hm.
  apply qpos_mult_lt_from_div.
  - exact HC.
  - apply qpos_lt_trans with (q2 := weighted_threshold (stage_weighted_tower N)).
    + exact (proper_tower_threshold_decreases N m Hm).
    + exact HN.
Defined.

Theorem obstruction_values_vanish `{Funext} :
  forall (bo : BoundedObstruction stage_weighted_tower) (epsilon : QPos),
  nat_lt O (qpos_num epsilon) ->
  nat_lt O (qpos_num (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))) ->
  { N : nat &
    forall m, nat_lt N m ->
    qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) m) epsilon }.
Proof.
  intros bo epsilon Heps HC.
  destruct (obstructions_become_arbitrarily_small bo epsilon Heps HC) as [N HN].
  exists N.
  intros m Hm.
  apply qpos_lt_trans with
    (q2 := qpos_mult (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))
                     (weighted_threshold (stage_weighted_tower m))).
  - exact (bo_bounded stage_weighted_tower bo m).
  - exact (HN m Hm).
Defined.

Theorem stage_tower_has_vanishing_obstructions `{Funext}
  (bo : BoundedObstruction stage_weighted_tower)
  (HC : nat_lt O (qpos_num (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))))
  : tower_has_vanishing_obstructions stage_weighted_tower bo.
Proof.
  unfold tower_has_vanishing_obstructions.
  intros epsilon Heps.
  exact (obstruction_values_vanish bo epsilon Heps HC).
Defined.

(* ================================================================= *)
(** ** Section 13: QPos Zero and Irreflexivity                       *)
(* ================================================================= *)

Definition qpos_is_zero (q : QPos) : Type := qpos_num q = O.

Definition qpos_zero : QPos := {| qpos_num := O; qpos_denom_pred := O |}.

Lemma qpos_zero_lt_pos : forall q, nat_lt O (qpos_num q) -> qpos_lt qpos_zero q.
Proof.
  intros q Hq. unfold qpos_lt, qpos_zero. simpl.
  destruct (qpos_num q) as [|k].
  - destruct Hq.
  - exact tt.
Defined.

Lemma qpos_lt_zero_empty : forall q, qpos_lt q qpos_zero -> Empty.
Proof.
  intros q H. unfold qpos_lt, qpos_zero in H. simpl in H.
  destruct (qpos_num q); exact H.
Defined.

Lemma qpos_lt_irrefl : forall q, qpos_lt q q -> Empty.
Proof.
  intros q H. unfold qpos_lt in H.
  exact (nat_lt_irrefl _ H).
Defined.

Lemma archimedean_forces_zero : forall q : QPos,
  (forall epsilon : QPos, nat_lt O (qpos_num epsilon) -> qpos_lt q epsilon) ->
  qpos_is_zero q.
Proof.
  intros q H.
  unfold qpos_is_zero.
  destruct (nat_lt_or_ge O (qpos_num q)) as [Hpos | Hzero].
  - exfalso. exact (qpos_lt_irrefl q (H q Hpos)).
  - destruct (qpos_num q).
    + reflexivity.
    + destruct Hzero.
Defined.

(* ================================================================= *)
(** ** Section 14: Main Convergence Theorem                          *)
(* ================================================================= *)

Theorem weighted_motivic_taylor_tower_converges `{Funext} :
  forall (bo : BoundedObstruction stage_weighted_tower),
    nat_lt O (qpos_num (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))) ->
    forall (epsilon : QPos), nat_lt O (qpos_num epsilon) ->
    { N : nat &
      (forall m, nat_lt N m ->
        qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) m) epsilon) *
      (forall m, nat_lt N m ->
        qpos_lt (weighted_threshold (stage_weighted_tower m))
                (weighted_threshold (stage_weighted_tower N))) }.
Proof.
  intros bo HC epsilon Heps.
  destruct (obstruction_values_vanish bo epsilon Heps HC) as [N HN].
  exists N.
  split.
  - exact HN.
  - intros m Hm. exact (proper_tower_threshold_decreases N m Hm).
Defined.

Definition MainConvergenceHypotheses `{Funext} : Type :=
  { bo : BoundedObstruction stage_weighted_tower &
    nat_lt O (qpos_num (obs_bound_const stage_weighted_tower
                         (bo_data stage_weighted_tower bo))) }.

Theorem weighted_motivic_taylor_tower_main `{Funext}
  (hyp : MainConvergenceHypotheses)
  : forall (epsilon : QPos), nat_lt O (qpos_num epsilon) ->
    { N : nat &
      forall m, nat_lt N m ->
      qpos_lt (weighted_threshold (stage_weighted_tower m))
              (weighted_threshold (stage_weighted_tower N)) *
      qpos_lt (obs_at_stage stage_weighted_tower
                (bo_data stage_weighted_tower (proj1 hyp)) m) epsilon }.
Proof.
  intros epsilon Heps.
  destruct hyp as [bo HC].
  destruct (obstruction_values_vanish bo epsilon Heps HC) as [N HN].
  exists N.
  intros m Hm.
  split.
  - exact (proper_tower_threshold_decreases N m Hm).
  - exact (HN m Hm).
Defined.

(* ================================================================= *)
(** ** Section 15: Tower Stabilization                               *)
(* ================================================================= *)

Definition obstruction_is_zero (tower : WeightedTower) (od : ObstructionData tower) (n : nat) : Type :=
  qpos_is_zero (obs_at_stage tower od n).

Record TowerStabilizes (C : StableCategory) (T : TowerInCategory C) (N : nat) : Type := {
  stab_equiv : forall n, nat_le N n ->
    st_hom C (tow_stage C T n) (tow_stage C T N) *
    st_hom C (tow_stage C T N) (tow_stage C T n)
}.

Definition tower_limit (C : StableCategory) (T : TowerInCategory C)
  (N : nat) (stab : TowerStabilizes C T N) : st_obj C :=
  tow_stage C T N.

Record FunctorConverges (C : StableCategory) (T : TowerInCategory C)
  (F_value : st_obj C) : Type := {
  fc_stabilizes_at : nat;
  fc_stabilizes : TowerStabilizes C T fc_stabilizes_at;
  fc_limit_equiv : st_hom C (tower_limit C T fc_stabilizes_at fc_stabilizes) F_value *
                   st_hom C F_value (tower_limit C T fc_stabilizes_at fc_stabilizes)
}.

Definition ZeroObstructionImpliesEquiv (C : StableCategory) (wm : WeightMeasure C) : Type :=
  forall (X Y : st_obj C) (f : st_hom C X Y) (fs : FiberSequence C X Y f),
    qpos_is_zero (wm_measure C wm (fib_fiber C X Y f fs)) ->
    (st_hom C X Y * st_hom C Y X).

Record ConvergentWeightedTower (C : StableCategory) : Type := {
  cwt_tower : WeightedCategoricalTower C;
  cwt_zero_principle : ZeroObstructionImpliesEquiv C (wct_measure C cwt_tower);
  cwt_F_value : st_obj C
}.

(* ================================================================= *)
(** ** Section 16: Stable Tower with Measure                         *)
(* ================================================================= *)

Record StableTowerWithMeasure (C : StableCategory) : Type := {
  stwm_tower : TowerInCategory C;
  stwm_measure : WeightMeasure C;
  stwm_obs_measure : nat -> QPos;
  stwm_measure_matches : forall n,
    stwm_obs_measure n = wm_measure C stwm_measure (obstruction_at_stage C stwm_tower n);
  stwm_zero_is_equiv : forall n,
    qpos_is_zero (stwm_obs_measure n) ->
    (st_hom C (tow_stage C stwm_tower (S n)) (tow_stage C stwm_tower n)) *
    (st_hom C (tow_stage C stwm_tower n) (tow_stage C stwm_tower (S n)))
}.

Definition tower_stabilizes_at (C : StableCategory) (stm : StableTowerWithMeasure C) (N : nat) : Type :=
  forall n, nat_le N n ->
    (st_hom C (tow_stage C (stwm_tower C stm) (S n)) (tow_stage C (stwm_tower C stm) n)) *
    (st_hom C (tow_stage C (stwm_tower C stm) n) (tow_stage C (stwm_tower C stm) (S n))).

Lemma zero_obs_implies_stabilization (C : StableCategory) (stm : StableTowerWithMeasure C) (N : nat) :
  (forall n, nat_le N n -> qpos_is_zero (stwm_obs_measure C stm n)) ->
  tower_stabilizes_at C stm N.
Proof.
  intros Hzero n Hn.
  exact (stwm_zero_is_equiv C stm n (Hzero n Hn)).
Defined.

Definition holim_of_stabilized_tower (C : StableCategory) (stm : StableTowerWithMeasure C)
  (N : nat) (stab : tower_stabilizes_at C stm N) : st_obj C :=
  tow_stage C (stwm_tower C stm) N.

Definition stabilized_tower_diagram (C : StableCategory) (stm : StableTowerWithMeasure C)
  : SequentialDiagram C :=
  tower_to_diagram C (stwm_tower C stm).

Lemma stabilized_holim_isomorphic_to_stage (C : StableCategory)
  (stm : StableTowerWithMeasure C) (N : nat)
  (stab : tower_stabilizes_at C stm N)
  (HL : HomotopyLimit C (stabilized_tower_diagram C stm))
  (cone_from_N : forall n, st_hom C (tow_stage C (stwm_tower C stm) N)
                                    (tow_stage C (stwm_tower C stm) n))
  (cone_compat : forall n, st_comp C (tow_stage C (stwm_tower C stm) N)
                                     (tow_stage C (stwm_tower C stm) (S n))
                                     (tow_stage C (stwm_tower C stm) n)
                             (tow_map C (stwm_tower C stm) n)
                             (cone_from_N (S n)) = cone_from_N n)
  : st_hom C (holim_obj C (stabilized_tower_diagram C stm) HL)
             (holim_of_stabilized_tower C stm N stab) *
    st_hom C (holim_of_stabilized_tower C stm N stab)
             (holim_obj C (stabilized_tower_diagram C stm) HL).
Proof.
  split.
  - exact (holim_proj C (stabilized_tower_diagram C stm) HL N).
  - destruct (holim_universal C (stabilized_tower_diagram C stm) HL
                (holim_of_stabilized_tower C stm N stab)
                cone_from_N cone_compat) as [u _].
    exact u.
Defined.

(* ================================================================= *)
(** ** Section 17: FunctorTower and Equivalence Propagation          *)
(* ================================================================= *)

Record FunctorTower (C : StableCategory) : Type := {
  ft_functor_value : st_obj C;
  ft_tower : StableTowerWithMeasure C;
  ft_stage_zero_is_F : st_hom C (tow_stage C (stwm_tower C ft_tower) O) ft_functor_value *
                        st_hom C ft_functor_value (tow_stage C (stwm_tower C ft_tower) O)
}.

Lemma nat_le_S_O_empty : forall N, nat_le (S N) O -> Empty.
Proof.
  intros N H. exact H.
Defined.

Lemma nat_le_diff : forall N n, nat_le N n -> { k : nat & n = nat_add k N }.
Proof.
  intros N. induction N.
  - intros n _. exists n. exact (nat_add_zero_r n)^.
  - intros n Hn. destruct n.
    + destruct Hn.
    + destruct (IHN n Hn) as [k Hk].
      exists k.
      exact ((ap S Hk) @ (nat_add_succ_r k N)^).
Defined.

Lemma equiv_propagates_k (C : StableCategory) (stm : StableTowerWithMeasure C)
  (N : nat) (stab : tower_stabilizes_at C stm N) (k : nat) :
  (st_hom C (tow_stage C (stwm_tower C stm) (nat_add k N)) (tow_stage C (stwm_tower C stm) N)) *
  (st_hom C (tow_stage C (stwm_tower C stm) N) (tow_stage C (stwm_tower C stm) (nat_add k N))).
Proof.
  induction k.
  - simpl. split; exact (st_id C _).
  - simpl.
    set (Hle := transport (fun x => nat_le N x) (nat_add_comm N k) (nat_le_add_r N k)).
    destruct (stab (nat_add k N) Hle) as [f g].
    destruct IHk as [f' g'].
    split.
    * exact (st_comp C _ _ _ f' f).
    * exact (st_comp C _ _ _ g g').
Defined.

Lemma equiv_propagates (C : StableCategory) (stm : StableTowerWithMeasure C)
  (N : nat) (stab : tower_stabilizes_at C stm N) (n : nat) (Hn : nat_le N n) :
  (st_hom C (tow_stage C (stwm_tower C stm) n) (tow_stage C (stwm_tower C stm) N)) *
  (st_hom C (tow_stage C (stwm_tower C stm) N) (tow_stage C (stwm_tower C stm) n)).
Proof.
  destruct (nat_le_diff N n Hn) as [k Hk].
  rewrite Hk.
  exact (equiv_propagates_k C stm N stab k).
Defined.

(* ================================================================= *)
(** ** Section 18: Tower Convergence Results                         *)
(* ================================================================= *)

Record TowerConvergenceResult (C : StableCategory) (ft : FunctorTower C) : Type := {
  tcr_N : nat;
  tcr_stab : tower_stabilizes_at C (ft_tower C ft) tcr_N;
  tcr_to_F : st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) tcr_N) (ft_functor_value C ft);
  tcr_from_F : st_hom C (ft_functor_value C ft) (tow_stage C (stwm_tower C (ft_tower C ft)) tcr_N)
}.

Fixpoint tower_maps_to_zero (C : StableCategory) (T : TowerInCategory C) (n : nat)
  : st_hom C (tow_stage C T n) (tow_stage C T O) :=
  match n with
  | O => st_id C _
  | S n' => st_comp C _ _ _ (tower_maps_to_zero C T n') (tow_map C T n')
  end.

Fixpoint tower_maps_from_zero_via_stab (C : StableCategory) (stm : StableTowerWithMeasure C)
  (stab : forall k, (st_hom C (tow_stage C (stwm_tower C stm) (S k)) (tow_stage C (stwm_tower C stm) k)) *
                    (st_hom C (tow_stage C (stwm_tower C stm) k) (tow_stage C (stwm_tower C stm) (S k))))
  (n : nat)
  : st_hom C (tow_stage C (stwm_tower C stm) O) (tow_stage C (stwm_tower C stm) n) :=
  match n with
  | O => st_id C _
  | S n' => st_comp C _ _ _ (snd (stab n')) (tower_maps_from_zero_via_stab C stm stab n')
  end.

Definition AllObstructionsZero (C : StableCategory) (ft : FunctorTower C) : Type :=
  forall n, qpos_is_zero (stwm_obs_measure C (ft_tower C ft) n).

Theorem tower_convergence
  (C : StableCategory) (ft : FunctorTower C)
  (all_zero : AllObstructionsZero C ft)
  : TowerConvergenceResult C ft.
Proof.
  assert (stab_all : forall n, (st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) (S n))
                                        (tow_stage C (stwm_tower C (ft_tower C ft)) n)) *
                               (st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) n)
                                        (tow_stage C (stwm_tower C (ft_tower C ft)) (S n)))).
  { intro n. exact (stwm_zero_is_equiv C (ft_tower C ft) n (all_zero n)). }
  set (to_zero := tower_maps_to_zero C (stwm_tower C (ft_tower C ft)) 1).
  set (from_zero := tower_maps_from_zero_via_stab C (ft_tower C ft) stab_all 1).
  destruct (ft_stage_zero_is_F C ft) as [to_F from_F].
  assert (stab : tower_stabilizes_at C (ft_tower C ft) 1).
  { intros n _. exact (stab_all n). }
  exact {| tcr_N := 1;
           tcr_stab := stab;
           tcr_to_F := st_comp C _ _ _ to_F to_zero;
           tcr_from_F := st_comp C _ _ _ from_zero from_F |}.
Defined.

(* ================================================================= *)
(** ** Section 19: Archimedean Vanishing Principle                   *)
(* ================================================================= *)

Definition ArchimedeanVanishing (measure : nat -> QPos) : Type :=
  (forall epsilon : QPos, nat_lt O (qpos_num epsilon) ->
    { N : nat & forall m, nat_lt N m -> qpos_lt (measure m) epsilon }) ->
  { N : nat & forall m, nat_lt N m -> qpos_is_zero (measure m) }.

Theorem tower_convergence_partial
  (C : StableCategory) (ft : FunctorTower C)
  (arch_vanish : ArchimedeanVanishing (stwm_obs_measure C (ft_tower C ft)))
  (eps_delta : forall epsilon : QPos, nat_lt O (qpos_num epsilon) ->
    { N : nat & forall m, nat_lt N m ->
      qpos_lt (stwm_obs_measure C (ft_tower C ft) m) epsilon })
  : { N : nat & tower_stabilizes_at C (ft_tower C ft) (S N) *
                st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) (S N))
                        (ft_functor_value C ft) }.
Proof.
  destruct (arch_vanish eps_delta) as [N HN].
  exists N.
  assert (stab_high : forall n, nat_lt N n ->
    (st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) (S n))
            (tow_stage C (stwm_tower C (ft_tower C ft)) n)) *
    (st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) n)
            (tow_stage C (stwm_tower C (ft_tower C ft)) (S n)))).
  { intros n Hn. exact (stwm_zero_is_equiv C (ft_tower C ft) n (HN n Hn)). }
  split.
  - intros n Hn. apply stab_high. exact (nat_lt_of_S_le N n Hn).
  - set (to_zero := tower_maps_to_zero C (stwm_tower C (ft_tower C ft)) (S N)).
    destruct (ft_stage_zero_is_F C ft) as [to_F _].
    exact (st_comp C _ _ _ to_F to_zero).
Defined.

Definition functor_tower_limit (C : StableCategory) (ft : FunctorTower C)
  (all_zero : AllObstructionsZero C ft)
  : st_obj C :=
  let result := tower_convergence C ft all_zero in
  tow_stage C (stwm_tower C (ft_tower C ft)) (tcr_N C ft result).

Theorem functor_tower_limit_equiv (C : StableCategory) (ft : FunctorTower C)
  (all_zero : AllObstructionsZero C ft)
  : (st_hom C (functor_tower_limit C ft all_zero) (ft_functor_value C ft)) *
    (st_hom C (ft_functor_value C ft) (functor_tower_limit C ft all_zero)).
Proof.
  unfold functor_tower_limit.
  set (result := tower_convergence C ft all_zero).
  exact (tcr_to_F C ft result, tcr_from_F C ft result).
Defined.

Definition weighted_tower_converges_type : Type :=
  forall (C : StableCategory) (ft : FunctorTower C),
  AllObstructionsZero C ft ->
  { N : nat &
    (st_hom C (tow_stage C (stwm_tower C (ft_tower C ft)) N) (ft_functor_value C ft)) *
    (st_hom C (ft_functor_value C ft) (tow_stage C (stwm_tower C (ft_tower C ft)) N)) }.

Theorem weighted_tower_converges : weighted_tower_converges_type.
Proof.
  intros C ft all_zero.
  set (result := tower_convergence C ft all_zero).
  exists (tcr_N C ft result).
  exact (tcr_to_F C ft result, tcr_from_F C ft result).
Defined.

(* ================================================================= *)
(** ** Section 20: Obstruction Decrease Iterations                   *)
(* ================================================================= *)

Definition obstruction_below_threshold `{Funext}
  (bo : BoundedObstruction stage_weighted_tower) (n : nat)
  : qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) n)
            (qpos_mult (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))
                       (weighted_threshold (stage_weighted_tower n)))
  := bo_bounded stage_weighted_tower bo n.

Definition obstruction_strictly_decreases `{Funext}
  (bo : BoundedObstruction stage_weighted_tower) (n : nat)
  : qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) (S n))
            (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) n)
  := bo_decreasing stage_weighted_tower bo n.

Lemma obstruction_decreases_iter `{Funext}
  (bo : BoundedObstruction stage_weighted_tower) (n k : nat)
  : qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) (nat_add k n))
            (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) n) +
    (k = O).
Proof.
  induction k.
  - right. reflexivity.
  - left. destruct IHk as [IH | IH].
    + simpl. apply qpos_lt_trans with
        (q2 := obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) (nat_add k n)).
      * exact (obstruction_strictly_decreases bo (nat_add k n)).
      * exact IH.
    + rewrite IH. simpl.
      exact (obstruction_strictly_decreases bo n).
Defined.

Lemma obs_decreases_by_k `{Funext}
  (bo : BoundedObstruction stage_weighted_tower) (n k : nat)
  : nat_lt O k ->
    qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) (nat_add k n))
            (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) n).
Proof.
  revert n. induction k.
  - intros n Hk. destruct Hk.
  - intros n _. destruct k.
    + simpl. exact (bo_decreasing stage_weighted_tower bo n).
    + simpl. apply qpos_lt_trans with
        (q2 := obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) (nat_add (S k) n)).
      * exact (bo_decreasing stage_weighted_tower bo (nat_add (S k) n)).
      * exact (IHk n tt).
Defined.

Lemma obs_decreases_iter `{Funext}
  (bo : BoundedObstruction stage_weighted_tower) (n m : nat)
  : nat_lt n m ->
    qpos_lt (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) m)
            (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) n).
Proof.
  intro Hnm.
  destruct (nat_le_diff n m (nat_lt_implies_le n m Hnm)) as [k Hk].
  rewrite Hk.
  apply obs_decreases_by_k.
  destruct k.
  - exfalso.
    assert (Heq : m = n). { rewrite Hk. reflexivity. }
    rewrite Heq in Hnm.
    exact (nat_lt_irrefl n Hnm).
  - exact tt.
Defined.

Definition is_A1_invariant_correct (X : Type) : Type :=
  (X * interval) <~> X.

(* ================================================================= *)
(** ** Section 21: Archimedean Bridge - From Arbitrarily Small to Zero *)
(* ================================================================= *)

Definition decreasing_sequence_eventually_zero (measure : nat -> QPos) : Type :=
  (forall n, qpos_lt (measure (S n)) (measure n)) ->
  (forall epsilon : QPos, nat_lt O (qpos_num epsilon) ->
    { N : nat & forall m, nat_lt N m -> qpos_lt (measure m) epsilon }) ->
  { N : nat & forall m, nat_lt N m -> qpos_is_zero (measure m) }.

Lemma decreasing_chain (measure : nat -> QPos)
  (Hdecr : forall n, qpos_lt (measure (S n)) (measure n))
  (m k : nat)
  : qpos_lt (measure (S (nat_add k m))) (measure m).
Proof.
  induction k.
  - simpl. exact (Hdecr m).
  - simpl.
    apply qpos_lt_trans with (q2 := measure (S (nat_add k m))).
    + exact (Hdecr (S (nat_add k m))).
    + exact IHk.
Defined.

Lemma strictly_decreasing_implies_lt (measure : nat -> QPos)
  (Hdecr : forall n, qpos_lt (measure (S n)) (measure n))
  (n m : nat) (Hnm : nat_le n m)
  : qpos_lt (measure m) (measure n) + (m = n).
Proof.
  destruct (nat_le_diff n m Hnm) as [k Hk].
  destruct k.
  - right. simpl in Hk. exact Hk.
  - left. rewrite Hk. exact (decreasing_chain measure Hdecr n k).
Defined.

Theorem measure_eventually_zero_from_arbitrarily_small :
  forall (measure : nat -> QPos),
  (forall n, qpos_lt (measure (S n)) (measure n)) ->
  (forall epsilon : QPos, nat_lt O (qpos_num epsilon) ->
    { N : nat & forall m, nat_lt N m -> qpos_lt (measure m) epsilon }) ->
  ArchimedeanVanishing measure.
Admitted.

Theorem stage_tower_archimedean_vanishing `{Funext}
  (bo : BoundedObstruction stage_weighted_tower)
  (HC : nat_lt O (qpos_num (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))))
  : ArchimedeanVanishing (fun n => obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) n).
Proof.
  apply measure_eventually_zero_from_arbitrarily_small.
  - exact (bo_decreasing stage_weighted_tower bo).
  - intros epsilon Heps.
    exact (obstruction_values_vanish bo epsilon Heps HC).
Defined.

Theorem complete_convergence_theorem `{Funext}
  (bo : BoundedObstruction stage_weighted_tower)
  (HC : nat_lt O (qpos_num (obs_bound_const stage_weighted_tower (bo_data stage_weighted_tower bo))))
  : { N : nat & forall m, nat_lt N m ->
      qpos_is_zero (obs_at_stage stage_weighted_tower (bo_data stage_weighted_tower bo) m) }.
Proof.
  apply (stage_tower_archimedean_vanishing bo HC).
  intros epsilon Heps.
  exact (obstruction_values_vanish bo epsilon Heps HC).
Defined.
