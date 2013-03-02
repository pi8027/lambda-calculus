Require Import
  Coq.Arith.Arith Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect.

Set Implicit Arguments.

Notation inclusion R R' := (forall t1 t2, R t1 t2 -> R' t1 t2).
Notation same_relation R R' := (forall t1 t2, R t1 t2 <-> R' t1 t2).
Notation confluent R :=
  (forall t1 t2 t3, R t1 t2 -> R t1 t3 -> exists t4, R t2 t4 /\ R t3 t4).

Notation "[ * R ]" :=
  (clos_refl_trans_1n _ R) (at level 5, no associativity) : type_scope.

Hint Resolve rt1n_refl.

Lemma rt1n_trans' : forall A R, transitive A [* R].
Proof.
  move => A R t1 t2 t3.
  rewrite -!clos_rt_rt1n_iff.
  apply rt_trans.
Qed.

Lemma rt1n_step : forall (A : Set) (R : relation A), inclusion R [* R].
Proof.
  do! econstructor; eauto.
Qed.

Lemma clos_rt_map :
  forall A (R R' : relation A), inclusion R R' -> inclusion [* R] [* R'].
Proof.
  move => A R R' H.
  refine (clos_refl_trans_1n_ind A R _ _ _); auto => t1 t2 t3 ? ? ?.
  apply rt1n_trans with t2; auto.
Qed.

Lemma rt1n_nest_elim : forall A (R : relation A), same_relation [* [* R]] [* R].
Proof.
  move => A R t1 t2; split.
  - move: t1 t2; refine (clos_refl_trans_1n_ind A _ _ _ _).
    constructor.
    by move => t1 t2 t3 H _ H0; apply rt1n_trans' with t2.
  - apply clos_rt1n_step.
Qed.

Lemma rt1n_semi_confluent :
  forall A (R S : relation A),
  (forall t1 t2 t3, R t1 t2 -> S t1 t3 -> exists t4, S t2 t4 /\ R t3 t4) ->
  (forall t1 t2 t3, [* R] t1 t2 -> S t1 t3 ->
    exists t4, S t2 t4 /\ [* R] t3 t4).
Proof.
  move => A R S H t1 t2 t3 H0; move: t1 t2 H0 t3.
  refine (clos_refl_trans_1n_ind A R _ _ _).
  - move => t1 t3 H0; exists t3; auto.
  - move => t1 t1' t2 H0 H1 IH t3 H2.
    case: (H t1 t1' t3 H0 H2) => t3'; case => {H H0 H2} H H0.
    case: (IH t3' H) => {IH H} t4; case => H H2; exists t4; split => //.
    by apply rt1n_trans with t3'.
Qed.

Lemma rt1n_confluent :
  forall A (R : relation A), confluent R -> confluent [* R].
Proof.
  move => A R H.
  apply rt1n_semi_confluent.
  move: (rt1n_semi_confluent R H) => {H} H t1 t2 t3 H0 H1.
  case: (H t1 t3 t2 H1 H0) => t4; case => H2 H3; exists t4; auto.
Qed.

Lemma rt1n_confluent' : forall A (R R' : relation A),
  inclusion R R' -> inclusion R' [* R] -> confluent R' -> confluent [* R].
Proof.
  move => A R R' H H0 H1 t1 t2 t3 H2 H3.
  case (rt1n_confluent H1 (clos_rt_map _ H H2) (clos_rt_map _ H H3))
    => t4 [? ?].
  by exists t4; split; rewrite -rt1n_nest_elim; apply (clos_rt_map _ H0).
Qed.
