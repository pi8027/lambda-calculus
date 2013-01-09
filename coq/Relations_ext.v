Require Import
  Coq.Arith.Arith Coq.Relations.Relations Coq.Relations.Relation_Operators
  ssreflect.

Notation inclusion R R' := (forall t1 t2, R t1 t2 -> R' t1 t2).
Notation same_relation R R' := (forall t1 t2, R t1 t2 <-> R' t1 t2).
Notation confluent R :=
  (forall t1 t2 t3, R t1 t2 -> R t1 t3 -> exists t4, R t2 t4 /\ R t3 t4).

Notation "[ * R ]" :=
  (clos_refl_trans_1n _ R) (at level 5, no associativity) : type_scope.

Lemma rt1n_trans' : forall A R, transitive A [* R].
Proof.
  move=> A R t1 t2 t3.
  rewrite -!clos_rt_rt1n_iff.
  apply rt_trans.
Qed.

Lemma rt1n_step : forall (A : Set) (R : relation A) (x y : A),
  R x y -> clos_refl_trans_1n A R x y.
Proof.
  do! econstructor ; eauto.
Qed.

Lemma clos_rt_map :
  forall A (R R' : relation A), inclusion R R' -> inclusion [* R] [* R'].
Proof.
  move=> A R R' H t1 t2; elim.
  constructor.
  econstructor; eauto.
Qed.

Lemma rt1n_nest_elim : forall A (R : relation A), same_relation [* [* R]] [* R].
Proof.
  move=> A R t1 t2; split.
  - elim => [t3 | t3 t4 t5 H H0 H1].
    constructor.
    by apply rt1n_trans' with t4.
  - apply clos_rt1n_step.
Qed.

Lemma rt1n_confluent :
  forall A (R : relation A), confluent R -> confluent [* R].
Proof.
  move=> A R H.
  have: (forall t1 t2 t3,
    R t1 t2 -> [* R] t1 t3 -> exists t4: A, [* R] t2 t4 /\ [* R] t3 t4).
    move=> t1 t2 t3 H0 H1; move: H1 t2 H0 ;
      elim => [t4 t2 H0 | t4 t5 t6 H0 H1 IH t2 H2].
    - by exists t2 ; do !constructor ; apply clos_rt1n_step.
    - elim (H t4 t5 t2 H0 H2) => [t7 [H3 H4]].
      elim (IH t7 H3) => [t8 [? ?]].
      by exists t8 ; split ; first apply rt1n_trans with t7.
  clear H => H t1 t2 t3 H0 ; move: H0 t3 ;
    elim => [t4 t3 H1 | t4 t5 t6 H0 H1 IH t3 H2].
  - by exists t3 ; do !constructor.
  - elim (H t4 t5 t3 H0 H2) => [t7 [H3 H4]].
    elim (IH t7 H3) => [t8 [H5 H6]].
    by exists t8; split; last apply rt1n_trans' with t7.
Qed.

Lemma rt1n_confluent' : forall A (R R' : relation A),
  inclusion R R' -> inclusion R' [* R] -> confluent R' -> confluent [* R].
Proof.
  move=> A R R' H H0 H1 t1 t2 t3 H2 H3.
  elim (rt1n_confluent _ _ H1 _ _ _
    (clos_rt_map _ _ _ H _ _ H2) (clos_rt_map _ _ _ H _ _ H3)) => t4 [? ?].
  by exists t4 ; split ; rewrite -rt1n_nest_elim ; apply (clos_rt_map _ R').
Qed.
