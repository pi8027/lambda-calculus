Require Import ssreflect List Relations Relation_Operators.

Notation "[]" := nil : list_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Definition confluent (A : Set) (R : relation A) : Prop :=
  forall (t1 t2 t3 : A), R t1 t2 -> R t1 t3 ->
  exists t4 : A, R t2 t4 /\ R t3 t4.

Lemma rt1n_trans' : forall (A : Set) (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  move=> A R x y z ; elim => [ | x0 y0 z0 H H0 H1 H2].
  auto.
  eapply rt1n_trans ; eauto.
Qed.

Lemma rt1n_step : forall (A : Set) (R : relation A) (x y : A),
  R x y -> clos_refl_trans_1n A R x y.
Proof.
  do! econstructor ; eauto.
Qed.

Lemma rt1n_concat : forall (A : Set) (R : relation A) (x y : A),
  clos_refl_trans_1n A (clos_refl_trans_1n A R) x y ->
  clos_refl_trans_1n A R x y.
Proof.
  move=> A R x y ; elim => [ | x0 y0 z H H0 H1].
  constructor.
  eapply rt1n_trans' ; eauto.
Qed.

Lemma rt1n_map : forall (A : Set) (R R' : relation A),
  (forall (x y : A), R x y -> R' x y) ->
  forall (x y : A), clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R' x y.
Proof.
  move=> A R R' H x y ; elim.
  constructor.
  econstructor ; eauto.
Qed.

Lemma rt1n_confluent : forall (A : Set) (R : relation A),
  confluent A R -> confluent A (clos_refl_trans_1n A R).
Proof.
  move=> A R H t1 t2 t3 H0 ; move: t3.
  elim: H0 => [t4 t3 H0 | x y z H0 H1 IH t3 H2].
  by exists t3 ; do !constructor.
  have: (forall t1 t2 t3, R t1 t2 -> clos_refl_trans_1n A R t1 t3 ->
    exists t4 : A, clos_refl_trans_1n A R t2 t4 /\
                   clos_refl_trans_1n A R t3 t4).
    move: H ; clear ; move=> H t1 t2 t3 H0 H1 ;
      move: H1 t2 H0 ; elim => [x t2 | x y z H0 H1 IH t2 H2].
    by exists t2 ; do !econstructor.
    elim (H x y t2 H0 H2) => [x0 [H3 H4]].
    elim (IH x0 H3) => [x1 [? ?]].
    exists x1 ; split ; first econstructor ; eauto.
  move=> semi_confluent.
  elim (semi_confluent x y t3 H0 H2) => [t4 [H3 H4]].
  elim (IH t4 H3) => [t5 [H5 H6]].
  by exists t5 ; split ; last eapply rt1n_trans' ; eauto.
Qed.
