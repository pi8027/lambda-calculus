From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From Coq Require Import Relations Relation_Operators.
Export Relations Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "[* R ]" :=
  (clos_refl_trans_1n _ R) (at level 5, no associativity) : type_scope.
Notation "[= R ]" := [* fun x y => R x y \/ R y x ]
  (at level 5, no associativity) : type_scope.

Notation inclusion R R' := (forall t1 t2, R t1 t2 -> R' t1 t2).
Notation same_relation R R' := (forall t1 t2, R t1 t2 <-> R' t1 t2).
Notation wconfluent R :=
  (forall t1 t2 t3, R t1 t2 -> R t1 t3 ->
                    exists2 t4, [*R%type] t2 t4 & [*R%type] t3 t4).
Notation confluent R :=
  (forall t1 t2 t3, R t1 t2 -> R t1 t3 ->
                    exists2 t4, R%type t2 t4 & R%type t3 t4).
Notation church_rosser R :=
  (forall t1 t2, [= R] t1 t2 ->
                 exists2 t3, [*R%type] t1 t3 & [*R%type] t2 t3).

Hint Resolve rt1n_refl.

Lemma rtc_trans A R : transitive A [*R].
Proof. by move => t1 t2 t3; rewrite -!clos_rt_rt1n_iff; apply rt_trans. Qed.

Lemma rtc_step A (R : relation A) : inclusion R [*R].
Proof. by move => x y H; apply rt1n_trans with y. Qed.

Lemma rtc_map A (R R' : relation A) : inclusion R R' -> inclusion [*R] [*R'].
Proof.
move => H t t'; elim/clos_refl_trans_1n_ind: t t' / => // t1 t2 T3 H0 H1 H2.
apply rt1n_trans with t2; auto.
Qed.

Lemma rtc_map' A B (R : relation A) (R' : relation B) (f : A -> B) :
  inclusion R (fun x y => R' (f x) (f y)) ->
  inclusion [*R] (fun x y => [*R'] (f x) (f y)).
Proof.
move => H t t'; elim/clos_refl_trans_1n_ind: t t' / => //= x y z H0 H1 H2.
apply rt1n_trans with (f y); auto.
Qed.

Lemma rtc_nest_elim A (R : relation A) : same_relation [*[*R]] [*R].
Proof.
move => t1 t2; split.
- by elim/clos_refl_trans_1n_ind: t1 t2 / => // t1 t2 t3 H _ H0;
     apply rtc_trans with t2.
- apply clos_rt1n_step.
Qed.

Lemma rtc_semi_confluent' A (R R' : relation A) :
  (forall t1 t2 t3, R t1 t2 -> R' t1 t3 -> exists2 t4, R' t2 t4 & [*R] t3 t4) ->
  (forall t1 t2 t3, [*R] t1 t2 -> R' t1 t3 ->
    exists2 t4, R' t2 t4 & [*R] t3 t4).
Proof.
move => H t1 t2 t3 H0; elim/clos_refl_trans_1n_ind: t1 t2 / H0 t3.
- by move => t1 t3 H0; exists t3.
- move => t1 t1' t2 H0 H1 IH t3 H2.
  case: (H t1 t1' t3 H0 H2) => {H H0 H2} t3' H H0.
  case: (IH t3' H) => {IH H} t4 H H2.
  by exists t4 => //; apply rtc_trans with t3'.
Qed.

Lemma rtc_semi_confluent A (R R' : relation A) :
  (forall t1 t2 t3, R t1 t2 -> R' t1 t3 -> exists2 t4, R' t2 t4 & R t3 t4) ->
  (forall t1 t2 t3, [*R] t1 t2 -> R' t1 t3 ->
    exists2 t4, R' t2 t4 & [*R] t3 t4).
Proof.
move => H; apply rtc_semi_confluent' => t1 t2 t3 H0 H1.
by case: (H _ _ _ H0 H1) => t4 H2 H3; exists t4 => //; apply rtc_step.
Qed.

Lemma rtc_confluent A (R : relation A) : confluent R -> confluent [*R].
Proof.
move => H; apply rtc_semi_confluent => t1 t2 t3 H0 H1.
by case: (rtc_semi_confluent H H1 H0) => t4 H2 H3; exists t4.
Qed.

Lemma rtc_confluent' A (R R' : relation A) :
  inclusion R R' -> inclusion R' [*R] -> confluent R' -> confluent [*R].
Proof.
move => H H0 H1 t1 t2 t3 H2 H3.
case: (rtc_confluent H1 (rtc_map H H2) (rtc_map H H3)) => t4 H4 H5.
by exists t4; apply rtc_nest_elim; apply (rtc_map H0).
Qed.

Lemma equiv_refl A (R : relation A) : reflexive A [= R].
Proof. by []. Qed.

Lemma equiv_trans A (R : relation A) : transitive A [= R].
Proof. apply rtc_trans. Qed.

Lemma equiv_sym A (R : relation A) : symmetric A [= R].
Proof.
move => x y; elim/clos_refl_trans_1n_ind: x y / => //= x y z H _ H0.
by apply equiv_trans with y => //; apply rtc_step; case: H; auto.
Qed.

Lemma equiv_includes_rtc A (R : relation A) : inclusion [* R] [= R].
Proof.
move => x y; elim/clos_refl_trans_1n_ind: x y / => //= x y z H _ H0.
by apply rt1n_trans with y => //; left.
Qed.

Lemma confluent_CR A (R : relation A) : confluent [* R] <-> church_rosser R.
Proof.
split; last by move => H x y z Hy Hz; apply H, equiv_trans with x;
               [apply equiv_sym, equiv_includes_rtc | apply equiv_includes_rtc].
move => H x y; elim/clos_refl_trans_1n_ind: x y /; first by move => x; exists x.
move => x y z [] H0 H1 [c H2 H3].
- by exists c => //; apply rt1n_trans with y.
- by case: (H _ _ _ (rtc_step H0) H2) => c' H4 H5;
    exists c' => //; apply rtc_trans with c.
Qed.

Section Z.

Variable (A : Type) (R : relation A) (comp : A -> A).
Variable (Z : forall x y, R x y -> [*R] y (comp x) /\ [*R] (comp x) (comp y)).

Lemma Z_confluent : confluent [*R].
Proof.
have Z1 x y : R x y -> [*R] y (comp x) by firstorder.
have Z2 x y : R x y -> [*R] (comp x) (comp y) by firstorder.
apply rtc_semi_confluent' => t1 t2 t3 H H0; exists (comp t3).
- apply rtc_trans with (comp t1); first apply Z1 => //.
  apply rtc_nest_elim; move: t1 t3 H0 {H}; apply rtc_map', Z2.
- case: H0.
  + by apply rt1n_trans with t2 => //; apply Z1.
  + move => {t3} t1' t3 H0 H1;
      elim/clos_refl_trans_1n_ind: t1' t3 / H1 t1 H0 {H}; eauto => t1' t1 H.
    by apply rtc_trans with (comp t1); [apply Z1 | apply Z2].
Qed.

End Z.

Lemma rtc_preservation A (P : A -> Prop) (R : relation A) :
  (forall x y, R x y -> P x -> P y) -> forall x y, [*R] x y -> P x -> P y.
Proof.
move => H x y; elim/clos_refl_trans_1n_ind: x y / => //= x y z H0 _ H1 H2.
exact (H1 (H x y H0 H2)).
Qed.

Lemma Acc_ind' (A : Type) (R : relation A) (P : A -> Prop) :
  (forall x, (forall y, R y x -> P y) -> P x) -> forall x, Acc R x -> P x.
Proof. move => H x H0; elim/Acc_ind: x / H0 H => x _ IH H; apply H; auto. Qed.

Lemma acc_preservation A B (RA : relation A) (RB : relation B) (f : A -> B) a :
  (forall x y, RA x y -> RB (f x) (f y)) -> Acc RB (f a) -> Acc RA a.
Proof.
move => H H0; move: {1 2}(f a) H0 (erefl (f a)) => b H0.
elim/Acc_ind': b / H0 a => b H0 a H1; subst b.
by constructor => a' H1; apply (fun x => H0 _ x _ erefl), H.
Qed.

Lemma Acc_ind2
  (A B : Type) (RA : relation A) (RB : relation B) (P : A -> B -> Prop) :
  (forall x y, (forall x', RA x' x -> P x' y) ->
               (forall y', RB y' y -> P x y') -> P x y) ->
  forall x y, Acc RA x -> Acc RB y -> P x y.
Proof.
move => H x y Hx Hy;
  elim/Acc_ind: x / Hx y Hy => x Hx IHx y Hy; elim/Acc_ind: y / Hy => y Hy IHy.
by apply H => [x' | y'] H2; [apply IHx | apply IHy].
Qed.

Lemma Acc_wconfluent A (R : relation A) :
  (forall x, Acc (fun a => R^~ a) x) -> wconfluent R -> confluent [*R].
Proof.
move => Hacc Hwconfluent x; elim/Acc_ind': x / (Hacc x) => x IH y z Hy Hz.
inversion Hy; subst; first by exists z.
inversion Hz; subst; first by exists y.
move: {Hy Hz} y0 y1 H H0 H1 H2 => y' z' Hy Hy0 Hz Hz0.
case: (Hwconfluent _ _ _ Hy Hz) => x' Hy1 Hz1.
case: (IH _ Hy _ _ Hy0 Hy1) => y'' Hy2 Hy3.
case: (IH _ Hz _ _ Hz0 Hz1) => z'' Hz2 Hz3.
case: (IH _ Hy _ _ (rtc_trans Hy0 Hy2) (rtc_trans Hy1 Hz3)) => x'' Hy4 Hz4.
by exists x''; [apply (rtc_trans Hy2 Hy4) | apply (rtc_trans Hz2 Hz4)].
Qed.
