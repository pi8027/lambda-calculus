Require Import Coq.Arith.Compare_dec Omega ssreflect.

Inductive term : Set := var of nat | app of term & term | abs of term.

Fixpoint shift d c t : term :=
  match t with
    | var n => (if le_dec c n then var (n + d) else var n)%GEN_IF
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (S c) t1)
  end.

Fixpoint unshift d c t : term :=
  match t with
    | var n => (if le_dec c n then var (n - d) else var n)%GEN_IF
    | app t1 t2 => app (unshift d c t1) (unshift d c t2)
    | abs t1 => abs (unshift d (S c) t1)
  end.

Fixpoint substitution1 t1 n t2 : term :=
  match t2 with
    | var m => (if eq_nat_dec n m then t1 else var m)%GEN_IF
    | app t2l t2r => app (substitution1 t1 n t2l) (substitution1 t1 n t2r)
    | abs t2' => abs (substitution1 (shift 1 0 t1) (S n) t2')
  end.

Fixpoint substitution2 s t1 n t2 : term :=
  match t2 with
    | var m => (if eq_nat_dec n m then shift s 0 t1 else var m)%GEN_IF
    | app t2l t2r => app (substitution2 s t1 n t2l) (substitution2 s t1 n t2r)
    | abs t2' => abs (substitution2 (S s) t1 (S n) t2')
  end.

Fixpoint substitution3 s t1 n t2 : term :=
  match t2 with
    | var m =>
      match lt_eq_lt_dec n m with
        | inleft (left p) => var (pred m)
        | inleft (right p) => shift s 0 t1
        | inright p => var m
      end
    | app t2l t2r => app (substitution3 s t1 n t2l) (substitution3 s t1 n t2r)
    | abs t2' => abs (substitution3 (S s) t1 (S n) t2')
  end.

Lemma shift_add :
  forall d d' c c' t, c <= c' <= d + c ->
  shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
  move=> d d' c c' t; case; move: t c c'; elim.
  - move=> n c c' H H0; simpl.
    case le_dec => H1; simpl; case le_dec => H2; f_equal; omega.
  - move=> t1 H t2 H0 c c' H1 H2; simpl; f_equal; auto.
  - move=> t H c c' H0 H1; simpl; f_equal; apply H; omega.
Qed.

Lemma shiftzero_eq : forall n t, shift 0 n t = t.
Proof.
  move=> n t; move: t n; elim.
  - move=> m n; simpl.
    case le_dec => H; f_equal; omega.
  - by move=> t1 H t2 H0 n; simpl; f_equal.
  - move=> t H n; simpl; f_equal; apply H.
Qed.

Lemma unshift_shift_sub1 :
  forall d d' c c' t, c <= c' <= d + c -> d' <= d ->
  unshift d' c' (shift d c t) = shift (d - d') c t.
Proof.
  move=> d d' c c' t; case; move: t c c'; elim.
  - move=> n c c' H H0 H1; simpl.
    case le_dec=> H2; simpl; case le_dec=> H3; try omega; f_equal; omega.
  - move=> t1 H t2 H0 c c' H1 H2 H3; simpl.
    f_equal; auto.
  - move=> t H c c' H0 H1 H2; simpl.
    f_equal; apply H; omega.
Qed.

Lemma unshift_shift_eq :
  forall d c c' t, c <= c' <= d + c -> unshift d c' (shift d c t) = t.
Proof.
  move=> d c c' t H.
  rewrite unshift_shift_sub1; auto.
  replace (d - d) with 0 by omega.
  apply shiftzero_eq.
Qed.

Lemma substitution_eq_1_2 :
  forall s t1 n t2, substitution1 (shift s 0 t1) n t2 = substitution2 s t1 n t2.
Proof.
  move=> s t1 n t2; move: t2 s t1 n; elim.
  - move=> m s t1 n; simpl; by case eq_nat_dec=> H.
  - move=> t2l H t2r H0 s t1 n; simpl; f_equal; auto.
  - move=> t2' H s t1 n; simpl; f_equal; rewrite shift_add.
    by replace (1 + s) with (S s) by omega.
    omega.
Qed.

Lemma substitution_eq_2_3 :
  forall t1 n t2,
    unshift 1 n (substitution2 n (shift 1 0 t1) n t2) = substitution3 n t1 n t2.
Proof.
  move=> t1 n t2; move: t2 t1 n; elim.
  - move=> m t1 n; simpl; case eq_nat_dec, lt_eq_lt_dec; try omega.
    - case s=> H; try omega; clear.
      rewrite shift_add; last omega.
      replace (n + 1) with (S n) by omega.
      rewrite unshift_shift_sub1; first f_equal; omega.
    - case s=> H; try omega; simpl; case le_dec=> H0; f_equal; omega.
    - simpl; case le_dec=> H; f_equal; omega.
  - by move=> ? ? ? ? ? ?; simpl; f_equal.
  - by move=> ? ? ? ?; simpl; f_equal.
Qed.

Lemma substitution_eq_1_3 :
  forall t1 n t2,
    unshift 1 n (substitution1 (shift (S n) 0 t1) n t2) =
    substitution3 n t1 n t2.
Proof.
  move=> t1 n t2.
  replace (S n) with (n + 1) by omega.
  rewrite -(shift_add 1 n 0 0); last omega.
  rewrite substitution_eq_1_2.
  apply substitution_eq_2_3.
Qed.
