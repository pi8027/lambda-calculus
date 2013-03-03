Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Omega
  Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat LCAC.Relations_ext LCAC.ssrnat_ext.

Set Implicit Arguments.

Inductive term : Set := var of nat | app of term & term | abs of term.

Fixpoint shift d c t : term :=
  match t with
    | var n => (if leq c n then var (n + d) else var n)%GEN_IF
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (S c) t1)
  end.

Fixpoint unshift d c t : term :=
  match t with
    | var n => (if leq c n then var (n - d) else var n)%GEN_IF
    | app t1 t2 => app (unshift d c t1) (unshift d c t2)
    | abs t1 => abs (unshift d (S c) t1)
  end.

Fixpoint substitution' n t1 t2 : term :=
  match t2 with
    | var m => (if eqn n m then t1 else var m)
    | app t2l t2r => app (substitution' n t1 t2l) (substitution' n t1 t2r)
    | abs t2' => abs (substitution' (S n) (shift 1 0 t1) t2')
  end.

Fixpoint substitution n t1 t2 : term :=
  match t2 with
    | var m =>
      if leq n m
        then (if eqn n m then shift n 0 t1 else var m.-1)
        else var m
    | app t2l t2r => app (substitution n t1 t2l) (substitution n t1 t2r)
    | abs t2' => abs (substitution (S n) t1 t2')
  end.

Lemma shift_add :
  forall d d' c c' t, c <= c' <= d + c ->
  shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
  move => d d' c c' t; move: t c c'; elim => /=.
  - move => n c c' ?; do !case: ifP => /= ?; f_equal; ssromega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - move => t IH c c' ?; f_equal; apply IH; ssromega.
Qed.

Lemma shiftzero_eq : forall n t, shift 0 n t = t.
Proof.
  move => n t; move: t n; elim => /=.
  - move => m n; case: ifP => ?; f_equal; ssromega.
  - by move => t1 ? t2 ? n; f_equal.
  - by move => t H n; f_equal.
Qed.

Lemma unshift_shift_sub :
  forall d d' c c' t, c <= c' <= d + c -> d' <= d ->
  unshift d' c' (shift d c t) = shift (d - d') c t.
Proof.
  move => d d' c c' t; move: t c c'; elim => /=.
  - move => n c c' ? ?; do 2 case: ifP => /= ?; f_equal; ssromega.
  - move => t1 ? t2 ? c c' ? ?; f_equal; auto.
  - move => t IH c c' ? ?; f_equal; apply IH; ssromega.
Qed.

Lemma unshift_shift_eq :
  forall d c c' t, c <= c' <= d + c -> unshift d c' (shift d c t) = t.
Proof.
  move => d c c' t H.
  rewrite -{2}(shiftzero_eq c t) unshift_shift_sub // -{1}(addn0 d) addKn //.
Qed.

Lemma substitution_eq :
  forall n t1 t2,
  unshift 1 n (substitution' n (shift (S n) 0 t1) t2) = substitution n t1 t2.
Proof.
  move => n t1 t2; move: t2 t1 n; elim.
  - simpl => n t1 m.
    do !case: ifP => ? //=; try by f_equal; ssromega.
    rewrite unshift_shift_sub; f_equal; ssromega.
  - by simpl => t2l ? t2r ? t1 n; f_equal.
  - by simpl => t2 IH t1 n; f_equal; rewrite shift_add.
Qed.

Inductive betared1' : relation term :=
  | betared1beta' : forall t1 t2,
                    betared1' (app (abs t1) t2)
                              (unshift 1 0 (substitution' 0 (shift 1 0 t2) t1))
  | betared1appl' : forall t1 t1' t2,
                    betared1' t1 t1' -> betared1' (app t1 t2) (app t1' t2)
  | betared1appr' : forall t1 t2 t2',
                    betared1' t2 t2' -> betared1' (app t1 t2) (app t1 t2')
  | betared1abs'  : forall t t', betared1' t t' -> betared1' (abs t) (abs t').

Inductive betared1 : relation term :=
  | betared1beta : forall t1 t2,
                   betared1 (app (abs t1) t2) (substitution 0 t2 t1)
  | betared1appl : forall t1 t1' t2,
                   betared1 t1 t1' -> betared1 (app t1 t2) (app t1' t2)
  | betared1appr : forall t1 t2 t2',
                   betared1 t2 t2' -> betared1 (app t1 t2) (app t1 t2')
  | betared1abs  : forall t t', betared1 t t' -> betared1 (abs t) (abs t').

Inductive parred : relation term :=
  | parredvar  : forall n, parred (var n) (var n)
  | parredapp  : forall t1 t1' t2 t2',
                 parred t1 t1' -> parred t2 t2' ->
                 parred (app t1 t2) (app t1' t2')
  | parredabs  : forall t t', parred t t' -> parred (abs t) (abs t')
  | parredbeta : forall t1 t1' t2 t2',
                 parred t1 t1' -> parred t2 t2' ->
                 parred (app (abs t1) t2) (substitution 0 t2' t1').

Function reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs t1) t2 =>
      substitution 0 (reduce_all_redex t2) (reduce_all_redex t1)
    | app t1 t2 => app (reduce_all_redex t1) (reduce_all_redex t2)
    | abs t' => abs (reduce_all_redex t')
  end.

Notation betared := [* betared1].
Infix "->1b" := betared1 (at level 70, no associativity).
Infix "->b"  := betared (at level 70, no associativity).
Infix "->bp" := parred (at level 70, no associativity).

Lemma betared1_eq : same_relation betared1' betared1.
Proof.
  split; elim; (try by constructor) => ? ?.
  - rewrite substitution_eq; constructor.
  - rewrite -substitution_eq; constructor.
Qed.

Lemma parred_refl : forall t, parred t t.
Proof.
  by elim; constructor.
Qed.

Lemma betaredappl :
  forall t1 t1' t2, betared t1 t1' -> betared (app t1 t2) (app t1' t2).
Proof.
  move => t1 t1' t2; elim => //.
  clear => t1 t1' t1'' ? ? ?.
  by apply rt1n_trans with (app t1' t2); first constructor.
Qed.

Lemma betaredappr :
  forall t1 t2 t2', betared t2 t2' -> betared (app t1 t2) (app t1 t2').
Proof.
  move => t1 t2 t2'; elim => //.
  clear => t2 t2' t2'' ? ? ?.
  by apply rt1n_trans with (app t1 t2'); first constructor.
Qed.

Lemma betaredabs : forall t t', betared t t' -> betared (abs t) (abs t').
Proof.
  move => t t'; elim => //.
  clear => t t' t'' ? ? ?.
  by apply rt1n_trans with (abs t'); first constructor.
Qed.

Hint Resolve parred_refl betaredappl betaredappr betaredabs.

Lemma betared1_in_parred : inclusion betared1 parred.
Proof.
  move => t t'; elim.
  - clear => t1 t2; constructor; auto.
  - clear => tl tl' tr ? ?; constructor; auto.
  - clear => tl tr tr' ? ?; constructor; auto.
  - by clear => t t' ? ?; constructor.
Qed.

Lemma parred_in_betared : inclusion parred betared.
Proof.
  move => t t'; elim => //.
  - clear => t1 t1' t2 t2' ? ? ? ?; apply rt1n_trans' with (app t1' t2); auto.
  - clear => t t' ? ?; auto.
  - clear => t1 t1' t2 t2' ? ? ? ?.
    apply rt1n_trans' with (app (abs t1') t2); auto.
    apply rt1n_trans' with (app (abs t1') t2'); auto.
    apply rt1n_trans with (substitution 0 t2' t1'); constructor.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
  move => d c d' c' t; move: t c c'; elim => /=.
  - move => n c c' ?; do ! case: ifP => ? /=; f_equal; ssromega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => t' IH c c' ?; f_equal; rewrite -addnS; apply IH; rewrite ltnS.
Qed.

Lemma subst_shift_distr :
  forall n t1 t2 d c,
  shift d (n + c) (substitution n t1 t2) =
  substitution n (shift d c t1) (shift d (S (n + c)) t2).
Proof.
  move => n t1 t2;move: t2 n; elim => //=.
  - move => m n d c.
    do !case: ifP => ? /=; try (f_equal; ssromega).
    apply Logic.eq_sym, shift_shift_distr; ssromega.
  - by simpl => t2l ? t2r ? n d c; f_equal.
  - simpl => t IH n d c; f_equal; apply (IH (S n)).
Qed.

Lemma shift_subst_distr :
  forall t1 t2 n d c, c <= n ->
  shift d c (substitution n t2 t1) = substitution (d + n) t2 (shift d c t1).
Proof.
  move => t1 t2; elim t1 => /=.
  - move => m n d c ?.
    do !case: ifP => ? /=; try (f_equal; ssromega).
    apply shift_add; ssromega.
  - simpl => t1l ? t1r ? n d c ?; f_equal; auto.
  - simpl => t1' IH n d c ?; f_equal.
    by rewrite -addnS; apply IH; rewrite ltnS.
Qed.

Lemma shift_const_subst :
  forall n t1 t2 d c, n < S d ->
  shift d c t1 = substitution (c + n) t2 (shift (S d) c t1).
Proof.
  move => n; elim => /=.
  - move => m t2 d c ?; do !case: ifP => ? /=; f_equal; ssromega.
  - simpl => t1l ? t1r ? t2 d c ?; f_equal; auto.
  - by simpl => t1 IH t2 d c ?; f_equal; apply IH.
Qed.

Lemma subst_subst_distr :
  forall n m t1 t2 t3,
  substitution (m + n) t3 (substitution m t2 t1) =
  substitution m (substitution n t3 t2)
    (substitution (S (m + n)) t3 t1).
Proof.
  move => n m t1; move: t1 m; elim => /=.
  - case => [ | v] m t2 t3;
      do! case: ifP => ? /=; try (f_equal; ssromega).
    - by symmetry; apply shift_subst_distr.
    - by symmetry; apply shift_subst_distr.
    - rewrite -(add0n m); apply shift_const_subst; ssromega.
  - by move => t1l ? t1r ? m t2 t3; f_equal.
  - by simpl => t1 IH m t2 t3; f_equal; rewrite -addSn.
Qed.

Lemma shift_lemma :
  forall t t' d c, parred t t' -> parred (shift d c t) (shift d c t').
Proof.
  move => t t' d c H; move: H d c; elim; clear.
  - by simpl => n d c.
  - by simpl => t1 t1' t2 t2' ? ? ? ? d c; constructor.
  - by simpl => t t' ? ? d c; constructor.
  - simpl => t1 t1' t2 t2' ? ? ? ? d c.
    rewrite -(add0n c) subst_shift_distr.
    by constructor.
Qed.

Lemma subst_lemma :
  forall n t1 t1' t2 t2', parred t1 t1' -> parred t2 t2' ->
  parred (substitution n t1 t2) (substitution n t1' t2').
Proof.
  move => n t1 t1' t2 t2' H H0; move: t2 t2' H0 n t1 t1' H.
  refine (parred_ind _ _ _ _ _) => /=; try constructor; auto.
  - by move => m n t1 t1' H; do !case: ifP => ? //=; apply shift_lemma.
  - move => t2l t2l' ? ? t2r t2r' ? ? n t1 t1' ?.
    rewrite (subst_subst_distr n 0); constructor; auto.
Qed.

Lemma parred_all_lemma :
  forall t t', parred t t' -> parred t' (reduce_all_redex t).
Proof.
  move => t; elim/reduce_all_redex_ind: {t}_.
  - by move => t n ? t' H; subst; inversion H.
  - move => _ t1 t2 _ ? ? t' H; inversion H; subst.
    - inversion H2; subst; constructor; auto.
    - apply subst_lemma; auto.
  - move => _ t1 t2 _ ? ? ? t' H; inversion H; subst => //.
    constructor; auto.
  - move => _ t1 _ ? t2 H; inversion H; subst; constructor; auto.
Qed.

Lemma parred_confluent : confluent parred.
Proof.
  by move => t1 t2 t3 ? ?;
    exists (reduce_all_redex t1); split; apply parred_all_lemma.
Qed.

Lemma betared_confluent : confluent betared.
Proof.
  apply (rt1n_confluent' _
    betared1_in_parred parred_in_betared parred_confluent).
Qed.
