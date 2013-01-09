Require Import
  Coq.Arith.Arith Coq.Arith.Compare_dec
  Coq.Relations.Relations Coq.Relations.Relation_Operators Omega ssreflect.
Require Import Relations_ext.

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

Fixpoint substitution' n t1 t2 : term :=
  match t2 with
    | var m => (if eq_nat_dec n m then t1 else var m)%GEN_IF
    | app t2l t2r => app (substitution' n t1 t2l) (substitution' n t1 t2r)
    | abs t2' => abs (substitution' (S n) (shift 1 0 t1) t2')
  end.

Fixpoint substitution n t1 t2 : term :=
  match t2 with
    | var m =>
      match lt_eq_lt_dec n m with
        | inleft (left p) => var (pred m)
        | inleft (right p) => shift n 0 t1
        | inright p => var m
      end
    | app t2l t2r => app (substitution n t1 t2l) (substitution n t1 t2r)
    | abs t2' => abs (substitution (S n) t1 t2')
  end.

Lemma shift_add :
  forall d d' c c' t, c <= c' <= d + c ->
  shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
  move=> d d' c c' t; move: t c c'; elim.
  - simpl=> n c c' ?.
    case le_dec; simpl; case le_dec=> ? ?; f_equal; omega.
  - simpl=> t1 ? t2 ? c c' ?; f_equal; auto.
  - simpl=> t IH c c' ?; f_equal; apply IH; omega.
Qed.

Lemma shiftzero_eq : forall n t, shift 0 n t = t.
Proof.
  move=> n t; move: t n; elim.
  - simpl=> m n; case le_dec => H; f_equal; omega.
  - by simpl=> t1 ? t2 ? n; f_equal.
  - simpl=> t H n; f_equal; apply H.
Qed.

Lemma unshift_shift_sub :
  forall d d' c c' t, c <= c' <= d + c -> d' <= d ->
  unshift d' c' (shift d c t) = shift (d - d') c t.
Proof.
  move=> d d' c c' t; move: t c c'; elim.
  - simpl=> n c c' ? ?.
    case le_dec; simpl; case le_dec=> ? ?; try omega; f_equal; omega.
  - simpl=> t1 ? t2 ? c c' ? ?; f_equal; auto.
  - simpl=> t IH c c' ? ?; f_equal; apply IH; omega.
Qed.

Lemma unshift_shift_eq :
  forall d c c' t, c <= c' <= d + c -> unshift d c' (shift d c t) = t.
Proof.
  move=> d c c' t ?.
  rewrite -{2}(shiftzero_eq c t) unshift_shift_sub; auto.
  f_equal; omega.
Qed.

Lemma substitution_eq :
  forall n t1 t2,
  unshift 1 n (substitution' n (shift (S n) 0 t1) t2) = substitution n t1 t2.
Proof.
  move=> n t1 t2; move: t2 t1 n; elim.
  - simpl=> n t1 m.
    case lt_eq_lt_dec; first case; case eq_nat_dec=> ? ?; try omega.
    - simpl; case le_dec=> ?; f_equal; omega.
    - rewrite unshift_shift_sub; f_equal; omega.
    - simpl; case le_dec=> ?; f_equal; omega.
  - by simpl=> t2l ? t2r ? t1 n; f_equal.
  - simpl=> t2 IH t1 n; f_equal.
    rewrite shift_add.
    - apply (IH t1 (S n)).
    - omega.
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

Notation betared := (betared1 * ).
Infix "->1b" := betared1 (at level 70, no associativity).
Infix "->b"  := betared (at level 70, no associativity).
Infix "->bp" := parred (at level 70, no associativity).

Lemma betared1_eq : same_relation betared1' betared1.
Proof.
  split; elim; (try by constructor)=> ? ?.
  - rewrite substitution_eq; constructor.
  - rewrite -substitution_eq; constructor.
Qed.

Lemma parred_refl : reflexive _ parred.
Proof.
  elim; by constructor.
Qed.

Lemma betaredappl :
  forall t1 t1' t2, betared t1 t1' -> betared (app t1 t2) (app t1' t2).
Proof.
  move=> t1 t1' t2; elim.
  - constructor.
  - clear=> t1 t1' t1'' ? ? ?.
    by apply rt1n_trans with (app t1' t2); first constructor.
Qed.

Lemma betaredappr :
  forall t1 t2 t2', betared t2 t2' -> betared (app t1 t2) (app t1 t2').
Proof.
  move=> t1 t2 t2'; elim.
  - constructor.
  - clear=> t2 t2' t2'' ? ? ?.
    by apply rt1n_trans with (app t1 t2'); first constructor.
Qed.

Lemma betaredabs : forall t t', betared t t' -> betared (abs t) (abs t').
Proof.
  move=> t t'; elim.
  - constructor.
  - clear=> t t' t'' ? ? ?.
    by apply rt1n_trans with (abs t'); first constructor.
Qed.

Hint Resolve parred_refl betaredappl betaredappr betaredabs.

Lemma betared1_in_parred : inclusion betared1 parred.
Proof.
  move=> t t'; elim.
  - clear=> t1 t2; constructor; auto.
  - clear=> tl tl' tr ? ?; constructor; auto.
  - clear=> tl tr tr' ? ?; constructor; auto.
  - by clear=> t t' ? ?; constructor.
Qed.

Lemma parred_in_betared : inclusion parred betared.
Proof.
  move=> t t'; elim.
  - constructor.
  - clear=> t1 t1' t2 t2' ? ? ? ?; apply rt1n_trans' with (app t1' t2); auto.
  - clear=> t t' ? ?; auto.
  - clear=> t1 t1' t2 t2' ? ? ? ?.
    apply rt1n_trans' with (app (abs t1') t2); auto.
    apply rt1n_trans' with (app (abs t1') t2'); auto.
    apply rt1n_trans with (substitution 0 t2' t1'); constructor.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
  move=> d c d' c' t; move: t c c'; elim.
  - simpl=> n c c' ?; case le_dec, le_dec;
      simpl; case le_dec, le_dec; f_equal; omega.
  - simpl=> t1 ? t2 ? c c' ?; f_equal; auto.
  - simpl=> t' IH c c' ?; f_equal.
    replace (S (d' + c)) with (d' + S c) by omega.
    apply IH; omega.
Qed.

Lemma subst_shift_distr :
  forall n t1 t2 d c,
  shift d (n + c) (substitution n t1 t2) =
  substitution n (shift d c t1) (shift d (S (n + c)) t2).
Proof.
  move=> n t1 t2;move: t2 n; elim.
  - move=> m n d c.
    rewrite {3}/shift {1}/substitution.
    case le_dec, lt_eq_lt_dec; try omega.
    - case s=> ?; try omega; simpl.
      case le_dec, lt_eq_lt_dec; try omega; case s0=> ?; try omega.
      f_equal; omega.
    - case s=> ?; simpl; (case lt_eq_lt_dec; first case)=> ?; try omega.
      - case le_dec=> ?; f_equal; omega.
      - apply eq_sym, shift_shift_distr; omega.
      - (simpl; case lt_eq_lt_dec; first case)=> ?; try omega.
        case le_dec=> ?; f_equal; omega.
  - simpl=> t2l ? t2r ? n d c; f_equal; auto.
  - simpl=> t IH n d c; f_equal; apply (IH (S n)).
Qed.

Lemma shift_subst_distr :
  forall t1 t2 n d c, c <= n ->
  shift d c (substitution n t2 t1) = substitution (d + n) t2 (shift d c t1).
Proof.
  move=> t1 t2; elim t1.
  - move=> m n d c ?.
    simpl; case lt_eq_lt_dec; first case; case le_dec=> ? ?; try omega;
      simpl; (case lt_eq_lt_dec; first case)=> ?; try omega.
    - case le_dec=> ?; f_equal; omega.
    - apply shift_add; omega.
    - case le_dec=> ?; f_equal; omega.
    - case le_dec=> ?; f_equal; omega.
  - simpl=> t1l ? t1r ? n d c ?; f_equal; auto.
  - simpl=> t1' IH n d c ?; f_equal.
    replace (S (d + n)) with (d + S n) by omega; apply IH; omega.
Qed.

Lemma shift_const_subst :
  forall n t1 t2 d c, n < S d ->
  shift d c t1 = substitution (c + n) t2 (shift (S d) c t1).
Proof.
  move=> n; elim.
  - simpl=> m t2 d c ?; case le_dec=> ?;
     simpl; (case lt_eq_lt_dec; first case)=> ?; f_equal; omega.
  - simpl=> t1l ? t1r ? t2 d c ?; f_equal; auto.
  - by simpl=> t1 IH t2 d c ?; f_equal; apply IH.
Qed.

Lemma subst_subst_distr :
  forall n m t1 t2 t3,
  substitution (m + n) t3 (substitution m t2 t1) =
  substitution m (substitution n t3 t2)
    (substitution (S (m + n)) t3 t1).
Proof.
  move=> n m t1; move: t1 m; elim.
  - move=> v m t2 t3.
    do !(rewrite !/(substitution _ _ (var _));
      do !((case lt_eq_lt_dec; first case)=> ?); try omega); auto.
    - replace m with (0 + m) by omega.
      apply shift_const_subst; omega.
    - apply eq_sym, shift_subst_distr; omega.
  - by simpl=> t1l ? t1r ? m t2 t3; f_equal.
  - simpl=> t1 IH m t2 t3; f_equal.
    by replace (S (m + n)) with (S m + n) by omega.
Qed.

Lemma shift_lemma :
  forall t t' d c, parred t t' -> parred (shift d c t) (shift d c t').
Proof.
  move=> t t' d c H; move: H d c; elim; clear.
  - by simpl=> n d c.
  - by simpl=> t1 t1' t2 t2' ? ? ? ? d c; constructor.
  - by simpl=> t t' ? ? d c; constructor.
  - simpl=> t1 t1' t2 t2' ? ? ? ? d c.
    replace c with (0 + c) by omega.
    rewrite subst_shift_distr.
    by constructor.
Qed.

Lemma subst_lemma :
  forall n t1 t1' t2 t2', parred t1 t1' -> parred t2 t2' ->
  parred (substitution n t1 t2) (substitution n t1' t2').
Proof.
  move=> n t1 t1' t2 t2' ? H; move: H n; elim; clear t2 t2'.
  - simpl=> m n; case lt_eq_lt_dec; first case; move=> ?; auto.
    by apply shift_lemma.
  - by simpl=> t2l t2l' t2r t2r' ? ? ? ? n; constructor.
  - simpl=> t2 t2' ? IH n; constructor; apply IH.
  - move=> t2 t2' t3 t3' ? H _ H0 n.
    by rewrite (subst_subst_distr n 0) //=; constructor.
Qed.

Lemma parred_all_lemma :
  forall t t', parred t t' -> parred t' (reduce_all_redex t).
Proof.
  move=> t; elim/reduce_all_redex_ind: {t}_.
  - by move=> t n ? t' H; subst; inversion H.
  - move=> _ t1 t2 _ ? ? t' H; inversion H; subst.
    - inversion H2; subst; constructor; auto.
    - apply subst_lemma; auto.
  - move=> _ t1 t2 _ ? ? ? t' H; inversion H; subst.
    - constructor; auto.
    - done.
  - move=> _ t1 _ ? t2 H; inversion H; subst; constructor; auto.
Qed.

Lemma parred_confluent : confluent parred.
Proof.
  by move=> t1 t2 t3 ? ?;
    exists (reduce_all_redex t1); split; apply parred_all_lemma.
Qed.

Lemma betared_confluent : confluent betared.
Proof.
  apply (rt1n_confluent' _ _ _
    betared1_in_parred parred_in_betared parred_confluent).
Qed.
