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

Fixpoint substitution1 n t1 t2 : term :=
  match t2 with
    | var m => (if eq_nat_dec n m then t1 else var m)%GEN_IF
    | app t2l t2r => app (substitution1 n t1 t2l) (substitution1 n t1 t2r)
    | abs t2' => abs (substitution1 (S n) (shift 1 0 t1) t2')
  end.

Fixpoint substitution2 n t1 t2 : term :=
  match t2 with
    | var m => (if eq_nat_dec n m then shift n 0 t1 else var m)%GEN_IF
    | app t2l t2r => app (substitution2 n t1 t2l) (substitution2 n t1 t2r)
    | abs t2' => abs (substitution2 (S n) t1 t2')
  end.

Fixpoint substitution3 n t1 t2 : term :=
  match t2 with
    | var m =>
      match lt_eq_lt_dec n m with
        | inleft (left p) => var (pred m)
        | inleft (right p) => shift n 0 t1
        | inright p => var m
      end
    | app t2l t2r => app (substitution3 n t1 t2l) (substitution3 n t1 t2r)
    | abs t2' => abs (substitution3 (S n) t1 t2')
  end.

Lemma shift_add :
  forall d d' c c' t, c <= c' <= d + c ->
  shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
  move=> d d' c c' t; move: t c c'; elim.
  - move=> n c c' ?; simpl.
    case le_dec; simpl; case le_dec=> ? ?; f_equal; omega.
  - move=> t1 ? t2 ? c c' ?; simpl; f_equal; auto.
  - move=> t IH c c' ?; simpl; f_equal; apply IH; omega.
Qed.

Lemma shiftzero_eq : forall n t, shift 0 n t = t.
Proof.
  move=> n t; move: t n; elim.
  - move=> m n; simpl.
    case le_dec => H; f_equal; omega.
  - by move=> t1 ? t2 ? n; simpl; f_equal.
  - move=> t H n; simpl; f_equal; apply H.
Qed.

Lemma unshift_shift_sub :
  forall d d' c c' t, c <= c' <= d + c -> d' <= d ->
  unshift d' c' (shift d c t) = shift (d - d') c t.
Proof.
  move=> d d' c c' t; move: t c c'; elim.
  - move=> n c c' ? ?; simpl.
    case le_dec; simpl; case le_dec=> ? ?; try omega; f_equal; omega.
  - move=> t1 ? t2 ? c c' ? ?; simpl; f_equal; auto.
  - move=> t IH c c' ? ?; simpl; f_equal; apply IH; omega.
Qed.

Lemma unshift_shift_eq :
  forall d c c' t, c <= c' <= d + c -> unshift d c' (shift d c t) = t.
Proof.
  move=> d c c' t ?.
  rewrite -{2}(shiftzero_eq c t) unshift_shift_sub; auto.
  f_equal; omega.
Qed.

Lemma substitution_eq_1_2 :
  forall t1 n t2, substitution1 n (shift n 0 t1) t2 = substitution2 n t1 t2.
Proof.
  move=> t1 n t2; move: t2 t1 n; elim.
  - move=> m t1 n; simpl; by case eq_nat_dec=> H.
  - move=> t2l ? t2r ? t1 n; simpl; f_equal; auto.
  - move=> t2' ? t1 n; simpl; f_equal; rewrite shift_add; last omega.
    by replace (1 + n) with (S n) by omega.
Qed.

Lemma substitution_eq_2_3 :
  forall t1 n t2,
  unshift 1 n (substitution2 n (shift 1 0 t1) t2) = substitution3 n t1 t2.
Proof.
  move=> t1 n t2; move: t2 t1 n; elim.
  - move=> m t1 n; simpl; case eq_nat_dec, lt_eq_lt_dec; try omega.
    - case s=> ?; try omega; clear.
      rewrite shift_add; last omega.
      replace (n + 1) with (S n) by omega.
      rewrite unshift_shift_sub; first f_equal; omega.
    - case s=> ?; try omega; simpl; case le_dec=> ?; f_equal; omega.
    - simpl; case le_dec=> ?; f_equal; omega.
  - by move=> t2l ? t2r ? t1 n; simpl; f_equal.
  - by move=> t2' ? t1 n; simpl; f_equal.
Qed.

Lemma substitution_eq_1_3 :
  forall t1 n t2,
  unshift 1 n (substitution1 n (shift (S n) 0 t1) t2) = substitution3 n t1 t2.
Proof.
  move=> t1 n t2.
  replace (S n) with (n + 1) by omega.
  rewrite -(shift_add 1 n 0 0); last omega.
  rewrite substitution_eq_1_2.
  apply substitution_eq_2_3.
Qed.

Inductive betared1' : relation term :=
  | betared1beta' : forall t1 t2,
                    betared1' (app (abs t1) t2)
                              (unshift 1 0 (substitution1 0 (shift 1 0 t2) t1))
  | betared1appl' : forall t1 t1' t2,
                    betared1' t1 t1' -> betared1' (app t1 t2) (app t1' t2)
  | betared1appr' : forall t1 t2 t2',
                    betared1' t2 t2' -> betared1' (app t1 t2) (app t1 t2')
  | betared1abs'  : forall t t', betared1' t t' -> betared1' (abs t) (abs t').

Inductive betared1 : relation term :=
  | betared1beta : forall t1 t2,
                   betared1 (app (abs t1) t2) (substitution3 0 t2 t1)
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
                 parred (app (abs t1) t2) (substitution3 0 t2' t1').

Function reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs t1) t2 =>
      substitution3 0 (reduce_all_redex t2) (reduce_all_redex t1)
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
  - rewrite substitution_eq_1_3; constructor.
  - rewrite -substitution_eq_1_3; constructor.
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
    apply rt1n_trans with (substitution3 0 t2' t1'); constructor.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
  move=> d c d' c' t; move: t c c'; elim.
  - move=> n c c' ?; simpl; case le_dec, le_dec;
      simpl; case le_dec, le_dec; f_equal; omega.
  - move=> t1 ? t2 ? c c' ?; simpl; f_equal; auto.
  - move=> t' IH c c' ?; simpl; f_equal.
    replace (S (d' + c)) with (d' + S c) by omega.
    apply IH; omega.
Qed.

Lemma subst_shift_distr :
  forall n t1 t2 d c,
  shift d (n + c) (substitution3 n t1 t2) =
  substitution3 n (shift d c t1) (shift d (S (n + c)) t2).
Proof.
  move=> n t1 t2;move: t2 n; elim.
  - move=> m n d c.
    rewrite {3}/shift {1}/substitution3.
    case le_dec, lt_eq_lt_dec; try omega.
    - case s=> ?; try omega; simpl.
      case le_dec, lt_eq_lt_dec; try omega; case s0=> ?; try omega.
      f_equal; omega.
    - case s=> ?; simpl; (case lt_eq_lt_dec; first case)=> ?; try omega.
      - case le_dec=> ?; f_equal; omega.
      - apply eq_sym, shift_shift_distr; omega.
      - (simpl; case lt_eq_lt_dec; first case)=> ?; try omega.
        case le_dec=> ?; f_equal; omega.
  - move=> t2l ? t2r ? n d c; simpl; f_equal; auto.
  - move=> t IH n d c; simpl; f_equal; apply (IH (S n)).
Qed.

Lemma shift_subst_distr :
  forall t1 t2 n d c, c <= n ->
  shift d c (substitution3 n t2 t1) = substitution3 (d + n) t2 (shift d c t1).
Proof.
  move=> t1 t2; elim t1.
  - move=> m n d c ?.
    simpl; case lt_eq_lt_dec; first case; case le_dec=> ? ?; try omega;
      simpl; (case lt_eq_lt_dec; first case)=> ?; try omega.
    - case le_dec=> ?; f_equal; omega.
    - apply shift_add; omega.
    - case le_dec=> ?; f_equal; omega.
    - case le_dec=> ?; f_equal; omega.
  - move=> t1l ? t1r ? n d c ?; simpl; f_equal; auto.
  - move=> t1' IH n d c ?; simpl; f_equal.
    replace (S (d + n)) with (d + S n) by omega; apply IH; omega.
Qed.

Lemma shift_const_subst :
  forall n t1 t2 d c, n < S d ->
  shift d c t1 = substitution3 (c + n) t2 (shift (S d) c t1).
Proof.
  move=> n; elim.
  - move=> m t2 d c ?; simpl; case le_dec=> ?;
     simpl; (case lt_eq_lt_dec; first case)=> ?; f_equal; omega.
  - move=> t1l ? t1r ? t2 d c ?; simpl; f_equal; auto.
  - by move=> t1 IH t2 d c ?; simpl; f_equal; apply IH.
Qed.

Lemma subst_subst_distr :
  forall n m t1 t2 t3,
  substitution3 (m + n) t3 (substitution3 m t2 t1) =
  substitution3 m (substitution3 n t3 t2)
    (substitution3 (S (m + n)) t3 t1).
Proof.
  move=> n m t1; move: t1 m; elim.
  - move=> v m t2 t3.
    do !(rewrite !/(substitution3 _ _ (var _));
      do !((case lt_eq_lt_dec; first case)=> ?); try omega); auto.
    - replace m with (0 + m) by omega.
      apply shift_const_subst; omega.
    - apply eq_sym, shift_subst_distr; omega.
  - by move=> t1l ? t1r ? m t2 t3; simpl; f_equal.
  - move=> t1 IH m t2 t3; simpl; f_equal.
    by replace (S (m + n)) with (S m + n) by omega.
Qed.

Lemma shift_lemma :
  forall t t' d c, parred t t' -> parred (shift d c t) (shift d c t').
Proof.
  move=> t t' d c H; move: H d c; elim.
  - move=> n d c; simpl; case le_dec=> _; auto.
  - by clear=> t1 t1' t2 t2' ? ? ? ? d c; simpl; constructor.
  - by clear=> t t' ? ? d c; simpl; constructor.
  - clear=> t1 t1' t2 t2' ? ? ? ? d c; simpl.
    replace c with (0 + c) by omega.
    rewrite subst_shift_distr.
    by constructor.
Qed.

Lemma subst_lemma :
  forall n t1 t1' t2 t2', parred t1 t1' -> parred t2 t2' ->
  parred (substitution3 n t1 t2) (substitution3 n t1' t2').
Proof.
  move=> n t1 t1' t2 t2' ? H; move: H n; elim; clear t2 t2'.
  - move=> m n; simpl; case lt_eq_lt_dec; first case; move=> ?; auto.
    by apply shift_lemma.
  - by move=> t2l t2l' t2r t2r' ? ? ? ? n; simpl; constructor.
  - move=> t2 t2' ? IH n; simpl; constructor; apply IH.
  - move=> t2 t2' t3 t3' ? H _ H0 n.
    simpl.
    rewrite (subst_subst_distr n 0).
    by constructor.
Qed.

Lemma parred_all_lemma :
  forall t t', parred t t' -> parred t' (reduce_all_redex t).
Proof.
  move=> t; elim/reduce_all_redex_ind: {t}_.
  - move=> t n H t' H0.
    rewrite H.
    by inversion H0.
  - move=> _ t1 t2 _ ? ? t' H.
    inversion H; subst.
    - inversion H2; subst; constructor; auto.
    - apply subst_lemma; auto.
  - move=> _ t1 t2 _ H ? ? t' H0.
    inversion H0; subst.
    - constructor; auto.
    - case H.
  - move=> _ t1 _ ? t2 H.
    inversion H; subst; constructor; auto.
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
