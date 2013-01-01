Require Import
  Coq.Arith.Compare_dec Coq.Relations.Relations Coq.Relations.Relation_Operators
  Omega ssreflect.
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

Lemma unshift_shift_sub1 :
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
  rewrite -{2}(shiftzero_eq c t) unshift_shift_sub1; auto.
  f_equal; omega.
Qed.

Lemma substitution_eq_1_2 :
  forall s t1 n t2, substitution1 (shift s 0 t1) n t2 = substitution2 s t1 n t2.
Proof.
  move=> s t1 n t2; move: t2 s t1 n; elim.
  - move=> m s t1 n; simpl; by case eq_nat_dec=> H.
  - move=> t2l ? t2r ? s t1 n; simpl; f_equal; auto.
  - move=> t2' ? s t1 n; simpl; f_equal; rewrite shift_add; last omega.
    by replace (1 + s) with (S s) by omega.
Qed.

Lemma substitution_eq_2_3 :
  forall t1 n t2,
    unshift 1 n (substitution2 n (shift 1 0 t1) n t2) = substitution3 n t1 n t2.
Proof.
  move=> t1 n t2; move: t2 t1 n; elim.
  - move=> m t1 n; simpl; case eq_nat_dec, lt_eq_lt_dec; try omega.
    - case s=> ?; try omega; clear.
      rewrite shift_add; last omega.
      replace (n + 1) with (S n) by omega.
      rewrite unshift_shift_sub1; first f_equal; omega.
    - case s=> ?; try omega; simpl; case le_dec=> ?; f_equal; omega.
    - simpl; case le_dec=> ?; f_equal; omega.
  - by move=> t2l ? t2r ? t1 n; simpl; f_equal.
  - by move=> t2' ? t1 n; simpl; f_equal.
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

Inductive betared1' : relation term :=
  | redbeta' : forall t1 t2,
               betared1' (app (abs t1) t2)
                        (unshift 1 0 (substitution1 (shift 1 0 t2) 0 t1))
  | redappl' : forall t1 t1' t2,
               betared1' t1 t1' -> betared1' (app t1 t2) (app t1' t2)
  | redappr' : forall t1 t2 t2',
               betared1' t2 t2' -> betared1' (app t1 t2) (app t1 t2')
  | redabs'  : forall t t', betared1' t t' -> betared1' (abs t) (abs t').

Inductive betared1 : relation term :=
  | redbeta : forall t1 t2,
              betared1 (app (abs t1) t2) (substitution3 0 t2 0 t1)
  | redappl : forall t1 t1' t2,
              betared1 t1 t1' -> betared1 (app t1 t2) (app t1' t2)
  | redappr : forall t1 t2 t2',
              betared1 t2 t2' -> betared1 (app t1 t2) (app t1 t2')
  | redabs  : forall t t', betared1 t t' -> betared1 (abs t) (abs t').

Inductive parred : relation term :=
  | parredvar  : forall n, parred (var n) (var n)
  | parredapp  : forall t1 t1' t2 t2',
                 parred t1 t1' -> parred t2 t2' ->
                 parred (app t1 t2) (app t1' t2')
  | parredabs  : forall t t', parred t t' -> parred (abs t) (abs t')
  | parredbeta : forall t1 t1' t2 t2',
                 parred t1 t1' -> parred t2 t2' ->
                 parred (app (abs t1) t2) (substitution3 0 t2' 0 t1').

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

Lemma shift_subst_distr :
  forall n t1 t2 d c,
  substitution3 n (shift d c t1) n (shift d (S (n + c)) t2) =
  shift d (n + c) (substitution3 n t1 n t2).
Proof.
  move=> n t1 t2;move: t2 n; elim.
  - move=> m n d c.
    rewrite {2}/shift {2}/substitution3.
    case le_dec, lt_eq_lt_dec; try omega.
    - case s=> ?; try omega; simpl.
      case le_dec, lt_eq_lt_dec; try omega; case s0=> ?; try omega.
      f_equal; omega.
    - case s=> ?; simpl; (case lt_eq_lt_dec; first case)=> ?; try omega.
      - case le_dec=> ?; f_equal; omega.
      - apply shift_shift_distr; omega.
      - (simpl; case lt_eq_lt_dec; first case)=> ?; try omega.
        case le_dec=> ?; f_equal; omega.
  - move=> t2l ? t2r ? n d c; simpl; f_equal; auto.
  - move=> t IH n d c; simpl; f_equal; apply IH.
Qed.

Lemma shift_lemma :
  forall t t' d c, parred t t' -> parred (shift d c t) (shift d c t').
Proof.
  move=> t t' d c H; move: H d c; elim.
  - move=> n d c; simpl; case le_dec=> _; apply parred_refl.
  - by clear=> t1 t1' t2 t2' ? ? ? ? d c; simpl; constructor.
  - by clear=> t t' ? ? d c; simpl; constructor.
  - clear=> t1 t1' t2 t2' ? ? ? ? d c; simpl.
    replace c with (0 + c) by omega.
    rewrite -shift_subst_distr.
    by constructor.
Qed.
