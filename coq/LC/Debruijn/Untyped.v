Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.Relations_ext LCAC.lib.ssrnat_ext.

Set Implicit Arguments.

Inductive term : Set := var of nat | app of term & term | abs of term.

Coercion var : nat >-> term.

Module Lambda_tactics.

Ltac elimif :=
  (case: ifP => //=; elimif; let hyp := fresh "H" in move => hyp) || idtac.

Ltac elimif_omega :=
  elimif;
  try (match goal with
    | |- var _ = var _ => f_equal
    | |- nth ?x ?xs _ = nth ?x ?xs _ => f_equal
    | |- _ => idtac
  end; ssromega).

End Lambda_tactics.

Import Lambda_tactics.

Fixpoint shift d c t : term :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d c.+1 t1)
  end.

Fixpoint substitute n t1 t2 : term :=
  match t2 with
    | var m =>
      if n <= m
        then (if n == m then shift n 0 t1 else m.-1)
        else m
    | app t2l t2r => app (substitute n t1 t2l) (substitute n t1 t2r)
    | abs t2' => abs (substitute n.+1 t1 t2')
  end.

Definition substitute_seqv ts m n : term :=
  shift n 0 (nth (var (m - n - size ts)) ts (m - n)).

Fixpoint substitute_seq n ts t : term :=
  match t with
    | var m => if n <= m then substitute_seqv ts m n else m
    | app t1 t2 => app (substitute_seq n ts t1) (substitute_seq n ts t2)
    | abs t' => abs (substitute_seq n.+1 ts t')
  end.

Lemma shiftzero : forall n t, shift 0 n t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  by move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add :
  forall d d' c c' t, c <= c' <= d + c ->
  shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
  move => d d' c c' t; elim: t c c' => /=.
  - move => n c c' ?; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => t IH c c' ?; rewrite IH // addnS !ltnS.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' ?; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => t' IH c c' ?; rewrite -addnS IH.
Qed.

Lemma subst_shift_distr :
  forall n d c t1 t2,
  shift d (n + c) (substitute n t1 t2) =
  substitute n (shift d c t1) (shift d (n + c).+1 t2).
Proof.
  move => n d c t1 t2; elim: t2 n => /=.
  - by move => m n; elimif_omega; rewrite -shift_shift_distr.
  - congruence.
  - by move => t IH n; rewrite (IH n.+1).
Qed.

Lemma shift_subst_distr :
  forall n d c t1 t2, c <= n ->
  shift d c (substitute n t2 t1) = substitute (d + n) t2 (shift d c t1).
Proof.
  move => n d c t1 t2; elim: t1 c n => /=.
  - by move => v c n H; elimif_omega; rewrite shift_add // addn0.
  - move => t1l IHl t1r IHr c n H; f_equal; auto.
  - by move => t1 IH c n H; rewrite -addnS IH.
Qed.

Lemma subst_shift_cancel :
  forall n d c t1 t2, n <= d ->
  substitute (c + n) t2 (shift d.+1 c t1) = shift d c t1.
Proof.
  move => n d c t1 t2; elim: t1 c => /=.
  - move => m c ?; elimif_omega.
  - move => t1l ? t1r ? c ?; f_equal; auto.
  - by move => t1 IH c ?; rewrite -IH.
Qed.

Lemma subst_subst_distr :
  forall n m t1 t2 t3,
  substitute (m + n) t3 (substitute m t2 t1) =
  substitute m (substitute n t3 t2) (substitute (S (m + n)) t3 t1).
Proof.
  move => n m t1; elim: t1 m => /=.
  - case => [ | v] m t2 t3; elimif_omega.
    - by rewrite shift_subst_distr.
    - by rewrite shift_subst_distr.
    - by rewrite (subst_shift_cancel m _ 0) // leq_addr.
  - congruence.
  - by move => t1 IH m t2 t3; rewrite -addSn IH.
Qed.

Lemma substitute_seq_cons_eq :
  forall n t ts t',
  substitute n t (substitute_seq n.+1 ts t') = substitute_seq n (t :: ts) t'.
Proof.
  move => n t ts t'; elim: t' n t ts.
  - move => /= n m t ts.
    rewrite /substitute_seqv; elimif_omega.
    - by rewrite (subst_shift_cancel m _ 0) // -(subnSK H0) subSS.
    - by move/eqP: H ->; rewrite subnn.
  - by move => /= tl IHtl tr IHtr n t ts; f_equal.
  - by move => /= t' IH n t ts; f_equal.
Qed.

Lemma substitute_seq_nil_eq : forall n t, substitute_seq n [::] t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  move => m n; rewrite /substitute_seqv nth_nil /=; elimif_omega.
Qed.

Reserved Notation "t ->1b t'" (at level 70, no associativity).
Reserved Notation "t ->bp t'" (at level 70, no associativity).

Inductive betared1 : relation term :=
  | betared1beta : forall t1 t2, app (abs t1) t2 ->1b substitute 0 t2 t1
  | betared1appl : forall t1 t1' t2, t1 ->1b t1' -> app t1 t2 ->1b app t1' t2
  | betared1appr : forall t1 t2 t2', t2 ->1b t2' -> app t1 t2 ->1b app t1 t2'
  | betared1abs  : forall t t', t ->1b t' -> abs t ->1b abs t'
  where "t ->1b t'" := (betared1 t t').

Inductive parred : relation term :=
  | parredvar  : forall n, var n ->bp var n
  | parredapp  : forall t1 t1' t2 t2',
                 t1 ->bp t1' -> t2 ->bp t2' -> app t1 t2 ->bp app t1' t2'
  | parredabs  : forall t t', t ->bp t' -> abs t ->bp abs t'
  | parredbeta : forall t1 t1' t2 t2',
                 t1 ->bp t1' -> t2 ->bp t2' ->
                 app (abs t1) t2 ->bp substitute 0 t2' t1'
  where "t ->bp t'" := (parred t t').

Notation betared := [* betared1].
Infix "->b" := betared (at level 70, no associativity).

Hint Resolve betared1beta betared1appl betared1appr betared1abs
    parredvar parredapp parredabs parredbeta.

Function reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs t1) t2 =>
      substitute 0 (reduce_all_redex t2) (reduce_all_redex t1)
    | app t1 t2 => app (reduce_all_redex t1) (reduce_all_redex t2)
    | abs t' => abs (reduce_all_redex t')
  end.

Lemma parred_refl : forall t, parred t t.
Proof.
  elim; auto.
Qed.

Lemma betaredappl : forall t1 t1' t2, t1 ->b t1' -> app t1 t2 ->b app t1' t2.
Proof.
  move => t1 t1' t2; elim => // {t1 t1'} t1 t1' t1'' ? ? ?.
  apply rt1n_trans with (app t1' t2) => //; auto.
Qed.

Lemma betaredappr : forall t1 t2 t2', t2 ->b t2' -> app t1 t2 ->b app t1 t2'.
Proof.
  move => t1 t2 t2'; elim => // {t2 t2'} t2 t2' t2'' ? ? ?.
  apply rt1n_trans with (app t1 t2') => //; auto.
Qed.

Lemma betaredabs : forall t t', t ->b t' -> abs t ->b abs t'.
Proof.
  move => t t'; elim => // {t t'} t t' t'' ? ? ?.
  apply rt1n_trans with (abs t') => //; auto.
Qed.

Hint Resolve parred_refl betaredappl betaredappr betaredabs.

Lemma betared1_in_parred : inclusion betared1 parred.
Proof.
  apply betared1_ind; auto.
Qed.

Lemma parred_in_betared : inclusion parred betared.
Proof.
  apply parred_ind => //.
  - move => t1 t1' t2 t2' ? ? ? ?; apply rtc_trans' with (app t1' t2); auto.
  - auto.
  - move => t1 t1' t2 t2' ? ? ? ?.
    apply rtc_trans' with (app (abs t1') t2); auto.
    apply rtc_trans' with (app (abs t1') t2'); auto.
    by apply rtc_step.
Qed.

Lemma subst_betared1 :
  forall n t1 t2 t2',
  t2 ->1b t2' -> substitute n t1 t2 ->1b substitute n t1 t2'.
Proof.
  move => n t1 t2 t2' H; move: t2 t2' H n.
  refine (betared1_ind _ _ _ _ _) => /=; auto => t2 t2' n.
  by rewrite (subst_subst_distr n 0).
Qed.

Lemma shift_parred :
  forall t t' d c, t ->bp t' -> shift d c t ->bp shift d c t'.
Proof.
  move => t t' d c H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _) => //=; auto => t1 t1' t2 t2' ? ? ? ? d c.
  rewrite (subst_shift_distr 0); auto.
Qed.

Lemma subst_parred :
  forall n t1 t1' t2 t2',
  t1 ->bp t1' -> t2 ->bp t2' -> substitute n t1 t2 ->bp substitute n t1' t2'.
Proof.
  move => n t1 t1' t2 t2' H H0; move: t2 t2' H0 n.
  refine (parred_ind _ _ _ _ _) => /=; auto.
  - by move => m n; elimif; apply shift_parred.
  - move => t2l t2l' ? ? t2r t2r' ? ? n.
    rewrite (subst_subst_distr n 0); auto.
Qed.

Lemma parred_all_lemma : forall t t', t ->bp t' -> t' ->bp reduce_all_redex t.
Proof with auto.
  move => t; elim/reduce_all_redex_ind: {t}_.
  - by move => t n ? t' H; inversion H; subst.
  - move => _ t1 t2 _ ? ? t' H; inversion H; subst.
    - inversion H2; subst...
    - apply subst_parred...
  - move => _ t1 t2 _ ? ? ? t' H; inversion H; subst => //...
  - move => _ t1 _ ? t2 H; inversion H; subst...
Qed.

Lemma parred_confluent : confluent parred.
Proof.
  by move => t1 t2 t3 ? ?;
    exists (reduce_all_redex t1); split; apply parred_all_lemma.
Qed.

Theorem betared_confluent : confluent betared.
Proof.
  apply (rtc_confluent' parred
    betared1_in_parred parred_in_betared parred_confluent).
Qed.
