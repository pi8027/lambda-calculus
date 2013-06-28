Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.Relations_ext LCAC.lib.ssrnat_ext LCAC.lib.seq_ext.

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

Ltac elimleq :=
  let H := fresh "H" in
  match goal with
    | [ |- is_true (?m <= ?n) -> _ ] =>
      move => H; rewrite -(subnK H) ?(addnK, addKn); move: {n H} (n - m) => n
  end.

End Lambda_tactics.

Import Lambda_tactics.

Fixpoint shift d c t : term :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d c.+1 t1)
  end.

Definition substitutev ts m n : term :=
  shift n 0 (nth (var (m - n - size ts)) ts (m - n)).

Fixpoint substitute n ts t : term :=
  match t with
    | var m => if n <= m then substitutev ts m n else m
    | app t1 t2 => app (substitute n ts t1) (substitute n ts t2)
    | abs t' => abs (substitute n.+1 ts t')
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
  move => d d' c c' t; case/andP; elimleq; rewrite leq_add2r; elimleq.
  elim: t c d => /=; try (move: addnS; congruence); move => *; elimif_omega.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
  move => d c d' c' t; elimleq; elim: t c' c => /=;
    try (move: addnS; congruence); move => *; elimif_omega.
Qed.

Lemma subst_shift_distr :
  forall n d c ts t,
  shift d (n + c) (substitute n ts t) =
  substitute n (map (shift d c) ts) (shift d (size ts + n + c) t).
Proof.
  move => n d c ts t; elim: t n => /=; try (move: addnS addSn; congruence).
  move => v n; elimif_omega; rewrite /substitutev.
  - rewrite !nth_default ?size_map /=; try ssromega.
    rewrite !(subnAC _ n) subnK; elimif_omega.
  - rewrite -shift_shift_distr // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma shift_subst_distr :
  forall n d c ts t, c <= n ->
  shift d c (substitute n ts t) = substitute (d + n) ts (shift d c t).
Proof.
  move => n d c ts t; elimleq; elim: t c n => /=;
    try (move: addnS; congruence); move => v c n; elimif_omega.
  by rewrite /substitutev shift_add ?addn0 ?leq_addl // !subnDA addnK.
Qed.

Lemma subst_shift_cancel :
  forall n d c ts t, c <= n -> size ts + n <= d + c ->
  substitute n ts (shift d c t) = shift (d - size ts) c t.
Proof.
  move => n d c ts t; elimleq; rewrite addnA leq_add2r; elimleq.
  elim: t c d => /=; try (move: addnS; congruence); move => v c d; elimif_omega.
  rewrite /substitutev nth_default /=; elimif_omega.
Qed.

Lemma subst_subst_distr :
  forall n m xs ys t,
  substitute (m + n) xs (substitute m ys t) =
  substitute m (map (substitute n xs) ys) (substitute (size ys + m + n) xs t).
Proof.
  move => n m xs ys t; elim: t m => /=; try (move: addnS addSn; congruence).
  move => v m; elimif_omega; rewrite /substitutev.
  - rewrite (subst_shift_cancel m) // ?size_map; try ssromega.
    rewrite nth_default /= /substitutev; elimif_omega.
    by rewrite !(nth_map' (shift _ _)) /= subnDA addnK
      (addnC _ m) addnAC addnK !subnDA (subnAC _ n (size ys)).
  - rewrite size_map -shift_subst_distr // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_app :
  forall n xs ys t,
  substitute n xs (substitute (size xs + n) ys t) = substitute n (xs ++ ys) t.
Proof.
  move => n xs ys t; elim: t n => /=; try (move: addnS; congruence).
  move => v n; rewrite /substitutev nth_cat size_cat; elimif_omega.
  - by rewrite subst_shift_cancel ?addn0 // addKn addnC !subnDA.
  - rewrite /substitutev; f_equal; apply nth_equal; ssromega.
Qed.

Lemma subst_nil : forall n t, substitute n [::] t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  move => m n; rewrite /substitutev nth_nil /=; elimif_omega.
Qed.

Reserved Notation "t ->1b t'" (at level 70, no associativity).
Reserved Notation "t ->bp t'" (at level 70, no associativity).

Inductive betared1 : relation term :=
  | betared1beta : forall t1 t2, app (abs t1) t2 ->1b substitute 0 [:: t2] t1
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
                 app (abs t1) t2 ->bp substitute 0 [:: t2'] t1'
  where "t ->bp t'" := (parred t t').

Notation betared := [* betared1].
Infix "->b" := betared (at level 70, no associativity).

Hint Resolve betared1beta betared1appl betared1appr betared1abs
    parredvar parredapp parredabs parredbeta.

Function reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs t1) t2 =>
      substitute 0 [:: reduce_all_redex t2] (reduce_all_redex t1)
    | app t1 t2 => app (reduce_all_redex t1) (reduce_all_redex t2)
    | abs t' => abs (reduce_all_redex t')
  end.

Lemma parred_refl : forall t, parred t t.
Proof.
  elim; auto.
Qed.

Lemma betaredappl : forall t1 t1' t2, t1 ->b t1' -> app t1 t2 ->b app t1' t2.
Proof.
  move => t1 t1' t2; elim => // {t1 t1'} t1 t1' t1'' H H0 H1.
  apply rt1n_trans with (app t1' t2) => //; auto.
Qed.

Lemma betaredappr : forall t1 t2 t2', t2 ->b t2' -> app t1 t2 ->b app t1 t2'.
Proof.
  move => t1 t2 t2'; elim => // {t2 t2'} t2 t2' t2'' H H0 H1.
  apply rt1n_trans with (app t1 t2') => //; auto.
Qed.

Lemma betaredabs : forall t t', t ->b t' -> abs t ->b abs t'.
Proof.
  move => t t'; elim => // {t t'} t t' t'' H H0 H1.
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
  - move => t1 t1' t2 t2' H H0 H1 H2; apply rtc_trans' with (app t1' t2); auto.
  - auto.
  - move => t1 t1' t2 t2' H H0 H1 H2.
    apply rtc_trans' with (app (abs t1') t2); auto.
    apply rtc_trans' with (app (abs t1') t2'); auto.
    by apply rtc_step.
Qed.

Lemma subst_betared1 :
  forall n ts t t', t ->1b t' -> substitute n ts t ->1b substitute n ts t'.
Proof.
  move => n t1 t2 t2' H; move: t2 t2' H n.
  refine (betared1_ind _ _ _ _ _) => /=; auto => t2 t2' n.
  by rewrite (subst_subst_distr n 0) /= !add1n.
Qed.

Lemma shift_parred :
  forall t t' d c, t ->bp t' -> shift d c t ->bp shift d c t'.
Proof.
  move => t t' d c H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _) => //=; auto => t1 t1' t2 t2' H H0 H1 H2 d c.
  rewrite (subst_shift_distr 0) /= !add1n; auto.
Qed.

Lemma subst_parred :
  forall n ps t t', Forall (prod_curry parred) ps -> t ->bp t' ->
  substitute n [seq fst p | p <- ps] t ->bp
  substitute n [seq snd p | p <- ps] t'.
Proof.
  move => n ps t t' H H0; move: t t' H0 n.
  refine (parred_ind _ _ _ _ _) => /=; auto.
  - move => v n; elimif; rewrite /substitutev !size_map; apply shift_parred.
    elim: {v n H0} ps (v - n) H => //= [[t t']] ps IH [| v] [] //= H H0.
    by rewrite subSS; apply IH.
  - move => t1 t1' t2 t2' H0 H1 H2 H3 n.
    by rewrite (subst_subst_distr n 0) /= !add1n; auto.
Qed.

Lemma parred_all_lemma : forall t t', t ->bp t' -> t' ->bp reduce_all_redex t.
Proof with auto.
  move => t; elim/reduce_all_redex_ind: {t}_.
  - by move => t n H t' H0; inversion H0; subst.
  - move => _ t1 t2 _ H H0 t' H1; inversion H1; subst.
    - inversion H4; subst...
    - apply (subst_parred 0 [:: (t2', reduce_all_redex t2)]) => /=; auto.
  - move => _ t1 t2 _ H H0 H1 t' H2; inversion H2; subst => //...
  - move => _ t1 _ H t2 H0; inversion H0; subst...
Qed.

Lemma parred_confluent : confluent parred.
Proof.
  by move => t1 t2 t3 H H0;
    exists (reduce_all_redex t1); split; apply parred_all_lemma.
Qed.

Theorem betared_confluent : confluent betared.
Proof.
  apply (rtc_confluent' parred
    betared1_in_parred parred_in_betared parred_confluent).
Qed.
