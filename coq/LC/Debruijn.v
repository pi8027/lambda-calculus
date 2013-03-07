Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Omega
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.Relations_ext LCAC.ssrnat_ext LCAC.seq_ext.

Set Implicit Arguments.

Local Ltac elimif_omega := do ! ((try (f_equal; ssromega)); case: ifP => //= ?).

Inductive term : Set := var of nat | app of term & term | abs of term.

Fixpoint shift d c t : term :=
  match t with
    | var n => (if leq c n then var (n + d) else var n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (S c) t1)
  end.

Fixpoint unshift d c t : term :=
  match t with
    | var n => (if leq c n then var (n - d) else var n)
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
  - move => n c c' ?; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - move => t IH c c' ?; f_equal; apply IH; ssromega.
Qed.

Lemma shiftzero_eq : forall n t, shift 0 n t = t.
Proof.
  move => n t; move: t n; elim => /=; try congruence.
  move => m n; case: ifP => ?; f_equal; ssromega.
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

Lemma substitution_eq :
  forall n t1 t2,
  unshift 1 n (substitution' n (shift (S n) 0 t1) t2) = substitution n t1 t2.
Proof.
  move => n t1 t2; move: t2 t1 n; elim => /=.
  - move => n t1 m; elimif_omega.
    rewrite unshift_shift_sub; f_equal; ssromega.
  - congruence.
  - by move => t2 IH t1 n; f_equal; rewrite shift_add.
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
  move => t1 t1' t2; elim => // {t1 t1'} t1 t1' t1'' ? ? ?.
  by apply rt1n_trans with (app t1' t2) => //; constructor.
Qed.

Lemma betaredappr :
  forall t1 t2 t2', betared t2 t2' -> betared (app t1 t2) (app t1 t2').
Proof.
  move => t1 t2 t2'; elim => // {t2 t2'} t2 t2' t2'' ? ? ?.
  by apply rt1n_trans with (app t1 t2') => //; constructor.
Qed.

Lemma betaredabs : forall t t', betared t t' -> betared (abs t) (abs t').
Proof.
  move => t t'; elim => // {t t'} t t' t'' ? ? ?.
  by apply rt1n_trans with (abs t') => //; constructor.
Qed.

Hint Resolve parred_refl betaredappl betaredappr betaredabs.

Lemma betared1_in_parred : inclusion betared1 parred.
Proof.
  by move => t t'; elim; intros; constructor.
Qed.

Lemma parred_in_betared : inclusion parred betared.
Proof.
  move => t t'; elim => //; clear.
  - move => t1 t1' t2 t2' ? ? ? ?; apply rt1n_trans' with (app t1' t2); auto.
  - move => t t' ? ?; auto.
  - move => t1 t1' t2 t2' ? ? ? ?.
    apply rt1n_trans' with (app (abs t1') t2); auto.
    apply rt1n_trans' with (app (abs t1') t2'); auto.
    apply rt1n_step; constructor.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
  move => d c d' c' t; move: t c c'; elim => /=.
  - move => n c c' ?; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => t' IH c c' ?; f_equal; rewrite -addnS; apply IH.
Qed.

Lemma subst_shift_distr :
  forall n t1 t2 d c,
  shift d (n + c) (substitution n t1 t2) =
  substitution n (shift d c t1) (shift d (S (n + c)) t2).
Proof.
  move => n t1 t2;move: t2 n; elim => //=.
  - move => m n d c; elimif_omega.
    apply Logic.eq_sym, shift_shift_distr; ssromega.
  - by move => t2l ? t2r ? n d c; f_equal.
  - move => t IH n d c; f_equal; apply (IH (S n)).
Qed.

Lemma shift_subst_distr :
  forall t1 t2 n d c, c <= n ->
  shift d c (substitution n t2 t1) = substitution (d + n) t2 (shift d c t1).
Proof.
  move => t1 t2; elim t1 => /=.
  - move => m n d c ?; elimif_omega; apply shift_add; ssromega.
  - move => t1l ? t1r ? n d c ?; f_equal; auto.
  - move => t1' IH n d c ?; rewrite -addnS IH //.
Qed.

Lemma shift_const_subst :
  forall n t1 t2 d c, n < S d ->
  shift d c t1 = substitution (c + n) t2 (shift (S d) c t1).
Proof.
  move => n; elim => /=.
  - move => m t2 d c ?; elimif_omega.
  - move => t1l ? t1r ? t2 d c ?; f_equal; auto.
  - by move => t1 IH t2 d c ?; f_equal; apply IH.
Qed.

Lemma subst_subst_distr :
  forall n m t1 t2 t3,
  substitution (m + n) t3 (substitution m t2 t1) =
  substitution m (substitution n t3 t2)
    (substitution (S (m + n)) t3 t1).
Proof.
  move => n m t1; move: t1 m; elim => /=.
  - case => [ | v] m t2 t3; elimif_omega.
    - by apply Logic.eq_sym, shift_subst_distr.
    - by apply Logic.eq_sym, shift_subst_distr.
    - apply (shift_const_subst m t3 _ (m + n) 0); ssromega.
  - congruence.
  - by move => t1 IH m t2 t3; f_equal; rewrite -addSn.
Qed.

Lemma shift_lemma :
  forall t t' d c, parred t t' -> parred (shift d c t) (shift d c t').
Proof.
  move => t t' d c H; move: H d c; elim; clear => //=; try by constructor.
  move => t1 t1' t2 t2' ? ? ? ? d c.
  rewrite -(add0n c) subst_shift_distr.
  by constructor.
Qed.

Lemma subst_lemma :
  forall n t1 t1' t2 t2', parred t1 t1' -> parred t2 t2' ->
  parred (substitution n t1 t2) (substitution n t1' t2').
Proof.
  move => n t1 t1' t2 t2' H H0; move: t2 t2' H0 n.
  refine (parred_ind _ _ _ _ _) => /=; try constructor; auto.
  - by move => m n; do !case: ifP => ? //; apply shift_lemma.
  - move => t2l t2l' ? ? t2r t2r' ? ? n.
    by rewrite (subst_subst_distr n 0); constructor.
Qed.

Lemma parred_all_lemma :
  forall t t', parred t t' -> parred t' (reduce_all_redex t).
Proof with auto.
  move => t; elim/reduce_all_redex_ind: {t}_.
  - by move => t n ? t' H; subst; inversion H.
  - move => _ t1 t2 _ ? ? t' H; inversion H; subst.
    - inversion H2; subst; constructor...
    - apply subst_lemma...
  - move => _ t1 t2 _ ? ? ? t' H; inversion H; subst => //; constructor...
  - move => _ t1 _ ? t2 H; inversion H; subst; constructor...
Qed.

Lemma parred_confluent : confluent parred.
Proof.
  by move => t1 t2 t3 ? ?;
    exists (reduce_all_redex t1); split; apply parred_all_lemma.
Qed.

Theorem betared_confluent : confluent betared.
Proof.
  apply (rt1n_confluent' parred
    betared1_in_parred parred_in_betared parred_confluent).
Qed.

Module STLC.

Inductive typ := tyvar of nat | tyfun of typ & typ.

Inductive typing : seq typ -> term -> typ -> Prop :=
  | typvar : forall ctx n ty, seqindex ctx n ty -> typing ctx (var n) ty
  | tyapp  : forall ctx t1 t2 ty1 ty2,
    typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
    typing ctx (app t1 t2) ty2
  | tyabs  : forall ctx t ty1 ty2,
    typing (ty1 :: ctx) t ty2 -> typing ctx (abs t) (tyfun ty1 ty2).

Lemma typvar_seqindex :
  forall ctx n ty, seqindex ctx n ty <-> typing ctx (var n) ty.
Proof.
  move => ctx n ty; split => H.
  by constructor.
  by inversion H.
Qed.

Lemma typing_shift_drop :
  forall ctx t ty d c,
  typing (take c ctx ++ drop (d + c) ctx) t ty <-> typing ctx (shift d c t) ty.
Proof.
  move => ctx t; move: t ctx; elim => //=.
  - move => n ctx ty d c.
    case: ifP => H; case: (leqP c (size ctx)) => H0; rewrite -!typvar_seqindex.
    - rewrite (nthopt_drop' _ n) (nthopt_drop' _ (n + d))
        -{1}(subnKC H) addnC -drop_addn (@drop_size_cat _ c (take c ctx)).
      by rewrite drop_addn addnC -addnA (subnKC H) addnC.
      by apply size_takel.
    - rewrite (nthopt_drop' _ n) (nthopt_drop' _ (n + d))
        !drop_oversize ?cats0 //; try ssromega.
      apply leq_trans with c => //.
      rewrite size_take; case: ifP => H1; ssromega.
    - move: ctx c n H H0.
      elim => // ty' ctx IH; case => // c; case => // n H H0.
      by rewrite addnS /=; apply IH.
    - move: ctx c n H H0.
      elim => // ty' ctx IH; case => // c; case => // n H H0.
      by rewrite addnS /=; apply IH.
  - move => tl IHtl tr IHtr ctx ty d c.
    split => H; inversion H; subst; apply tyapp with ty1.
    - by apply (proj1 (IHtl ctx (tyfun ty1 ty) d c)).
    - by apply (proj1 (IHtr ctx ty1 d c)).
    - by apply (proj2 (IHtl ctx (tyfun ty1 ty) d c)).
    - by apply (proj2 (IHtr ctx ty1 d c)).
  - move => t IH ctx ty; split => H; inversion H; subst; constructor.
    - apply (proj1 (IH (ty1 :: ctx) ty2 d c.+1)).
      rewrite -addSnnS //=.
    - move: (proj2 (IH (ty1 :: ctx) ty2 d c.+1)).
      rewrite -addSnnS //=; auto.
Qed.

Lemma shift_type_preserve :
  forall t ty ctx1 ctx2 ctx3,
  typing (ctx1 ++ ctx3) t ty ->
  typing (ctx1 ++ ctx2 ++ ctx3) (shift (size ctx2) (size ctx1) t) ty.
Proof.
 elim => /=.
  - move => n ty ctx1 ctx2 ctx3 H.
    inversion H; subst => /= {H}.
    case: ifP => H /=; constructor.
    - by move: H2; rewrite -(subnKC H) {H}
        -addnA (addnC (n - size ctx1)) -!lift_seqindex.
    - move: H2; rewrite !appl_seqindex //; ssromega.
  - move => tl IHtl tr IHtr ty ctx1 ctx2 ctx3 H.
    inversion H; subst; apply tyapp with ty1; auto.
  - move => t IH ty ctx1 ctx2 ctx3 H.
    by inversion H; subst; constructor; apply (IH _ (ty1 :: ctx1)).
Qed.

Lemma substitution_type_preserve :
  forall ctx t1 t2 ty1 ty2 n,
  typing (drop n ctx) t1 ty1 ->
  typing (insert n ty1 ctx) t2 ty2 ->
  n <= size ctx -> typing ctx (substitution n t1 t2) ty2.
Proof.
  move => ctx t1 t2; move: t2 t1 ctx; elim => /=.
  - move => m t1 ctx ty1 ty2 n H H0 H1;
      inversion H0; simpl in *; subst; do !case: ifP => /=.
    - move/eqnP => ? _; subst.
      move: H4; rewrite -insert_seqindex_c // => ?; subst.
      by rewrite -typing_shift_drop take0 //= addn0.
    - move => H2 H3; constructor.
      (have: n < m by ssromega) => {H0 H2 H3} H0; move: H4.
      rewrite -{1}(ltn_predK H0) -insert_seqindex_r //; ssromega.
    - move => H2; constructor.
      (have: m < n by ssromega) => {H0 H2} H0; move: H4.
      rewrite -insert_seqindex_l //; ssromega.
  - move => t2l IHt2l t2r IHt2r t1 ctx ty1 ty2 n H H0 H1.
    inversion H0; subst; apply tyapp with ty0.
    - by apply IHt2l with ty1.
    - by apply IHt2r with ty1.
  - move => t IH t1 ctx ty1 ty2 n H H0 H1.
    inversion H0; subst; constructor.
    by apply (IH t1 (ty0 :: ctx) ty1 ty3).
Qed.

Lemma type_preserve1 :
  forall ctx t1 t2 ty, t1 ->1b t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => ctx t1 t2 ty H; move: t1 t2 H ctx ty.
  refine (betared1_ind _ _ _ _ _) => //=.
  - move => t1 t2 ctx ty H.
    inversion H; subst; inversion H3; subst.
    apply substitution_type_preserve with ty1 => //.
    by rewrite drop0.
  - move => t1 t1' t2 H IH ctx ty H0.
    inversion H0; subst.
    by apply tyapp with ty1; auto.
  - move => t1 t2 t2' H IH ctx ty H0.
    inversion H0; subst.
    by apply tyapp with ty1; auto.
  - move => t1 t2 H IH ctx ty H0.
    inversion H0; subst; constructor; auto.
Qed.

Theorem type_preserve :
  forall ctx t1 t2 ty, t1 ->b t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => ctx t1 t2 ty; move: t1 t2.
  refine (clos_refl_trans_1n_ind _ _ _ _ _) => // t1 t2 t3 H _ IH H0.
  apply IH.
  by apply type_preserve1 with t1.
Qed.

End STLC.
