Require Import
  Coq.Lists.List Coq.Relations.Relations Coq.Relations.Relation_Operators
  Coq.Program.Basics Omega
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
  - move => t1 t1' t2 t2' ? ? ? ?; apply rtc_trans' with (app t1' t2); auto.
  - move => t t' ? ?; auto.
  - move => t1 t1' t2 t2' ? ? ? ?.
    apply rtc_trans' with (app (abs t1') t2); auto.
    apply rtc_trans' with (app (abs t1') t2'); auto.
    apply rtc_step; constructor.
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
  apply (rtc_confluent' parred
    betared1_in_parred parred_in_betared parred_confluent).
Qed.

Fixpoint forallfv' P t n :=
  match t with
    | var m => if n <= m then P (m - n) else True
    | app t1 t2 => forallfv' P t1 n /\ forallfv' P t2 n
    | abs t => forallfv' P t n.+1
  end.

Notation forallfv P t := (forallfv' P t 0).

Lemma shift_preserves_forallfv :
  forall P t n d c, c <= n -> forallfv' P t n ->
  forallfv' P (shift d c t) (n + d).
Proof.
  move => P t n d; move : t n; elim => /=.
  - by move => t n c H; elimif_omega; rewrite subnDr.
  - move => tl IHtl tr IHtr n c H; case; auto.
  - move => t IH n c; rewrite -addSn -ltnS; auto.
Qed.

Lemma substitution_preserves_forallfv :
  forall P t1 t2 n m,
  forallfv' P t1 (n + m).+1 -> forallfv' P t2 n ->
  forallfv' P (substitution m t2 t1) (n + m).
Proof.
  move => P; elim => /=.
  - move => t1 t2 n m.
    elimif_omega.
    - by replace (t1 - (n + m).+1) with (t1.-1 - (n + m)) by ssromega.
    - move => _.
      by apply shift_preserves_forallfv.
  - move => t1l IHt1l t1r IHt1r t2 n m; case; auto.
  - move => t1 IH t2 n m; rewrite -addnS; apply IH.
Qed.

Theorem betared_preserves_forallfv :
  forall P t1 t2, t1 ->1b t2 -> forallfv P t1 -> forallfv P t2.
Proof.
  move => P t1 t2 H; move: t1 t2 H 0.
  refine (betared1_ind _ _ _ _ _).
  - move => /= t1 t2 n; case.
    rewrite -{1 3}(addn0 n).
    apply (substitution_preserves_forallfv P t1 t2 n 0).
  - by move => /= t1 t1' t2 H H0 n; case => H1 H2; split => //; apply H0.
  - by move => /= t1 t2 t2' H H0 n; case => H1 h2; split => //; apply H0.
  - move => /= t t' _ H n; apply H.
Qed.

Module STLC.

Inductive typ := tyvar of nat | tyfun of typ & typ.

Inductive typing : seq typ -> term -> typ -> Prop :=
  | typvar : forall ctx n ty, seqindex ctx n ty -> typing ctx (var n) ty
  | typapp : forall ctx t1 t2 ty1 ty2,
    typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
    typing ctx (app t1 t2) ty2
  | typabs : forall ctx t ty1 ty2,
    typing (ty1 :: ctx) t ty2 -> typing ctx (abs t) (tyfun ty1 ty2).

Lemma typvar_seqindex :
  forall ctx n ty, seqindex ctx n ty <-> typing ctx (var n) ty.
Proof.
  move => ctx n ty; split => H.
  by constructor.
  by inversion H.
Qed.

Lemma subject_shift :
  forall t ty ctx1 ctx2 ctx3,
  typing (ctx1 ++ ctx3) t ty ->
  typing (ctx1 ++ ctx2 ++ ctx3) (shift (size ctx2) (size ctx1) t) ty.
Proof.
 elim => /=.
  - move => n ty ctx1 ctx2 ctx3.
    case: ifP => H; rewrite -!typvar_seqindex.
    - by rewrite -(subnKC H) {H} -addnA (addnC (n - size ctx1)) -!lift_seqindex.
    - rewrite !appl_seqindex //; ssromega.
  - move => tl IHtl tr IHtr ty ctx1 ctx2 ctx3 H.
    inversion H; subst; apply typapp with ty1; auto.
  - move => t IH ty ctx1 ctx2 ctx3 H.
    by inversion H; subst; constructor; apply (IH _ (ty1 :: ctx1)).
Qed.

Lemma subject_substitution :
  forall ctx t1 t2 ty1 ty2 n,
  n <= size ctx ->
  typing (drop n ctx) t1 ty1 ->
  typing (insert n ty1 ctx) t2 ty2 ->
  typing ctx (substitution n t1 t2) ty2.
Proof.
  move => ctx t1 t2; move: t2 t1 ctx; elim => /=.
  - move => m t1 ctx ty1 ty2 n H H0.
    do !(case: ifP => /=); rewrite -!typvar_seqindex.
    - move/eqnP => ? _; subst; rewrite -insert_seqindex_c // => ?; subst.
      move: (subject_shift [::] (take m ctx) (drop m ctx) H0) => /=.
      rewrite cat_take_drop size_takel //.
    - move => H1 H2.
      (have: n < m by ssromega) => {H1 H2} H1.
      rewrite -{1}(ltn_predK H1) -insert_seqindex_r //; ssromega.
    - move => H1.
      rewrite -insert_seqindex_l //; ssromega.
  - move => t2l IHt2l t2r IHt2r t1 ctx ty1 ty2 n H H0 H1.
    inversion H1; subst; apply typapp with ty0.
    - by apply IHt2l with ty1.
    - by apply IHt2r with ty1.
  - move => t IH t1 ctx ty1 ty2 n H H0 H1.
    inversion H1; subst; constructor.
    by apply (IH t1 (ty0 :: ctx) ty1 ty3).
Qed.

Lemma subject_reduction1 :
  forall ctx t1 t2 ty, t1 ->1b t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => ctx t1 t2 ty H; move: t1 t2 H ctx ty.
  refine (betared1_ind _ _ _ _ _) => //=.
  - move => t1 t2 ctx ty H.
    inversion H; subst; inversion H3; subst.
    apply subject_substitution with ty1 => //.
    by rewrite drop0.
  - move => t1 t1' t2 H IH ctx ty H0.
    inversion H0; subst.
    by apply typapp with ty1; auto.
  - move => t1 t2 t2' H IH ctx ty H0.
    inversion H0; subst.
    by apply typapp with ty1; auto.
  - move => t1 t2 H IH ctx ty H0.
    inversion H0; subst; constructor; auto.
Qed.

Lemma subject_reduction :
  forall ctx t1 t2 ty, t1 ->b t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => ctx t1 t2 ty; move: t1 t2.
  exact (rtc_preservation (fun t => typing ctx t ty)
    (fun t1 t2 => @subject_reduction1 ctx t1 t2 ty)).
Qed.

Lemma typing_app_ctx :
  forall ctx ctx' t ty, typing ctx t ty -> typing (ctx ++ ctx') t ty.
Proof.
  move => ctx ctx'; move: ctx.
  refine (typing_ind _ _ _ _).
  - move => ctx n ty.
    rewrite -!typvar_seqindex.
    move: n ctx; elim => [| n IHn]; case => //.
  - move => ctx t1 t2 ty1 ty2 _ H _ H0.
    by apply typapp with ty1.
  - by move => ctx t ty1 ty2 _ H; constructor.
Qed.

Notation SNorm t := (Acc (fun x y => betared1 y x) t).

Lemma snorm_appl : forall tl tr, SNorm (app tl tr) -> SNorm tl.
Proof.
  move => tl tr; move: tl.
  fix IH 2 => tl; case => H; constructor => tl' H0.
  by apply IH, H; constructor.
Qed.

Fixpoint reducible' (ctx : seq typ) (t : term) (ty : typ) : Prop :=
  match ty with
    | tyvar n => SNorm t
    | tyfun ty1 ty2 => forall t1 ctx',
        typing (ctx ++ ctx') t1 ty1 /\ reducible' (ctx ++ ctx') t1 ty1 ->
        reducible' (ctx ++ ctx') (app t t1) ty2
  end.

Notation reducible ctx t ty := (typing ctx t ty /\ reducible' ctx t ty).

Fixpoint neutral (t : term) : Prop :=
  match t with
    | var _ => True
    | app _ _ => True
    | abs _ => False
  end.

Lemma backward : forall t, (forall t', t ->1b t' -> SNorm t') -> SNorm t.
Proof.
  elim => //=.
Qed.

Lemma CR2 :
  forall ctx t t' ty, t ->b t' -> reducible ctx t ty -> reducible ctx t' ty.
Proof.
  move => ctx t t' ty H; case => H0 H1; split.
  - by apply subject_reduction with t.
  - move: H H1 {H0}.
    apply (rtc_preservation (fun t => reducible' ctx t ty)) => {t t'}.
    move: ty ctx; elim.
    - by move => n ctx t1 t2 H; case => H0; apply H0.
    - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 ctx' H1.
      apply IHtyr with (app t1 t3).
      - by constructor.
      - by apply H0.
Qed.

Lemma CR1_3 :
  forall ty,
  (forall ctx t, reducible ctx t ty -> SNorm t) /\
  (forall ctx t, typing ctx t ty -> neutral t ->
   (forall t', t ->1b t' -> reducible ctx t' ty) -> reducible ctx t ty).
Proof.
  elim.
  - move => n; split => /= ctx t.
    - firstorder.
    - move => H H0 H1; split; last constructor; firstorder.
  - move => tyl; case => IHtyl1 IHtyl2 tyr;
      case => IHtyr1 IHtyr2; split => ctx t.
    - case => /= H H0.
      have H1: typing (ctx ++ [:: tyl ]) (var (size ctx)) tyl
        by rewrite -typvar_seqindex -(addn0 (size ctx))
          seqindex_drop (drop_size_cat [:: tyl ] Logic.eq_refl).
      have H2: typing (ctx ++ [:: tyl ]) (app t (var (size ctx))) tyr.
        by apply typapp with tyl => //; apply typing_app_ctx.
      apply snorm_appl with (var (size ctx)).
      apply IHtyr1 with (ctx ++ [:: tyl ]).
      apply IHtyr2 => // t' H3.
      apply CR2 with (app t (var (size ctx))).
      - by apply rtc_step.
      - split => //.
        apply H0, IHtyl2 => // x H4; inversion H4.
    - move => H H0 H1 /=; split => // tr ctx' H2.
      have H3: SNorm tr by apply IHtyl1 with (ctx ++ ctx').
      move: tr H3 H2.
      refine (Acc_ind _ _) => tr H2 H3 H4.
      apply IHtyr2 => //.
      - apply typapp with tyl.
        - by apply typing_app_ctx.
        - tauto.
      - move => tr' H5; inversion H5; subst.
        - move: H0 => //=.
        - split.
          - apply subject_reduction1 with (app t tr) => //.
            apply typapp with tyl.
            - by apply typing_app_ctx.
            - tauto.
          - case: (H1 t1' H9); firstorder.
        - split.
          - apply subject_reduction1 with (app t tr) => //.
            apply typapp with tyl.
            - by apply typing_app_ctx.
            - tauto.
          - apply H3 => //.
            apply CR2 with tr => //.
            apply rtc_step => //.
Qed.

End STLC.
