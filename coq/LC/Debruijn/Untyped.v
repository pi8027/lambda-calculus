Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Coq.Program.Basics
  Omega
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.Relations_ext LCAC.lib.ssrnat_ext LCAC.lib.seq_ext.

Set Implicit Arguments.

Inductive term : Set := var of nat | app of term & term | abs of term.

Coercion var : nat >-> term.

Local Ltac elimif :=
  (case: ifP => //=; elimif; let hyp := fresh "H" in move => hyp) || idtac.

Local Ltac elimif_omega :=
  elimif;
  try (match goal with
    | |- var _ = var _ => f_equal
    | |- nth ?x ?xs _ = nth ?x ?xs _ => f_equal
    | |- _ => idtac
  end; ssromega).

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

Inductive typ := tyvar of nat | tyfun of typ & typ.

Coercion tyvar : nat >-> typ.

Inductive typing : context typ -> term -> typ -> Prop :=
  | typvar : forall ctx n ty, ctxindex ctx n ty -> typing ctx n ty
  | typapp : forall ctx t1 t2 ty1 ty2,
    typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
    typing ctx (app t1 t2) ty2
  | typabs : forall ctx t ty1 ty2,
    typing (Some ty1 :: ctx) t ty2 -> typing ctx (abs t) (tyfun ty1 ty2).

Hint Resolve typvar typapp typabs.

Lemma typvar_seqindex :
  forall ctx n ty, typing ctx (var n) ty <-> ctxindex ctx n ty.
Proof.
  move => ctx n ty; split => H.
  - by inversion H.
  - by constructor.
Qed.

Lemma ctxleq_preserves_typing :
  forall ctx1 ctx2 t ty,
  ctxleq ctx1 ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  move => ctx1 ctx2 t ty H H0; move: ctx1 t ty H0 ctx2 H.
  refine (typing_ind _ _ _ _).
  - auto.
  - eauto.
  - move => ctx2 t tyl tyr H H0 ctx1 H1.
    by constructor; apply H0; case.
Qed.

Lemma subject_shift :
  forall t ty c ctx1 ctx2,
  typing ctx1 t ty -> typing (ctxinsert ctx2 ctx1 c) (shift (size ctx2) c t) ty.
Proof.
  move => t ty c ctx1 ctx2 H; move: ctx1 t ty H c ctx2.
  refine (typing_ind _ _ _ _).
  - move => /= ctx1 n ty H c ctx2.
    rewrite typvar_seqindex H ctxnth_ctxinsert; elimif_omega.
  - simpl; eauto.
  - move => /= ctx1 t ty1 ty2 H H0 c ctx2.
    constructor; apply (H0 c.+1).
Qed.

Lemma subject_substitute_seq :
  forall t ty n ctx ctx',
  Forall (fun p => typing (drop n ctx) p.1 p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (substitute_seq n [seq p.1 | p <- ctx'] t) ty.
Proof with auto.
  elim.
  - move => /= m ty n ctx ctx'.
    rewrite /substitute_seqv typvar_seqindex ctxnth_ctxinsert !size_map.
    elimif_omega.
    - by constructor.
    - have: (m - n < size ctx') by ssromega.
      move: {m H H0 H1} (m - n) => m H.
      rewrite !(nth_map (var 0, tyvar 0)) // => H0 [H1]; subst.
      case: {ctx' H H0} (nth _ _ _) (Forall_nth _ (var 0, tyvar 0) ctx' m H H0)
        => /= t ty.
      move/(subject_shift 0 (ctxinsert [::] (take n ctx) n)).
      rewrite size_ctxinsert /= add0n size_take minnC minKn.
      apply ctxleq_preserves_typing => {m t ty} m ty ->.
      rewrite !ctxnth_ctxinsert size_ctxinsert /= !add0n addn0 !subn0 nth_nil
        size_take minnC minKn.
      elimif; rewrite ?nth_take ?nth_drop //; f_equal; ssromega.
    - move => H2 H3; rewrite nth_default /=.
      - rewrite typvar_seqindex H3; f_equal; ssromega.
      - rewrite size_map; ssromega.
  - move => tl IHtl tr IHtr ty n ctx ctx' H H0.
    inversion H0; subst => /= {H0}; apply typapp with ty1...
  - move => /= t IH ty n ctx ctx' H H0.
    inversion H0; subst => {H0}...
Qed.

Lemma subject_reduction :
  forall ctx t1 t2 ty, t1 ->1b t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => ctx t1 t2 ty H; move: t1 t2 H ctx ty.
  refine (betared1_ind _ _ _ _ _) => //=.
  - move => t1 t2 ctx ty H.
    inversion H; subst; inversion H3; subst.
    rewrite -(substitute_seq_nil_eq 1 t1) substitute_seq_cons_eq.
    apply (subject_substitute_seq 0 ctx [:: (t2, ty1)]).
    - by rewrite /= drop0.
    - by rewrite /ctxinsert sub0n take0 drop0 /=.
  - move => t1 t1' t2 H IH ctx ty H0.
    inversion H0; subst; eauto.
  - move => t1 t2 t2' H IH ctx ty H0.
    inversion H0; subst; eauto.
  - move => t1 t2 H IH ctx ty H0.
    inversion H0; subst; auto.
Qed.

Notation SNorm t := (Acc (fun x y => betared1 y x) t).

Lemma snorm_appl : forall tl tr, SNorm (app tl tr) -> SNorm tl.
Proof.
  move => tl tr; move: tl.
  fix IH 2 => tl [H]; constructor => tl' H0.
  by apply IH, H; constructor.
Qed.

Fixpoint reducible (ctx : context typ) (t : term) (ty : typ) : Prop :=
  match ty with
    | tyvar n => SNorm t
    | tyfun ty1 ty2 => forall t1 ctx',
        ctxleq ctx ctx' -> typing ctx' t1 ty1 -> reducible ctx' t1 ty1 ->
        reducible ctx' (app t t1) ty2
  end.

Definition neutral t := (if t is abs _ then False else True).

Lemma ctxleq_preserves_reducibility :
  forall ctx ctx' t ty,
  ctxleq ctx ctx' -> reducible ctx t ty -> reducible ctx' t ty.
Proof.
  move => ctx ctx' t [] //=; auto.
Qed.

Lemma CR2 :
  forall ctx t t' ty, t ->1b t' -> reducible ctx t ty -> reducible ctx t' ty.
Proof.
  move => ctx t t' ty; elim: ty ctx t t'.
  - by move => /= _ _ t t' H []; apply.
  - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 ctx' H1 H2 H3.
    by apply IHtyr with (app t1 t3); auto; constructor.
Qed.

Arguments CR2 [ctx t t' ty] _ _.

Lemma CR1_and_CR3 :
  forall ty,
  (forall ctx t, typing ctx t ty -> reducible ctx t ty -> SNorm t) /\
  (forall ctx t, typing ctx t ty -> neutral t ->
   (forall t', t ->1b t' -> reducible ctx t' ty) -> reducible ctx t ty).
Proof.
  elim.
  - move => n; split => /= ctx t.
    - firstorder.
    - move => H H0 H1; constructor; firstorder.
  - move => tyl [IHtyl1 IHtyl2] tyr [IHtyr1 IHtyr2] /=.
    split => [ctx t H H0 | ctx tl H H0 H1 tr ctx' H2 H3 H4].
    - have H1: typing (ctx ++ [:: Some tyl]) (size ctx) tyl
        by rewrite typvar_seqindex nth_cat ltnn subnn.
      have H2: typing (ctx ++ [:: Some tyl]) (app t (size ctx)) tyr
        by apply typapp with tyl => //; move: H;
        apply ctxleq_preserves_typing, ctxleq_appr.
      apply snorm_appl with (size ctx), (IHtyr1 _ _ H2), IHtyr2 => // t' H3.
      apply (CR2 H3), H0 => //.
      - apply ctxleq_appr.
      - apply IHtyl2 => // x H4; inversion H4.
    - have H5: SNorm tr by apply IHtyl1 with ctx' => //.
      move: tr H5 H2 H3 H4; refine (Acc_ind _ _) => tr _ IH H2 H3 H4.
      have H5: typing ctx' (app tl tr) tyr.
        apply typapp with tyl.
        - by apply ctxleq_preserves_typing with ctx.
        - tauto.
      apply IHtyr2 => // t' H6.
      move: H0; inversion H6; subst => // _.
      - by apply H1.
      - apply IH => //.
        - by move: H3; apply subject_reduction.
        - by move: H4; apply CR2.
Qed.

Lemma CR1 : forall ctx t ty, typing ctx t ty -> reducible ctx t ty -> SNorm t.
Proof.
  move => ctx t ty; case: (CR1_and_CR3 ty); firstorder.
Qed.

Lemma CR3 :
  forall ctx t ty, typing ctx t ty -> neutral t ->
  (forall t', t ->1b t' -> reducible ctx t' ty) -> reducible ctx t ty.
Proof.
  move => ctx t ty; case: (CR1_and_CR3 ty) => _ H H0 H1 H2.
  apply H => //; apply H2.
Qed.

Lemma snorm_subst : forall t1 t2, SNorm (substitute 0 t2 t1) -> SNorm t1.
Proof.
  move => t1 t2.
  move: {1 3}(substitute 0 t2 t1) (erefl (substitute 0 t2 t1)) => t3 H H0.
  move: t3 H0 t1 t2 H.
  refine (Acc_ind _ _) => t3 _ IH t1 t2 H; subst; constructor => t3' H0.
  by apply (IH (substitute 0 t2 t3') (subst_betared1 0 t2 H0) t3' t2).
Qed.

Lemma abstraction_lemma :
  forall ctx t1 tyl tyr,
  typing ctx (abs t1) (tyfun tyl tyr) ->
  (forall t2 ctx', ctxleq ctx ctx' -> typing ctx' t2 tyl ->
   reducible ctx' t2 tyl -> reducible ctx' (substitute 0 t2 t1) tyr) ->
  reducible ctx (abs t1) (tyfun tyl tyr).
Proof.
  move => /= ctx t1 tyl tyr H H0 t2 ctx' H1 H2 H3.
  have H4: (typing ctx' (substitute 0 t2 t1) tyr).
    apply subject_reduction with (app (abs t1) t2); auto.
    apply typapp with tyl => //.
    by move: H; apply ctxleq_preserves_typing.
  move: (snorm_subst t1 t2 (CR1 H4 (H0 t2 ctx' H1 H2 H3))) (CR1 H2 H3) => H5 H6.
  move: t1 H5 t2 H6 H H0 H1 H2 H3 {H4}.
  refine (Acc_ind _ _) => t1 H H0.
  refine (Acc_ind _ _) => t2 H1 H2 H3 H4 H5 H6 H7.
  apply CR3 => //.
  - apply typapp with tyl => //.
    by apply ctxleq_preserves_typing with ctx.
  - move => t3 H8.
    inversion H8; subst => {H8}; auto.
    - inversion H12; subst => {H12}.
      apply H0 => //.
      - by apply subject_reduction with (abs t1); auto.
      - by move => t'' ctx'' H8 H10 H11;
          apply (CR2 (subst_betared1 0 t'' H9)), H4.
    - apply H2 => //.
      - by apply subject_reduction with t2.
      - by apply CR2 with t2.
Qed.

Lemma reduce_lemma :
  forall ctx (ctx' : seq (term * typ)) t ty,
  typing ([seq Some p.2 | p <- ctx'] ++ ctx) t ty ->
  Forall (fun p => typing ctx p.1 p.2 /\ reducible ctx p.1 p.2) ctx' ->
  reducible ctx (substitute_seq 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  move => ctx ctx' t ty; elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx'.
    rewrite /substitute_seqv typvar_seqindex subn0 size_map shiftzero.
    elim: ctx' n => [| c' ctx' IH []] /=.
    - move => n H _; rewrite nth_nil subn0.
      apply CR3 => //; auto => t' H0; inversion H0.
    - by move => [->] [[_ H] _].
    - by move => n H [_ H0]; apply IH.
  - move => tl IHtl tr IHtr ty ctx ctx' H H0.
    inversion H; subst => {H}.
    move: (IHtl (tyfun ty1 ty) ctx ctx') => /=; apply; auto.
    apply subject_substitute_seq.
    - rewrite drop0; move: H0; apply Forall_impl; tauto.
    - by rewrite /ctxinsert sub0n take0 drop0 /=.
  - move => t IHt ty ctx ctx' H H0.
    inversion H; subst => {H} /=.
    apply abstraction_lemma.
    - constructor.
      apply subject_substitute_seq.
      - rewrite /= drop0; move: H0; apply Forall_impl; tauto.
      - by rewrite /ctxinsert /= take0 drop0 /=.
    - move => t2 ctx2 H H1 H2.
      rewrite substitute_seq_cons_eq.
      apply (IHt ty2 ctx2 ((t2, ty1) :: ctx')) => /=.
      - move: H3; apply ctxleq_preserves_typing.
        move: H; apply (ctxleq_appl (Some ty1 :: _)).
      - split => //.
        move: H0; apply Forall_impl => p [H4 H5]; split.
        - by move: H4; apply ctxleq_preserves_typing.
        - by move: H5; apply ctxleq_preserves_reducibility.
Qed.

Theorem typed_term_is_snorm : forall ctx t ty, typing ctx t ty -> SNorm t.
Proof.
  move => ctx t ty H.
  apply (@CR1 ctx t ty) => //.
  move: (@reduce_lemma ctx [::] t ty H) => /=.
  by rewrite substitute_seq_nil_eq; apply.
Qed.
