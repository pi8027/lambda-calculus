Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Coq.Program.Basics
  Omega
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.Relations_ext LCAC.ssrnat_ext LCAC.seq_ext LCAC.context.

Set Implicit Arguments.

Local Ltac elimif_omega :=
  do !((try (f_equal; ssromega));
       let hyp := fresh "H" in case: ifP => //= hyp).

Inductive term : Set := var of nat | app of term & term | abs of term.

Fixpoint shift d c t : term :=
  match t with
    | var n => (if leq c n then var (n + d) else var n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d c.+1 t1)
  end.

Fixpoint unshift d c t : term :=
  match t with
    | var n => (if leq c n then var (n - d) else var n)
    | app t1 t2 => app (unshift d c t1) (unshift d c t2)
    | abs t1 => abs (unshift d c.+1 t1)
  end.

Fixpoint substitute' n t1 t2 : term :=
  match t2 with
    | var m => (if eqn n m then t1 else var m)
    | app t2l t2r => app (substitute' n t1 t2l) (substitute' n t1 t2r)
    | abs t2' => abs (substitute' n.+1 (shift 1 0 t1) t2')
  end.

Fixpoint substitute n t1 t2 : term :=
  match t2 with
    | var m =>
      if leq n m
        then (if eqn n m then shift n 0 t1 else var m.-1)
        else var m
    | app t2l t2r => app (substitute n t1 t2l) (substitute n t1 t2r)
    | abs t2' => abs (substitute n.+1 t1 t2')
  end.

Fixpoint substitute_seq_var n ts v : term :=
  if ts is t :: ts
    then (if v is v.+1 then substitute_seq_var n ts v else shift n 0 t)
    else var (v + n).

Fixpoint substitute_seq n ts t : term :=
  match t with
    | var m => if leq n m then substitute_seq_var n ts (m - n) else var m
    | app t1 t2 => app (substitute_seq n ts t1) (substitute_seq n ts t2)
    | abs t' => abs (substitute_seq n.+1 ts t')
  end.

Lemma shiftzero : forall n t, shift 0 n t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  by move => m n; rewrite addn0; case: ifP.
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
  forall n t1 t2 d c,
  shift d (n + c) (substitute n t1 t2) =
  substitute n (shift d c t1) (shift d (n + c).+1 t2).
Proof.
  move => n t1 t2; elim: t2 n => /=.
  - move => m n d c; elimif_omega; rewrite -shift_shift_distr //.
  - congruence.
  - by move => t IH n d c; rewrite (IH n.+1).
Qed.

Lemma shift_subst_distr :
  forall t1 t2 n d c, c <= n ->
  shift d c (substitute n t2 t1) = substitute (d + n) t2 (shift d c t1).
Proof.
  move => t1 t2; elim t1 => /=.
  - by move => m n d c ?; elimif_omega; rewrite shift_add // addn0.
  - move => t1l ? t1r ? n d c ?; f_equal; auto.
  - by move => t1' IH n d c ?; rewrite -addnS IH.
Qed.

Lemma shift_const_subst :
  forall n t1 t2 d c, n <= d ->
  shift d c t1 = substitute (c + n) t2 (shift d.+1 c t1).
Proof.
  move => n t1 t2 d c; elim: t1 c => /=.
  - move => m c ?; elimif_omega.
  - move => t1l ? t1r ? c ?; f_equal; auto.
  - by move => t1 IH c ?; rewrite IH.
Qed.

Lemma subst_subst_distr :
  forall n m t1 t2 t3,
  substitute (m + n) t3 (substitute m t2 t1) =
  substitute m (substitute n t3 t2)
    (substitute (S (m + n)) t3 t1).
Proof.
  move => n m t1; elim: t1 m => /=.
  - case => [ | v] m t2 t3; elimif_omega.
    - by rewrite shift_subst_distr.
    - by rewrite shift_subst_distr.
    - apply (shift_const_subst m t3 _ (m + n) 0); ssromega.
  - congruence.
  - by move => t1 IH m t2 t3; rewrite -addSn IH.
Qed.

Lemma substitute_seq_cons_eq :
  forall n t ts t',
  substitute n t (substitute_seq n.+1 ts t') = substitute_seq n (t :: ts) t'.
Proof.
  move => n t ts t'; elim: t' n t ts.
  - move => /= n m t ts.
    elimif_omega.
    - rewrite -(subnSK H).
      elim: ts (n - m.+1) => //=.
      - move => x; elimif_omega.
      - move => t' ts IH; case => // {IH}.
        by rewrite -{1}(add0n m) -shift_const_subst.
    - by move/eqnP: H1 => H1; rewrite H1 subnn.
  - by move => /= tl IHtl tr IHtr n t ts; f_equal.
  - by move => /= t' IH n t ts; f_equal.
Qed.

Lemma substitute_seq_nil_eq : forall n t, substitute_seq n [::] t = t.
Proof.
  move => n t; elim: t n => /=.
  - by move => n m; case: ifP => // H; rewrite addnC subnKC.
  - by move => tl IHtl tr IHtr n; f_equal.
  - by move => t H n; f_equal.
Qed.

Lemma unshift_shift_sub :
  forall d d' c c' t, c <= c' <= d + c -> d' <= d ->
  unshift d' c' (shift d c t) = shift (d - d') c t.
Proof.
  move => d d' c c' t; elim: t c c' => /=.
  - move => n c c' ? ?; elimif_omega.
  - move => t1 ? t2 ? c c' ? ?; f_equal; auto.
  - by move => t IH c c' ? ?; rewrite IH // addnS !ltnS.
Qed.

Lemma substitute_eq :
  forall n t1 t2,
  unshift 1 n (substitute' n (shift n.+1 0 t1) t2) = substitute n t1 t2.
Proof.
  move => n t1 t2; elim: t2 t1 n => /=.
  - move => n t1 m; elimif_omega.
    rewrite unshift_shift_sub; f_equal; ssromega.
  - congruence.
  - by move => t2 IH t1 n; f_equal; rewrite shift_add.
Qed.

Reserved Notation "t ->1b t'" (at level 70, no associativity).
Reserved Notation "t ->bp t'" (at level 70, no associativity).

Inductive betared1' : relation term :=
  | betared1beta' : forall t1 t2,
                    betared1' (app (abs t1) t2)
                              (unshift 1 0 (substitute' 0 (shift 1 0 t2) t1))
  | betared1appl' : forall t1 t1' t2,
                    betared1' t1 t1' -> betared1' (app t1 t2) (app t1' t2)
  | betared1appr' : forall t1 t2 t2',
                    betared1' t2 t2' -> betared1' (app t1 t2) (app t1 t2')
  | betared1abs'  : forall t t', betared1' t t' -> betared1' (abs t) (abs t').

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

Function reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs t1) t2 =>
      substitute 0 (reduce_all_redex t2) (reduce_all_redex t1)
    | app t1 t2 => app (reduce_all_redex t1) (reduce_all_redex t2)
    | abs t' => abs (reduce_all_redex t')
  end.

Lemma betared1_eq : same_relation betared1' betared1.
Proof.
  split; elim; (try by constructor) => ? ?.
  - rewrite substitute_eq; constructor.
  - rewrite -substitute_eq; constructor.
Qed.

Lemma parred_refl : forall t, parred t t.
Proof.
  by elim; constructor.
Qed.

Lemma betaredappl :
  forall t1 t1' t2, t1 ->b t1' -> app t1 t2 ->b app t1' t2.
Proof.
  move => t1 t1' t2; elim => // {t1 t1'} t1 t1' t1'' ? ? ?.
  by apply rt1n_trans with (app t1' t2) => //; constructor.
Qed.

Lemma betaredappr :
  forall t1 t2 t2', t2 ->b t2' -> app t1 t2 ->b app t1 t2'.
Proof.
  move => t1 t2 t2'; elim => // {t2 t2'} t2 t2' t2'' ? ? ?.
  by apply rt1n_trans with (app t1 t2') => //; constructor.
Qed.

Lemma betaredabs : forall t t', t ->b t' -> abs t ->b abs t'.
Proof.
  move => t t'; elim => // {t t'} t t' t'' ? ? ?.
  by apply rt1n_trans with (abs t') => //; constructor.
Qed.

Hint Resolve parred_refl betaredappl betaredappr betaredabs.

Lemma betared1_in_parred : inclusion betared1 parred.
Proof.
  by apply betared1_ind; constructor.
Qed.

Lemma parred_in_betared : inclusion parred betared.
Proof.
  apply parred_ind => //.
  - move => t1 t1' t2 t2' ? ? ? ?; apply rtc_trans' with (app t1' t2); auto.
  - auto.
  - move => t1 t1' t2 t2' ? ? ? ?.
    apply rtc_trans' with (app (abs t1') t2); auto.
    apply rtc_trans' with (app (abs t1') t2'); auto.
    apply rtc_step; constructor.
Qed.

Lemma subst_betared1 :
  forall n t1 t2 t2', t2 ->1b t2' ->
  substitute n t1 t2 ->1b substitute n t1 t2'.
Proof.
  move => n t1 t2 t2' H; move: t2 t2' H n.
  refine (betared1_ind _ _ _ _ _); try by constructor.
  move => t2 t2' n.
  rewrite (subst_subst_distr n 0).
  constructor.
Qed.

Lemma shift_parred :
  forall t t' d c, t ->bp t' -> shift d c t ->bp shift d c t'.
Proof.
  move => t t' d c H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _) => //; try by constructor.
  move => t1 t1' t2 t2' ? ? ? ? d c /=.
  rewrite (subst_shift_distr 0).
  by constructor.
Qed.

Lemma subst_parred :
  forall n t1 t1' t2 t2',
  t1 ->bp t1' -> t2 ->bp t2' -> substitute n t1 t2 ->bp substitute n t1' t2'.
Proof.
  move => n t1 t1' t2 t2' H H0; move: t2 t2' H0 n.
  refine (parred_ind _ _ _ _ _) => /=; try constructor; auto.
  - by move => m n; do !case: ifP => // _; apply shift_parred.
  - move => t2l t2l' ? ? t2r t2r' ? ? n.
    by rewrite (subst_subst_distr n 0); constructor.
Qed.

Lemma parred_all_lemma : forall t t', t ->bp t' -> t' ->bp reduce_all_redex t.
Proof with auto.
  move => t; elim/reduce_all_redex_ind: {t}_.
  - by move => t n ? t' H; inversion H; subst.
  - move => _ t1 t2 _ ? ? t' H; inversion H; subst.
    - inversion H2; subst; constructor...
    - apply subst_parred...
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
  move => P t n d; elim: t n => /=.
  - by move => t n c H; elimif_omega; rewrite subnDr.
  - move => tl IHtl tr IHtr n c H; case; auto.
  - move => t IH n c; rewrite -addSn -ltnS; auto.
Qed.

Lemma substitution_preserves_forallfv :
  forall P t1 t2 n m,
  forallfv' P t1 (n + m).+1 -> forallfv' P t2 n ->
  forallfv' P (substitute m t2 t1) (n + m).
Proof.
  move => P; elim => /=.
  - move => t1 t2 n m; elimif_omega.
    - by rewrite -subn1 -subnDA add1n.
    - move => _; exact: shift_preserves_forallfv.
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
    apply substitution_preserves_forallfv.
  - move => /= t1 t1' t2 H H0 n; case => H1 H2; split => //; exact: H0.
  - move => /= t1 t2 t2' H H0 n; case => H1 h2; split => //; exact: H0.
  - move => /= t t' _ H n; apply H.
Qed.

Module STLC.

Inductive typ := tyvar of nat | tyfun of typ & typ.

Inductive typing : context typ -> term -> typ -> Prop :=
  | typvar : forall ctx n ty, ctxindex ctx n ty -> typing ctx (var n) ty
  | typapp : forall ctx t1 t2 ty1 ty2,
    typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
    typing ctx (app t1 t2) ty2
  | typabs : forall ctx t ty1 ty2,
    typing (Some ty1 :: ctx) t ty2 -> typing ctx (abs t) (tyfun ty1 ty2).

Lemma typvar_seqindex :
  forall ctx n ty, typing ctx (var n) ty <-> ctxindex ctx n ty.
Proof.
  move => ctx n ty; split => H.
  by inversion H.
  by constructor.
Qed.

Lemma ctxleq_preserves_typing :
  forall ctx1 ctx2 t ty,
  ctxleq ctx1 ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  move => ctx1 ctx2 t ty H H0; move: ctx1 t ty H0 ctx2 H.
  refine (typing_ind _ _ _ _).
  - move => ctx2 n ty H ctx1 H0.
    constructor; auto.
  - move => ctx2 tl tr tyl tyr H H0 H1 H2 ctx1 H3.
    apply typapp with tyl; auto.
  - move => ctx2 t tyl tyr H H0 ctx1 H1.
    constructor; apply H0; case => //.
Qed.

Lemma subject_shift :
  forall t ty c ctx1 ctx2,
  typing ctx1 t ty -> typing (ctxinsert ctx2 ctx1 c) (shift (size ctx2) c t) ty.
Proof.
  move => t ty c ctx1 ctx2 H; move: ctx1 t ty H c ctx2.
  refine (typing_ind _ _ _ _).
  - move => /= ctx1 n ty H c ctx2.
    case: ifP => ?; rewrite typvar_seqindex H ctxnth_ctxinsert; elimif_omega.
  - move => /= ctx t1 t2 ty1 ty2 H H0 H1 H2 c ctx2.
    apply typapp with ty1; auto.
  - move => /= ctx1 t ty1 ty2 H H0 c ctx2.
    constructor; apply (H0 c.+1).
Qed.

Lemma subject_substitute_seq :
  forall t ty n ctx ctx',
  Forall (fun p => typing (drop n ctx) p.1 p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (substitute_seq n [seq p.1 | p <- ctx'] t) ty.
Proof.
  elim.
  - move => /= m ty n ctx ctx'.
    rewrite typvar_seqindex ctxnth_ctxinsert.
    case: ifP.
    - move/negbF; rewrite -leqNgt => H; rewrite H typvar_seqindex //.
    - move/negbT; rewrite -leqNgt => H; rewrite H.
      rewrite -{1 3}(subnKC H) ltn_add2l addnC.
      move: (m - n) => {m H}.
      elim: ctx' => //=.
      - by move => m _; rewrite subn0; constructor.
      - move => c' ctx' IH; case => //=.
        - case => H _; case => H0; subst.
          move: (subject_shift 0 (ctxinsert [::] (take n ctx) n) H).
          rewrite /= size_ctxinsert add0n size_take minnC minKn.
          apply ctxleq_preserves_typing.
          (* FIXME *)
          elim: ctx n {H IH} => [| c ctx IH].
          - elim => // n H; case => //.
          - case => // n; case => //=; apply IH.
        - move => m; case => H.
          rewrite ltnS addSn subSS.
          apply IH.
  - move => tl IHtl tr IHtr ty n ctx ctx' H H0.
    inversion H0; subst => {H0}.
    apply typapp with ty1; auto.
  - move => /= t IH ty n ctx ctx' H H0.
    inversion H0; subst => {H0}.
    constructor; auto.
Qed.

Lemma subject_reduction1 :
  forall ctx t1 t2 ty, t1 ->1b t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => ctx t1 t2 ty H; move: t1 t2 H ctx ty.
  refine (betared1_ind _ _ _ _ _) => //=.
  - move => t1 t2 ctx ty H.
    inversion H; subst; inversion H3; subst.
    rewrite -(substitute_seq_nil_eq 1 t1) substitute_seq_cons_eq.
    apply (subject_substitute_seq 0 ctx [:: (t2, ty1)]) => //.
    by rewrite /= drop0.
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

Notation SNorm t := (Acc (fun x y => betared1 y x) t).

Lemma snorm_appl : forall tl tr, SNorm (app tl tr) -> SNorm tl.
Proof.
  move => tl tr; move: tl.
  fix IH 2 => tl; case => H; constructor => tl' H0.
  by apply IH, H; constructor.
Qed.

Fixpoint reducible' (ctx : context typ) (t : term) (ty : typ) : Prop :=
  match ty with
    | tyvar n => SNorm t
    | tyfun ty1 ty2 => forall t1 ctx',
        ctxleq ctx ctx' -> typing ctx' t1 ty1 /\ reducible' ctx' t1 ty1 ->
        reducible' ctx' (app t t1) ty2
  end.

Notation reducible ctx t ty := (typing ctx t ty /\ reducible' ctx t ty).

Definition neutral t := (if t is abs _ then False else True).

Lemma ctxleq_preserves_reducibility :
  forall ctx ctx' t ty,
  ctxleq ctx ctx' -> reducible ctx t ty -> reducible ctx' t ty.
Proof.
  move => ctx ctx' tl ty H; case => H0 H1; split.
  - by apply ctxleq_preserves_typing with ctx.
  - case: ty H H0 H1 => //= tyl tyr H H0 H1 tr ctx'' H2.
    apply H1; auto.
Qed.

Lemma CR2' :
  forall ctx t t' ty, t ->1b t' -> reducible ctx t ty -> reducible ctx t' ty.
Proof.
  move => ctx t t' ty H; case => H0 H1; split.
  - by apply subject_reduction1 with t.
  - elim: ty ctx t t' H H1 {H0}.
    - move => /= n ctx t1 t2 H; case => H0; exact: H0.
    - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 ctx' H1 H2.
      apply IHtyr with (app t1 t3).
      - by constructor.
      - exact: H0.
Qed.

Lemma CR2 :
  forall ctx t t' ty, t ->b t' -> reducible ctx t ty -> reducible ctx t' ty.
Proof.
  move => ctx t t' ty; move: t t'.
  apply (rtc_preservation (fun t => reducible ctx t ty)) => t t'.
  apply CR2'.
Qed.

Lemma CR1_and_CR3 :
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
      have H1: typing (ctx ++ [:: Some tyl]) (var (size ctx)) tyl
        by rewrite typvar_seqindex ctxnth_drop' (drop_size_cat [:: Some tyl]).
      have H2: typing (ctx ++ [:: Some tyl]) (app t (var (size ctx))) tyr
        by apply typapp with tyl => //; move: H;
          apply ctxleq_preserves_typing, ctxleq_appr.
      apply snorm_appl with (var (size ctx)).
      apply IHtyr1 with (ctx ++ [:: Some tyl]).
      apply IHtyr2 => // t' H3.
      apply CR2' with (app t (var (size ctx))) => //.
      split => //.
      apply H0.
      - apply ctxleq_appr.
      - apply IHtyl2 => // x H4; inversion H4.
    - move => H H0 H1 /=; split => // tr ctx' H2 H3.
      have H4: SNorm tr by apply IHtyl1 with ctx'.
      move: tr H4 H2 H3; refine (Acc_ind _ _) => tr _ IH H2 H3.
      have H4: typing ctx' (app t tr) tyr.
        apply typapp with tyl.
        - by apply ctxleq_preserves_typing with ctx.
        - tauto.
      apply IHtyr2 => // tr' H5.
      move: H0; inversion H5; subst => // _; split.
      - by apply subject_reduction1 with (app t tr).
      - case: (H1 t1' H8); auto.
      - by apply subject_reduction1 with (app t tr).
      - by apply IH => //; apply CR2' with tr.
Qed.

Lemma CR1 : forall ctx t ty, reducible ctx t ty -> SNorm t.
Proof.
  move => ctx t ty; case: (CR1_and_CR3 ty); firstorder.
Qed.

Lemma CR3 :
  forall ctx t ty, typing ctx t ty -> neutral t ->
  (forall t', t ->1b t' -> reducible ctx t' ty) -> reducible ctx t ty.
Proof.
  move => ctx t ty; case: (CR1_and_CR3 ty); firstorder.
Qed.

Lemma snorm_subst :
  forall t1 t2, SNorm (substitute 0 t2 t1) -> SNorm t1.
Proof.
  move => t1 t2.
  move: (erefl (substitute 0 t2 t1)).
  move: {1 3}(substitute 0 t2 t1) => t3 H H0.
  move: t3 H0 t1 t2 H.
  refine (Acc_ind _ _) => t3 _ IH t1 t2 H; constructor => t3' H0.
  refine (IH (substitute 0 t2 t3') _ t3' t2 _) => // {IH}.
  by subst; apply subst_betared1.
Qed.

Lemma apply_lemma :
  forall ctx tl tr tyl tyr,
  reducible ctx tl (tyfun tyl tyr) ->
  reducible ctx tr tyl -> reducible ctx (app tl tr) tyr.
Proof.
  move => /= ctx tl tr tyl tyr; case => H H0; case => H1 H2; split; auto.
  by apply typapp with tyl.
Qed.

Lemma abstraction_lemma :
  forall ctx t1 tyl tyr,
  typing ctx (abs t1) (tyfun tyl tyr) ->
  (forall t2 ctx', ctxleq ctx ctx' ->
   reducible ctx' t2 tyl -> reducible ctx' (substitute 0 t2 t1) tyr) ->
  reducible ctx (abs t1) (tyfun tyl tyr).
Proof.
  move => ctx t1 tyl tyr H H0; split => //= t2 ctx' H1 H2.
  suff: (reducible ctx' (app (abs t1) t2) tyr) by tauto.
  move: (snorm_subst t1 t2 (CR1 (H0 t2 ctx' H1 H2))) (CR1 H2) => H3 H4.
  move: t1 H3 t2 H4 H H0 H1 H2.
  refine (Acc_ind _ _) => t1 H H0; refine (Acc_ind _ _) => t2 H1 H2 H3 H4 H5 H6.
  apply CR3 => //.
  - apply typapp with tyl.
    - by apply ctxleq_preserves_typing with ctx.
    - tauto.
  - move => t3 H7.
    inversion H7; subst => {H7}; auto.
    - inversion H11; subst => {H11}.
      apply H0 => //.
      - by apply subject_reduction1 with (abs t1) => //; constructor.
      - move => t'' ctx'' H7 H9.
        apply CR2' with (substitute 0 t'' t1); auto.
        exact: subst_betared1.
    - by apply H2 => //; apply CR2' with t2.
Qed.

Lemma reduce_lemma :
  forall ctx (ctx' : seq (term * typ)) t ty,
  typing ([seq Some p.2 | p <- ctx'] ++ ctx) t ty ->
  Forall (fun p => reducible ctx p.1 p.2) ctx' ->
  reducible ctx (substitute_seq 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  move => ctx ctx' t ty; elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx'.
    rewrite typvar_seqindex subn0.
    elim: ctx' n => [| c' ctx' IH].
    - move => /= n H _; rewrite addn0.
      apply CR3 => //.
      - by constructor.
      - move => t' H0; inversion H0.
    - case => /=.
      - by case => H; case => H0 H1; rewrite shiftzero H.
      - by move => n H; case => H0 H1; apply IH.
  - move => tl IHtl tr IHtr ty ctx ctx' H H0.
    inversion H; subst => {H}.
    move: (IHtl (tyfun ty1 ty) ctx ctx'); case => //= H1 H2; split; auto.
    apply typapp with ty1 => //.
    apply subject_substitute_seq => //.
    by rewrite drop0; move: H0; apply Forall_impl => p; case.
  - move => t IHt ty ctx ctx' H H0.
    inversion H; subst => {H} /=.
    apply abstraction_lemma.
    - constructor.
      apply subject_substitute_seq => //.
      by rewrite /= drop0; move: H0; apply Forall_impl => p; case.
    - move => t2 ctx2 H H1.
      rewrite substitute_seq_cons_eq.
      apply (IHt ty2 ctx2 ((t2, ty1) :: ctx')) => /=.
      - move: H3; apply ctxleq_preserves_typing.
        move: H; apply (ctxleq_appl (Some ty1 :: _)).
      - split => //.
        move: H0; apply Forall_impl => p.
        exact: ctxleq_preserves_reducibility.
Qed.

Theorem typed_term_is_snorm : forall ctx t ty, typing ctx t ty -> SNorm t.
Proof.
  move => ctx t ty H.
  apply (@CR1 ctx t ty).
  move: (@reduce_lemma ctx [::] t ty H) => /=.
  rewrite substitute_seq_nil_eq; exact.
Qed.

End STLC.
