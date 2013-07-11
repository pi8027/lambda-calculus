Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.ssrnat_ext LCAC.lib.seq_ext LCAC.LC.Debruijn.Untyped.

Import Lambda_tactics.

Set Implicit Arguments.

Inductive typ := tyvar of nat | tyfun of typ & typ.

Coercion tyvar : nat >-> typ.

Inductive typing : context typ -> term -> typ -> Prop :=
  | typvar ctx n ty : ctxindex ctx n ty -> typing ctx n ty
  | typapp ctx t1 t2 ty1 ty2 :
    typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
    typing ctx (app t1 t2) ty2
  | typabs ctx t ty1 ty2 :
    typing (Some ty1 :: ctx) t ty2 -> typing ctx (abs t) (tyfun ty1 ty2).

Hint Constructors typing.

Lemma typvar_seqindex ctx n ty : typing ctx (var n) ty <-> ctxindex ctx n ty.
Proof.
  split => H.
  - by inversion H.
  - by constructor.
Qed.

Module subject_reduction_proof.

Lemma ctxleq_preserves_typing ctx1 ctx2 t ty :
  ctx1 <=c ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  move => H H0; move: ctx1 t ty H0 ctx2 H.
  refine (typing_ind _ _ _ _); eauto => ctx2 t tyl tyr H H0 ctx1 H1.
  by constructor; apply H0; case.
Qed.

Lemma subject_shift t ty c ctx1 ctx2 :
  typing ctx1 t ty -> typing (ctxinsert ctx2 ctx1 c) (shift (size ctx2) c t) ty.
Proof.
  move => H; move: ctx1 t ty H c ctx2.
  refine (typing_ind _ _ _ _) => /=.
  - move => ctx1 n ty H c ctx2.
    rewrite typvar_seqindex H nth_ctxinsert; elimif_omega.
  - eauto.
  - move => ctx1 t ty1 ty2 H H0 c ctx2.
    constructor; apply (H0 c.+1).
Qed.

Lemma subject_subst t ty n ctx ctx' :
  Forall (fun p => typing (drop n ctx) p.1 p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (substitute n [seq p.1 | p <- ctx'] t) ty.
Proof with auto.
  elim: t ty n ctx.
  - move => /= m ty n ctx.
    rewrite /substitutev typvar_seqindex nth_ctxinsert !size_map.
    elimif_omega.
    - by constructor.
    - move: H H0 {H1}; elimleq; rewrite ltn_add2l => H.
      rewrite !(nth_map (var 0, tyvar 0)) // => H0 [H1]; subst.
      case: {ctx' H H0} (nth _ _ _) (Forall_nth _ (var 0, tyvar 0) ctx' m H H0)
        => /= t ty.
      move/(subject_shift 0 (ctxinsert [::] (take n ctx) n)).
      rewrite size_ctxinsert add0n size_take minnC minKn.
      apply ctxleq_preserves_typing => {m t ty} m ty ->.
      rewrite !nth_ctxinsert size_ctxinsert /=
        size_take minnC minKn nth_nil !add0n addn0 !subn0.
      elimif; rewrite ?nth_take ?nth_drop //; f_equal; ssromega.
    - move => H2 H3; rewrite nth_default /=.
      - rewrite typvar_seqindex H3; f_equal; ssromega.
      - rewrite size_map; ssromega.
  - move => tl IHtl tr IHtr ty n ctx H H0.
    inversion H0; subst => /= {H0}; apply typapp with ty1...
  - move => /= t IH ty n ctx H H0.
    inversion H0; subst => {H0}...
Qed.

Theorem subject_reduction ctx t1 t2 ty :
  t1 ->b1 t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => H; move: t1 t2 H ctx ty.
  refine (betared1_ind _ _ _ _ _) => //=.
  - move => t1 t2 ctx ty H.
    inversion H; subst; inversion H3; subst.
    apply (subject_subst 0 ctx [:: (t2, ty1)]).
    - by rewrite /= drop0.
    - by rewrite /ctxinsert sub0n take0 drop0 /=.
  - move => t1 t1' t2 H IH ctx ty H0; inversion H0; subst; eauto.
  - move => t1 t2 t2' H IH ctx ty H0; inversion H0; subst; eauto.
  - move => t1 t2 H IH ctx ty H0; inversion H0; subst; auto.
Qed.

Hint Resolve ctxleq_preserves_typing subject_subst subject_reduction.

End subject_reduction_proof.

Module strong_normalization_proof.

Import subject_reduction_proof.

Notation SNorm t := (Acc (fun x y => betared1 y x) t).

Lemma snorm_appl tl tr : SNorm (app tl tr) -> SNorm tl.
Proof.
  move: tl.
  fix IH 2 => tl [H]; constructor => tl' H0.
  by apply IH, H; constructor.
Qed.

Fixpoint reducible (ctx : context typ) (t : term) (ty : typ) : Prop :=
  match ty with
    | tyvar n => SNorm t
    | tyfun ty1 ty2 => forall t1 ctx',
        ctx <=c ctx' -> typing ctx' t1 ty1 -> reducible ctx' t1 ty1 ->
        reducible ctx' (app t t1) ty2
  end.

Definition neutral t := (if t is abs _ then False else True).

Lemma ctxleq_preserves_reducibility ctx ctx' t ty :
  ctx <=c ctx' -> reducible ctx t ty -> reducible ctx' t ty.
Proof.
  case: ty => /=; auto.
Qed.

Lemma CR2 ctx t t' ty :
  t ->b1 t' -> reducible ctx t ty -> reducible ctx t' ty.
Proof.
  elim: ty ctx t t'.
  - by move => /= _ _ t t' H []; apply.
  - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 ctx' H1 H2 H3.
    by apply IHtyr with (app t1 t3); auto; constructor.
Qed.

Arguments CR2 [ctx t t' ty] _ _.

Hint Resolve ctxleq_preserves_reducibility CR2.

Lemma CR1_and_CR3 ty :
  (forall ctx t, typing ctx t ty -> reducible ctx t ty -> SNorm t) /\
  (forall ctx t, typing ctx t ty -> neutral t ->
   (forall t', t ->b1 t' -> reducible ctx t' ty) -> reducible ctx t ty).
Proof.
  elim: ty.
  - by move: Acc_intro; eauto.
  - move => tyl [IHtyl1 IHtyl2] tyr [IHtyr1 IHtyr2] /=.
    split => [ctx t H H0 | ctx tl H H0 H1 tr ctx' H2 H3 H4].
    - have H1: typing (ctx ++ [:: Some tyl]) (size ctx) tyl
        by rewrite typvar_seqindex nth_cat ltnn subnn.
      have H2: typing (ctx ++ [:: Some tyl]) (app t (size ctx)) tyr by eauto.
      apply snorm_appl with (size ctx), (IHtyr1 _ _ H2), IHtyr2 => // t' H3.
      apply (CR2 H3), H0; auto.
      apply IHtyl2 => // x H4; inversion H4.
    - have H5: SNorm tr by apply IHtyl1 with ctx'.
      move: tr H5 H2 H3 H4; refine (Acc_ind _ _) => tr _ IH H2 H3 H4.
      have H5: typing ctx' (app tl tr) tyr by eauto.
      apply IHtyr2 => // t' H6.
      move: H0; inversion H6; subst => // _; eauto.
Qed.

Lemma CR1 ctx t ty : typing ctx t ty -> reducible ctx t ty -> SNorm t.
Proof.
  case: (CR1_and_CR3 ty); eauto.
Qed.

Lemma CR3 ctx t ty :
  typing ctx t ty -> neutral t ->
  (forall t', t ->b1 t' -> reducible ctx t' ty) -> reducible ctx t ty.
Proof.
  case: (CR1_and_CR3 ty); auto.
Qed.

Lemma snorm_subst n ts t : SNorm (substitute n ts t) -> SNorm t.
Proof.
  move: {1 3}(substitute _ _ _) (erefl (substitute n ts t)) => t3 H H0.
  move: t3 H0 n ts t H.
  refine (Acc_ind _ _) => t3 _ IH n ts t H; subst; constructor => t' H0.
  by apply (IH (substitute n ts t') (subst_betared1 n ts H0) n ts t').
Qed.

Lemma abstraction_lemma ctx t1 tyl tyr :
  typing ctx (abs t1) (tyfun tyl tyr) ->
  (forall t2 ctx', ctx <=c ctx' -> typing ctx' t2 tyl ->
   reducible ctx' t2 tyl -> reducible ctx' (substitute 0 [:: t2] t1) tyr) ->
  reducible ctx (abs t1) (tyfun tyl tyr).
Proof.
  move => /= H H0 t2 ctx' H1 H2 H3.
  have H4: typing ctx' (substitute 0 [:: t2] t1) tyr by eauto.
  move: (snorm_subst 0 [:: t2] t1 (CR1 H4 (H0 t2 ctx' H1 H2 H3)))
    (CR1 H2 H3) => H5 H6.
  move: t1 H5 t2 H6 H H0 H1 H2 H3 {H4}.
  refine (Acc_ind _ _) => t1 H H0.
  refine (Acc_ind _ _) => t2 H1 H2 H3 H4 H5 H6 H7.
  apply CR3 => //; eauto => t3 H8.
  inversion H8; subst => {H8}; eauto.
  inversion H12; subst => {H12}.
  apply H0 => //; eauto => t'' ctx'' H8 H10 H11.
  by apply (CR2 (subst_betared1 0 [:: t''] H9)), H4.
Qed.

Lemma reduce_lemma ctx (ctx' : seq (term * typ)) t ty :
  typing ([seq Some p.2 | p <- ctx'] ++ ctx) t ty ->
  Forall (fun p => typing ctx p.1 p.2 /\ reducible ctx p.1 p.2) ctx' ->
  reducible ctx (substitute 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx'.
    rewrite /substitutev typvar_seqindex subn0 size_map shiftzero.
    elim: ctx' n => [| c' ctx' IH []] /=.
    - move => n H _; rewrite nth_nil subn0.
      apply CR3 => //; auto => t' H0; inversion H0.
    - move => [->]; tauto.
    - by move => n H [_]; apply IH.
  - move => tl IHtl tr IHtr ty ctx ctx' H H0.
    inversion H; subst => {H}.
    move: (IHtl (tyfun ty1 ty) ctx ctx') => /=; apply; auto.
    apply subject_subst.
    - rewrite drop0; move: H0; apply Forall_impl; tauto.
    - by rewrite /ctxinsert sub0n take0 drop0 /=.
  - move => t IHt ty ctx ctx' H H0.
    inversion H; subst => {H} /=.
    apply abstraction_lemma.
    - apply typabs, subject_subst.
      - rewrite /= drop0; move: H0; apply Forall_impl; tauto.
      - by rewrite /ctxinsert /= take0 drop0 /=.
    - move => t2 ctx2 H H1 H2.
      rewrite subst_app.
      apply (IHt ty2 ctx2 ((t2, ty1) :: ctx')) => /=.
      - move: H3; apply ctxleq_preserves_typing.
        move: H; apply (ctxleq_appl (Some ty1 :: _)).
      - split => //; move: H0; apply Forall_impl => p []; eauto.
Qed.

Theorem typed_term_is_snorm ctx t ty : typing ctx t ty -> SNorm t.
Proof.
  move => H.
  apply (@CR1 ctx t ty) => //.
  move: (@reduce_lemma ctx [::] t ty H) => /=.
  by rewrite subst_nil; apply.
Qed.

End strong_normalization_proof.
