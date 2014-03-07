Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.Relations_ext LCAC.lib.ssrnat_ext LCAC.lib.seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive typ := tyvar of nat | tyfun of typ & typ.
Inductive term := var of nat | app of term & term & typ | abs of term.

Coercion tyvar : nat >-> typ.
Coercion var : nat >-> term.

Notation "ty :->: ty'" := (tyfun ty ty') (at level 70, no associativity).
Notation "t @{ t' \: ty }" := (app t t' ty) (at level 60, no associativity).

Fixpoint eqtyp t1 t2 :=
  match t1, t2 with
    | tyvar n, tyvar m => n == m
    | t1l :->: t1r, t2l :->: t2r => eqtyp t1l t2l && eqtyp t1r t2r
    | _, _ => false
  end.

Lemma eqtypP : Equality.axiom eqtyp.
Proof.
  move => t1 t2; apply: (iffP idP) => [| <-].
  - by elim: t1 t2 => [n | t1l IHt1l t1r IHt1r]
      [// m /eqP -> | //= t2l t2r /andP [] /IHt1l -> /IHt1r ->].
  - by elim: t1 => //= t1l ->.
Defined.

Canonical typ_eqMixin := EqMixin eqtypP.
Canonical typ_eqType := Eval hnf in EqType typ typ_eqMixin.

Fixpoint eqterm t1 t2 :=
  match t1, t2 with
    | var n, var m => n == m
    | t1l @{t1r \: ty1}, t2l @{t2r \: ty2} =>
      [&& eqterm t1l t2l, eqterm t1r t2r & (ty1 == ty2)]
    | abs t1, abs t2 => eqterm t1 t2
    | _, _ => false
  end.

Lemma eqtermP : Equality.axiom eqterm.
Proof.
  move => t1 t2; apply: (iffP idP) => [| <-].
  - by elim: t1 t2 => [n | t1l IHt1l t1r IHt1r ty1 | t1 IHt1]
      [// m /eqP -> |
       //= t2l t2r ty2 /and3P [] /IHt1l -> /IHt1r -> /eqP -> | // t2 /IHt1 ->].
  - by elim: t1 => //= t1l -> t1r -> /=.
Defined.

Canonical term_eqMixin := EqMixin eqtermP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Fixpoint shift d c t : term :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | t1 @{t2 \: ty} => shift d c t1 @{shift d c t2 \: ty}
    | abs t1 => abs (shift d c.+1 t1)
  end.

Notation substitutev ts m n :=
  (shift n 0 (nth (var (m - n - size ts)) ts (m - n))) (only parsing).

Fixpoint substitute n ts t : term :=
  match t with
    | var m => if n <= m then substitutev ts m n else m
    | t1 @{t2 \: ty} => substitute n ts t1 @{substitute n ts t2 \: ty}
    | abs t' => abs (substitute n.+1 ts t')
  end.

Reserved Notation "t ->b1 t'" (at level 70, no associativity).

Inductive betared1 : relation term :=
  | betared1beta t1 t2 ty : abs t1 @{t2 \: ty} ->b1 substitute 0 [:: t2] t1
  | betared1appl t1 t1' t2 ty :
      t1 ->b1 t1' -> t1 @{t2 \: ty} ->b1 t1' @{t2 \: ty}
  | betared1appr t1 t2 t2' ty :
      t2 ->b1 t2' -> t1 @{t2 \: ty} ->b1 t1 @{t2' \: ty}
  | betared1abs t t' : t ->b1 t' -> abs t ->b1 abs t'
  where "t ->b1 t'" := (betared1 t t').

Notation betared := [* betared1].
Infix "->b" := betared (at level 70, no associativity).

Hint Constructors betared1.

Fixpoint typing (ctx : context typ) (t : term) (ty : typ) : bool :=
  match t, ty with
    | var n, _ => ctxindex ctx n ty
    | tl @{tr \: ty'}, _ => typing ctx tl (ty' :->: ty) && typing ctx tr ty'
    | abs t, tyl :->: tyr => typing (Some tyl :: ctx) t tyr
    | _, _ => false
  end.

Ltac congruence' := move => /=; try (move: addSn addnS; congruence).

Lemma shiftzero n t : shift 0 n t = t.
Proof. by elim: t n; congruence' => m n; rewrite addn0 if_same. Qed.

Lemma shift_add d d' c c' t :
  c <= c' <= c + d -> shift d' c' (shift d c t) = shift (d' + d) c t.
Proof. case/andP; do 2 elimleq; elim: t c; congruence' => *; elimif_omega. Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof. elimleq; elim: t c'; congruence' => *; elimif_omega. Qed.

Lemma shift_subst_distr n d c ts t :
  c <= n -> shift d c (substitute n ts t) = substitute (d + n) ts (shift d c t).
Proof.
  elimleq; elim: t c => /=; congruence' => v c;
    elimif_omega; rewrite shift_add; elimif_omega.
Qed.

Lemma subst_shift_distr n d c ts t :
  n <= c ->
  shift d c (substitute n ts t) =
  substitute n (map (shift d (c - n)) ts) (shift d (size ts + c) t).
Proof.
  elimleq; elim: t n; congruence' => v n; elimif_omega.
  - rewrite !nth_default ?size_map /=; elimif_omega.
  - rewrite -shift_shift_distr // nth_map' /=;
      f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_shift_cancel n d c ts t :
  c <= n -> size ts + n <= d + c ->
  substitute n ts (shift d c t) = shift (d - size ts) c t.
Proof.
  do 2 elimleq; elim: t c; congruence' => v c;
    elimif_omega; rewrite nth_default /=; elimif_omega.
Qed.

Lemma subst_subst_distr n m xs ys t :
  m <= n ->
  substitute n xs (substitute m ys t) =
  substitute m (map (substitute (n - m) xs) ys) (substitute (size ys + n) xs t).
Proof.
  elimleq; elim: t m; congruence' => v m /=; elimif_omega.
  - rewrite (@subst_shift_cancel m) // size_map 1?nth_default /=; elimif_omega.
  - rewrite size_map -shift_subst_distr // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_app n xs ys t :
  substitute n xs (substitute (size xs + n) ys t) = substitute n (xs ++ ys) t.
Proof.
  elim: t n; congruence' => v n; rewrite nth_cat size_cat;
    elimif_omega; rewrite subst_shift_cancel; elimif_omega.
Qed.

Lemma subst_nil n t : substitute n [::] t = t.
Proof. elim: t n; congruence' => v n; rewrite nth_nil /=; elimif_omega. Qed.

Lemma subst_betared1 n ts t t' :
  t ->b1 t' -> substitute n ts t ->b1 substitute n ts t'.
Proof.
  move => H; move: t t' H n.
  refine (betared1_ind _ _ _ _) => /=; auto => t t' ty n.
  by rewrite subst_subst_distr //= add1n subn0.
Qed.

Module subject_reduction_proof.

Lemma ctxleq_preserves_typing ctx1 ctx2 t ty :
  ctx1 <=c ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  elim: t ty ctx1 ctx2 => [n | tl IHtl tr IHtr tty | t IHt []] //=.
  - by move => ty ctx1 ctx2 /ctxleqP; apply.
  - by move => ty ctx1 ctx2 H /andP [] /IHtl -> //=; apply IHtr.
  - by move => tyl tyr ctx1 ctx2 H; apply IHt; rewrite ctxleqss eqxx.
Qed.

Lemma subject_shift t ty c ctx1 ctx2 :
  typing ctx1 t ty -> typing (ctxinsert ctx2 ctx1 c) (shift (size ctx2) c t) ty.
Proof.
  elim: t ty c ctx1 => [n | tl IHtl tr IHtr tty | t IHt []] //=.
  - by move => ty c ctx1 /eqP ->; apply/eqP; rewrite nth_insert; elimif_omega.
  - by move => ty c ctx1 /andP [] /IHtl -> /=; apply IHtr.
  - by move => tyl tyr c ctx1; apply (IHt tyr c.+1 (Some tyl :: ctx1)).
Qed.

Lemma subject_subst t ty n ctx ctx' :
  all (fun p => typing (drop n ctx) p.1 p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (substitute n [seq p.1 | p <- ctx'] t) ty.
Proof.
  elim: t ty n ctx => [m | tl IHtl tr IHtr tty | t IHt []] //=.
  - move => ty n ctx; rewrite nth_insert !size_map; elimif_omega.
    + by move => _ H; rewrite nth_default ?size_map ?leq_addr //= addnC.
    + move => H0; rewrite !(nth_map (var 0, tyvar 0)) // => /eqP [] ->.
      move: {H0} (all_nthP (var 0, tyvar 0) H0 m H).
      move/(subject_shift 0 (ctxinsert [::] (take n ctx) n)).
      rewrite size_insert /= add0n size_take minnC minKn /insert take0
              sub0n take_minn minnn size_take minnE subKn ?leq_subr //=
              drop_take_nil drop0 cats0 -catA -{4}(cat_take_drop n ctx).
      apply ctxleq_preserves_typing; rewrite ctxleq_appl.
      by case: (leqP' n (size ctx)) =>
        //= /ltnW /drop_oversize ->; rewrite cats0 ctxleql0 size_nseq.
  - by move => ty n ctx H /andP [] /IHtl -> //=; apply IHtr.
  - by move => tyl tyr n ctx H; apply (IHt tyr n.+1 (Some tyl :: ctx)).
Qed.

Lemma subject_subst0 t ty ctx ctx' :
  all (fun p => typing ctx p.1 p.2) ctx' ->
  typing ([seq Some p.2 | p <- ctx'] ++ ctx) t ty ->
  typing ctx (substitute 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  by move: (@subject_subst t ty 0 ctx ctx'); rewrite /insert take0 sub0n drop0.
Qed.

Arguments subject_subst [t ty n ctx] _ _ _.
Arguments subject_subst0 [t ty ctx] _ _ _.

Theorem subject_reduction ctx t1 t2 ty :
  t1 ->b1 t2 -> typing ctx t1 ty -> typing ctx t2 ty.
Proof.
  move => H; move: t1 t2 H ctx ty; refine (betared1_ind _ _ _ _) => /=
    [t1 t2 tty ctx ty /andP [] H H0 |
     t1 t1' t2 tty _ IH ctx ty /andP [] /IH -> |
     t1 t2 t2' tty _ IH ctx ty /andP [] -> /IH |
     t t' _ IH ctx [] //= t0 t1 /IH] //=.
  by apply (subject_subst0 [:: (t2, tty)]) => //=; rewrite H0.
Qed.

Hint Resolve ctxleq_preserves_typing subject_subst subject_reduction.

End subject_reduction_proof.

Module strong_normalization_proof.

Import subject_reduction_proof.

Definition SNorm (t : term) : Prop := Acc (fun x y => betared1 y x) t.

Fixpoint reducible (ctx : context typ) (t : term) (ty : typ) : Prop :=
  match ty with
    | tyvar n => SNorm t
    | ty1 :->: ty2 => forall t1 ctx',
        ctx <=c ctx' -> typing ctx' t1 ty1 -> reducible ctx' t1 ty1 ->
        reducible ctx' (t @{t1 \: ty1}) ty2
  end.

Definition neutral t := if t is abs _ then false else true.

Lemma ctxleq_preserves_reducibility ctx ctx' t ty :
  ctx <=c ctx' -> reducible ctx t ty -> reducible ctx' t ty.
Proof.
  case: ty => //= tyl tyr H H0 t1 ctx'' H1.
  apply H0; move: H H1; apply ctxleq_trans.
Qed.

Lemma CR2 ctx t t' ty :
  t ->b1 t' -> reducible ctx t ty -> reducible ctx t' ty.
Proof.
  elim: ty ctx t t'.
  - by move => /= _ _ t t' H []; apply.
  - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 ctx' H1 H2 H3.
    by apply IHtyr with (t1 @{t3 \: tyl}); auto.
Qed.

Hint Resolve ctxleq_preserves_reducibility CR2.

Lemma CR1_and_CR3 ty :
  (forall ctx t, typing ctx t ty -> reducible ctx t ty -> SNorm t) /\
  (forall ctx t, typing ctx t ty -> neutral t ->
   (forall t', t ->b1 t' -> reducible ctx t' ty) -> reducible ctx t ty).
Proof.
  elim: ty; first by [].
  move => /= tyl [IHtyl1 IHtyl2] tyr [IHtyr1 IHtyr2].
  split => [ctx t H H0 | ctx tl H H0 H1 tr ctx' H2 H3 H4].
  - have H1: ctxindex (ctx ++ [:: Some tyl]) (size ctx) tyl
      by rewrite nth_cat ltnn subnn.
    have H2: typing (ctx ++ [:: Some tyl]) (t @{size ctx \: tyl}) tyr
      by rewrite /= H1 andbT; eauto.
    suff : SNorm ((fun t => t @{size ctx \: tyl}) t) by
      rewrite -/((fun t => t @{size ctx \: tyl}) t);
        apply acc_preservation => x y H3; constructor.
    apply (IHtyr1 _ _ H2), IHtyr2 => // t' H3.
    apply (CR2 H3), H0; auto.
    apply IHtyl2 => // x H4; inversion H4.
  - have H5: SNorm tr by apply IHtyl1 with ctx'.
    move: tr H5 H2 H3 H4; refine (Acc_ind _ _) => tr _ IH H2 H3 H4.
    have H5: typing ctx' (tl @{tr \: tyl}) tyr by rewrite /= H3 andbT; eauto.
    apply IHtyr2 => // t' H6.
    move: H0; inversion H6; subst => // _; eauto.
Qed.

Lemma CR1 ctx t ty : typing ctx t ty -> reducible ctx t ty -> SNorm t.
Proof. case: (CR1_and_CR3 ty) => H _; apply H. Qed.

Lemma CR3 ctx t ty :
  typing ctx t ty -> neutral t ->
  (forall t', t ->b1 t' -> reducible ctx t' ty) -> reducible ctx t ty.
Proof. case: (CR1_and_CR3 ty) => _; apply. Qed.

Lemma abstraction_lemma ctx t1 tyl tyr :
  typing ctx (abs t1) (tyl :->: tyr) ->
  (forall t2 ctx', ctx <=c ctx' -> typing ctx' t2 tyl ->
   reducible ctx' t2 tyl -> reducible ctx' (substitute 0 [:: t2] t1) tyr) ->
  reducible ctx (abs t1) (tyl :->: tyr).
Proof.
  move => /= H H0 t2 ctx' H1 H2 H3.
  have H4: typing ctx' (substitute 0 [:: t2] t1) tyr
    by apply (subject_subst0 [:: (t2, tyl)]); rewrite /= ?H2 //;
      move: H; apply ctxleq_preserves_typing; rewrite ctxleqss eqxx.
  have H5: SNorm t1 by
    move: (CR1 H4 (H0 t2 ctx' H1 H2 H3));
      apply acc_preservation => x y; apply subst_betared1.
  move: (CR1 H2 H3) => H6; move: t1 H5 t2 H6 H H0 H1 H2 H3 {H4}.
  refine (Acc_ind _ _) => t1 H H0.
  refine (Acc_ind _ _) => t2 H1 H2 H3 H4 H5 H6 H7.
  apply CR3 => //=.
  - by rewrite H6 andbT; move: H3;
      apply ctxleq_preserves_typing; rewrite ctxleqss eqxx.
  - move => t3 H8.
    inversion H8; subst => {H8}; eauto.
    inversion H13; subst => {H13}.
    apply H0 => //; eauto => t'' ctx'' H8 H10 H11.
    by apply (CR2 (subst_betared1 0 [:: t''] H9)), H4.
Qed.

Lemma reduce_lemma ctx (ctx' : seq (term * typ)) t ty :
  typing ([seq Some p.2 | p <- ctx'] ++ ctx) t ty ->
  all (fun p => typing ctx p.1 p.2) ctx' ->
  Forall (fun p => reducible ctx p.1 p.2) ctx' ->
  reducible ctx (substitute 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx'.
    rewrite subn0 size_map shiftzero.
    elim: ctx' n => [| c' ctx' IH []] /=.
    + move => n H _ _; rewrite nth_nil subn0.
      apply CR3 => //; auto => t' H0; inversion H0.
    + case/eqP => ->; tauto.
    + by move => n H /andP [_ H0] [_]; apply IH.
  - move => tl IHtl tr IHtr tty ty ctx ctx' /= /andP [] H H0 H1 H2.
    move: (IHtl (tty :->: ty) ctx ctx') => /=; apply; auto.
    by apply subject_subst0.
  - move => t IHt [] //= tyl tyr ctx ctx' H H0 H1.
    apply abstraction_lemma.
    + rewrite -/(substitute 0 _ (abs t)).
      by apply subject_subst0.
    + move => t2 ctx2 H2 H3 H4.
      rewrite subst_app /=.
      apply (IHt tyr ctx2 ((t2, tyl) :: ctx')) => /=.
      * move: H; apply ctxleq_preserves_typing.
        by rewrite ctxleqss eqxx ctxleq_appl /=.
      * rewrite H3 /=; move: H0; apply sub_all => p; eauto.
      * split => //; move: H1; apply Forall_impl; eauto.
Qed.

Theorem typed_term_is_snorm ctx t ty : typing ctx t ty -> SNorm t.
Proof.
  move => H; move/(@reduce_lemma ctx [::]): (H) => /= /(_ erefl I).
  by rewrite subst_nil; apply CR1.
Qed.

End strong_normalization_proof.
