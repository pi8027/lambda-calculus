From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LCAC Require Import Relations_ext seq_ext_base ssrnat_ext seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive typ := tyvar of nat | tyfun of typ & typ.
Inductive term := var of nat | app of term & term | abs of typ & term.

Coercion tyvar : nat >-> typ.
Coercion var : nat >-> term.

Notation "ty :->: ty'" := (tyfun ty ty') (at level 50, no associativity).
Notation "t @ t'" := (app t t') (at level 60, no associativity).

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
    | t1l @ t1r, t2l @ t2r => eqterm t1l t2l && eqterm t1r t2r
    | abs ty1 t1, abs ty2 t2 => (ty1 == ty2) && eqterm t1 t2
    | _, _ => false
  end.

Lemma eqtermP : Equality.axiom eqterm.
Proof.
  move => t1 t2; apply: (iffP idP) => [| <-].
  - by elim: t1 t2 => [n | t1l IHt1l t1r IHt1r | ty1 t1 IHt1]
      [// m /eqP -> | //= t2l t2r /andP [] /IHt1l -> /IHt1r -> |
       //= ty2 t2 /andP [] /eqP -> /IHt1 ->].
  - by elim: t1 => //= [t1l -> | ty1 t1 ->] //; rewrite andbT.
Defined.

Canonical term_eqMixin := EqMixin eqtermP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Fixpoint shift d c t : term :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | t1 @ t2 => shift d c t1 @ shift d c t2
    | abs ty t1 => abs ty (shift d c.+1 t1)
  end.

Notation substitutev ts m n :=
  (shift n 0 (nth (var (m - n - size ts)) ts (m - n))) (only parsing).

Fixpoint substitute n ts t : term :=
  match t with
    | var m => if n <= m then substitutev ts m n else m
    | t1 @ t2 => substitute n ts t1 @ substitute n ts t2
    | abs ty t' => abs ty (substitute n.+1 ts t')
  end.

Reserved Notation "t ->b1 t'" (at level 80, no associativity).

Inductive betared1 : relation term :=
  | betared1beta ty t1 t2 : abs ty t1 @ t2 ->b1 substitute 0 [:: t2] t1
  | betared1appl t1 t1' t2 : t1 ->b1 t1' -> t1 @ t2 ->b1 t1' @ t2
  | betared1appr t1 t2 t2' : t2 ->b1 t2' -> t1 @ t2 ->b1 t1 @ t2'
  | betared1abs ty t t' : t ->b1 t' -> abs ty t ->b1 abs ty t'
  where "t ->b1 t'" := (betared1 t t').

Notation betared := [* betared1].
Infix "->b" := betared (at level 80, no associativity).

Hint Constructors betared1.

Fixpoint typing_rec (ctx : context typ) (t : term) : option typ :=
  match t with
    | var n => nth None ctx n
    | tl @ tr =>
      if typing_rec ctx tl is Some (tyl :->: tyr)
        then (if typing_rec ctx tr == Some tyl then Some tyr else None)
        else None
    | abs ty t => omap (tyfun ty) (typing_rec (Some ty :: ctx) t)
  end.

Definition typing := nosimpl typing_rec.

Notation "ctx \|- t \: ty" := (Some ty == typing ctx t)
  (at level 69, no associativity).
Notation "ctx \|- t \: ty" := (Some (ty : typ) == typing ctx t)
  (at level 69, no associativity, only parsing).

Lemma typing_varE ctx (n : nat) ty : ctx \|- n \: ty = ctxindex ctx n ty.
Proof. by rewrite /typing /=. Qed.

Lemma typing_appP ctx t1 t2 ty :
  reflect (exists2 tyl, ctx \|- t1 \: tyl :->: ty & ctx \|- t2 \: tyl)
          (ctx \|- t1 @ t2 \: ty).
Proof.
  apply: (iffP idP); rewrite /typing /=.
  - by move: (typing_rec ctx t1) => [] // [] // tyl tyr;
      case: ifP => // /eqP -> /eqP [] ->; exists tyl.
  - by case => tyl /eqP <- /eqP <-; rewrite eqxx.
Qed.

Lemma typing_absP ctx t tyl ty :
  reflect (exists2 tyr, ty = tyl :->: tyr & Some tyl :: ctx \|- t \: tyr)
          (ctx \|- abs tyl t \: ty).
Proof.
  apply: (iffP idP); rewrite /typing /=.
  - by case: typing_rec => //= tyr /eqP [] ->; exists tyr.
  - by case => tyr ->; case: typing_rec => // tyr' /eqP [] <-.
Qed.

Lemma typing_absE ctx t tyl tyr :
  ctx \|- abs tyl t \: tyl :->: tyr = Some tyl :: ctx \|- t \: tyr.
Proof.
  by rewrite /typing /=; case: typing_rec => //= tyr';
    rewrite /eq_op /= /eq_op /= -/eq_op eqxx.
Qed.

Notation SN := (Acc (fun x y => betared1 y x)).

Definition neutral t := if t is abs _ _ then false else true.

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
  - rewrite -shift_shift_distr // nth_map' /=.
      congr shift; apply nth_equal; rewrite size_map; elimif_omega.
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
  - rewrite size_map -shift_subst_distr // nth_map' /=;
      congr shift; apply nth_equal; rewrite size_map; elimif_omega.
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
  ctx1 <=c ctx2 -> ctx1 \|- t \: ty -> ctx2 \|- t \: ty.
Proof.
  elim: t ty ctx1 ctx2 => /= [n | tl IHtl tr IHtr | tyl t IHt] ty ctx1 ctx2.
  - move/ctxleqP; apply.
  - by move => H /typing_appP [tyl H0 H1]; apply/typing_appP;
      exists tyl; [apply (IHtl _ ctx1) | apply (IHtr _ ctx1)].
  - by move => H /typing_absP [tyr -> H0]; rewrite typing_absE;
      move: H0; apply IHt; rewrite ctxleqE eqxx.
Qed.

Lemma typing_shift t c ctx1 ctx2 :
  typing (ctxinsert ctx2 ctx1 c) (shift (size ctx2) c t) = typing ctx1 t.
Proof.
  rewrite /typing.
  elim: t c ctx1 => /= [n | tl IHtl tr IHtr | tyl t IHt] c ctx1.
  - by rewrite nth_insert; elimif_omega.
  - by rewrite IHtl IHtr.
  - by rewrite -(IHt c.+1).
Qed.

Lemma subject_subst t ty n ctx ctx' :
  all (fun p => drop n ctx \|- p.1 \: p.2) ctx' ->
  ctxinsert [seq Some p.2 | p <- ctx'] ctx n \|- t \: ty ->
  ctx \|- substitute n (unzip1 ctx') t \: ty.
Proof.
  elim: t ty n ctx => /= [m | tl IHtl tr IHtr | tyl t IHt] ty n ctx H.
  - rewrite /typing /= nth_insert !size_map => /eqP ->; elimif.
    + apply/eqP/esym; rewrite nth_default ?size_map /=; elimif_omega.
    + rewrite -/typing !(nth_map (var 0, tyvar 0)) //.
      move: {H H0} (all_nthP (var 0, tyvar 0) H m H0).
      rewrite -(typing_shift _ 0 _ (ctxinsert [::] (take n ctx) n))
              size_insert /= add0n size_take minnC minKn /insert take0
              sub0n take_minn minnn size_take minnE subKn ?leq_subr //=
              drop_take_nil drop0 cats0 -catA -{4}(cat_take_drop n ctx).
      apply ctxleq_preserves_typing; rewrite ctxleq_appl.
      by case: (leqP' n (size ctx)) =>
        //= /ltnW /drop_oversize ->; rewrite cats0;
        apply/ctxleqP => /= n' ty' /eqP; rewrite nth_nseq if_same.
  - by case/typing_appP => tyl H0 H1; apply/typing_appP; exists tyl; auto.
  - by case/typing_absP => tyr -> H0; rewrite typing_absE; apply IHt.
Qed.

Lemma subject_subst0 t ty ctx ctx' :
  all (fun p => ctx \|- p.1 \: p.2) ctx' ->
  [seq Some p.2 | p <- ctx'] ++ ctx \|- t \: ty ->
  ctx \|- substitute 0 (unzip1 ctx') t \: ty.
Proof.
  by move: (@subject_subst t ty 0 ctx ctx'); rewrite /insert take0 sub0n drop0.
Qed.

Arguments subject_subst [t ty n ctx] _ _ _.
Arguments subject_subst0 [t ty ctx] _ _ _.

Theorem subject_reduction ctx t1 t2 ty :
  t1 ->b1 t2 -> ctx \|- t1 \: ty -> ctx \|- t2 \: ty.
Proof.
  move => H; move: t1 t2 H ctx ty; refine (betared1_ind _ _ _ _) => /=.
  - move => ty t1 t2 ctx ty2 /typing_appP [tyl] /typing_absP [tyr [-> ->]] H H0.
    by apply (subject_subst0 [:: (t2, ty)]) => //=; rewrite H0.
  - by move => t1 t1' t2 H H0 ctx ty /typing_appP [tyl H1 H2];
      apply/typing_appP; exists tyl; [apply H0 | apply H2].
  - by move => t1 t2 t2' H H0 ctx ty /typing_appP [tyl H1 H2];
      apply/typing_appP; exists tyl; [apply H1 | apply H0].
  - by move => tyl t t' H H0 ctx ty /typing_absP [tyr -> H1];
      rewrite typing_absE; apply H0.
Qed.

Hint Resolve ctxleq_preserves_typing subject_subst subject_reduction.

End subject_reduction_proof.

(*******************************************************************************
  Strong normalization proof with the type-free version of reducibility
*******************************************************************************)
Module strong_normalization_proof_typefree.

Fixpoint reducible (ty : typ) (t : term) : Prop :=
  match ty with
    | tyvar n => SN t
    | tyl :->: tyr => forall t', reducible tyl t' -> reducible tyr (t @ t')
  end.

Lemma CR2 t t' ty : t ->b1 t' -> reducible ty t -> reducible ty t'.
Proof.
  elim: ty t t' => /= [_ | tyl IHtyl tyr IHtyr] t t' H.
  - by case; apply.
  - by move => H0 t'' H1; apply IHtyr with (t @ t''); auto.
Qed.

Hint Resolve CR2.

Lemma CR1_and_CR3 ty :
  (forall t, reducible ty t -> SN t) /\
  (forall t, neutral t ->
             (forall t', t ->b1 t' -> reducible ty t') -> reducible ty t).
Proof.
  elim: ty; first by [].
  move => /= tyl [IHtyl1 IHtyl2] tyr [IHtyr1 IHtyr2];
    split => [t H | tl H H0 tr H1].
  - suff: SN ([fun t => t @ 0] t) by apply acc_preservation; constructor.
    apply IHtyr1, IHtyr2 => // t' H0.
    apply (CR2 H0), H, IHtyl2 => // t'' H1; inversion H1.
  - move: (IHtyl1 tr H1) => H2.
    move: tr H2 H1; refine (Acc_ind' _) => tr IH H1.
    apply IHtyr2 => // t' H2.
    move: H; inversion H2; subst => // _; eauto.
Qed.

Definition CR1 t ty := proj1 (CR1_and_CR3 ty) t.
Definition CR3 t ty := proj2 (CR1_and_CR3 ty) t.

Lemma abs_reducibility t tyl tyr :
  (forall t', reducible tyl t' -> reducible tyr (substitute 0 [:: t'] t)) ->
  reducible (tyl :->: tyr) (abs tyl t).
Proof.
  move => /= H t' H0.
  have H1: SN t by
    move: (CR1 (H t' H0)); apply acc_preservation => x y; apply subst_betared1.
  move: t t' H1 {H0} (CR1 H0) H (H0); refine (Acc_ind2 _) => t t' IHt IHt' H H0.
  apply CR3 => // t'' H1; inversion H1; subst; eauto; inversion H5; subst.
  by apply IHt; auto => t'' H2; apply (CR2 (subst_betared1 0 [:: t''] H6)), H.
Qed.

Lemma reduce_lemma ctx (ctx' : seq (term * typ)) t ty :
  [seq Some p.2 | p <- ctx'] ++ ctx \|- t \: ty ->
  Forall (fun p => reducible p.2 p.1) ctx' ->
  reducible ty (substitute 0 (unzip1 ctx') t).
Proof.
  elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx'.
    rewrite subn0 size_map shiftzero.
    elim: ctx' n => [| c' ctx' IH []] /=.
    + move => n _ _; rewrite nth_nil subn0.
      apply CR3 => //; auto => t' H0; inversion H0.
    + case/eqP => ->; tauto.
    + by move => n H [_ H0]; apply IH.
  - move => tl IHtl tr IHtr tyr ctx ctx' /typing_appP [tyl H H0] H1.
    by move: (IHtl (tyl :->: tyr) ctx ctx') => /=;
      apply => //; apply IHtr with ctx.
  - move => tyl t IHt ty ctx ctx' /typing_absP [tyr -> H] H0.
    simpl substitute; apply abs_reducibility => t' H1.
    by rewrite subst_app /=; apply (IHt tyr ctx ((t', tyl) :: ctx')).
Qed.

Theorem typed_term_is_sn ctx t ty : ctx \|- t \: ty -> SN t.
Proof.
  by move/(@reduce_lemma ctx [::]) => /= /(_ I); rewrite subst_nil; apply CR1.
Qed.

End strong_normalization_proof_typefree.

(*******************************************************************************
  Strong normalization proof with the Kripke-style reducibility
*******************************************************************************)
Module strong_normalization_proof_kripke.

Import subject_reduction_proof.

Fixpoint reducible (ctx : context typ) (ty : typ) (t : term) : Prop :=
  match ty with
    | tyvar n => SN t
    | tyl :->: tyr => forall t' ctx',
        ctx <=c ctx' -> ctx' \|- t' \: tyl -> reducible ctx' tyl t' ->
        reducible ctx' tyr (t @ t')
  end.

Lemma ctxleq_preserves_reducibility ctx ctx' t ty :
  ctx <=c ctx' -> reducible ctx ty t -> reducible ctx' ty t.
Proof.
  case: ty => //= tyl tyr H H0 t1 ctx'' H1.
  apply H0; move: H H1; apply ctxleq_trans.
Qed.

Lemma CR2 ctx t t' ty :
  t ->b1 t' -> reducible ctx ty t -> reducible ctx ty t'.
Proof.
  elim: ty ctx t t'.
  - by move => /= _ _ t t' H []; apply.
  - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 ctx' H1 H2 H3.
    by apply IHtyr with (t1 @ t3); auto.
Qed.

Hint Resolve ctxleq_preserves_reducibility CR2.

Lemma CR1_and_CR3 ty :
  (forall ctx t, ctx \|- t \: ty -> reducible ctx ty t -> SN t) /\
  (forall ctx t, ctx \|- t \: ty -> neutral t ->
   (forall t', t ->b1 t' -> reducible ctx ty t') -> reducible ctx ty t).
Proof.
  elim: ty; first by [].
  move => /= tyl [IHtyl1 IHtyl2] tyr [IHtyr1 IHtyr2];
    split => [ctx t H H0 | ctx tl H H0 H1 tr ctx' H2 H3 H4].
  - set H1 := ctxindex_last ctx tyl.
    have H2: ctx ++ [:: Some tyl] \|- t @ size ctx \: tyr by
      apply/typing_appP; exists tyl; eauto.
    suff: SN ([fun t => t @ size ctx] t) by
      apply acc_preservation; constructor.
    apply (IHtyr1 _ _ H2), IHtyr2 => // t' H3.
    apply (CR2 H3), H0 => //=.
    apply IHtyl2 => // x H4; inversion H4.
  - have H5: SN tr by apply IHtyl1 with ctx'.
    move: tr H5 H2 H3 H4; refine (Acc_ind' _) => tr IH H2 H3 H4.
    have H5: ctx' \|- tl @ tr \: tyr by apply/typing_appP; exists tyl; eauto.
    apply IHtyr2 => // t' H6.
    move: H0; inversion H6; subst => // _; eauto.
Qed.

Definition CR1 t ty := proj1 (CR1_and_CR3 ty) t.
Definition CR3 t ty := proj2 (CR1_and_CR3 ty) t.

Lemma abs_reducibility ctx t tyl tyr :
  ctx \|- abs tyl t \: tyl :->: tyr ->
  (forall t' ctx', ctx <=c ctx' -> ctx' \|- t' \: tyl ->
   reducible ctx' tyl t' -> reducible ctx' tyr (substitute 0 [:: t'] t)) ->
  reducible ctx (tyl :->: tyr) (abs tyl t).
Proof.
  move => /= H H0 t' ctx' H1 H2 H3.
  have H4: ctx' \|- substitute 0 [:: t'] t \: tyr by
    apply (subject_subst0 [:: (t', tyl)]); rewrite /= ?H2 // -typing_absE;
      move: H; apply ctxleq_preserves_typing.
  have {H4} H4: SN t by
    move: (CR1 H4 (H0 t' ctx' H1 H2 H3));
      apply acc_preservation => x y; apply subst_betared1.
  move: t t' {H2 H3} H4 (CR1 H2 H3) H H0 H1 (H2) (H3);
    refine (Acc_ind2 _) => t t' IHt IHt' H H0 H1 H2 H3; apply CR3 => //.
  - apply/typing_appP; exists tyl; last apply H2.
    by move: H; apply ctxleq_preserves_typing.
  - move => t'' H4.
    inversion H4; subst => {H4}; eauto; inversion H8; subst => {H8}.
    apply IHt => //; eauto => t'' ctx'' H4 H5 H6.
    by apply (CR2 (subst_betared1 0 [:: t''] H7)), H0.
Qed.

Lemma reduce_lemma ctx (ctx' : seq (term * typ)) t ty :
  [seq Some p.2 | p <- ctx'] ++ ctx \|- t \: ty ->
  all (fun p => ctx \|- p.1 \: p.2) ctx' ->
  Forall (fun p => reducible ctx p.2 p.1) ctx' ->
  reducible ctx ty (substitute 0 (unzip1 ctx') t).
Proof.
  elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx'.
    rewrite subn0 size_map shiftzero.
    elim: ctx' n => [| c' ctx' IH []] /=.
    + move => n H _ _; rewrite nth_nil subn0.
      apply CR3 => //; auto => t' H0; inversion H0.
    + case/eqP => ->; tauto.
    + by move => n H /andP [_ H0] [_]; apply IH.
  - move => tl IHtl tr IHtr tyr ctx ctx' /typing_appP [tyl H H0] H1 H2.
    move: (IHtl (tyl :->: tyr) ctx ctx') => /=; apply; auto.
    by apply subject_subst0.
  - move => tyl t IHt ty ctx ctx' /typing_absP [tyr -> H] H0 H1.
    simpl substitute; apply abs_reducibility;
      first by apply (@subject_subst0 (abs tyl t)) => //; rewrite typing_absE.
    move => /= t2 ctx2 H2 H3 H4.
    rewrite subst_app /=.
    apply (IHt tyr ctx2 ((t2, tyl) :: ctx')) => /=.
    + by move: H; rewrite -!typing_absE;
        apply ctxleq_preserves_typing; rewrite ctxleq_appl.
    + rewrite H3 /=; move: H0; apply sub_all => p; eauto.
    + intuition; move: H1; apply Forall_impl; eauto.
Qed.

Theorem typed_term_is_sn ctx t ty : ctx \|- t \: ty -> SN t.
Proof.
  move => H; move: (@reduce_lemma ctx [::] _ _ H) => /= /(_ erefl I).
  by rewrite subst_nil; apply CR1.
Qed.

End strong_normalization_proof_kripke.

(*******************************************************************************
  Strong normalization proof with the typed version of reducibility
*******************************************************************************)
Module strong_normalization_proof_typed.

Import subject_reduction_proof.

Fixpoint list_hyp ty : seq typ :=
  if ty is tyl :->: tyr then tyl :: list_hyp tyl ++ list_hyp tyr else [::].

Fixpoint list_hyp' (ctx : context typ) t : seq typ :=
  oapp list_hyp [::] (typing ctx t) ++
  match t with
    | var n => [::]
    | app tl tr => list_hyp' ctx tl ++ list_hyp' ctx tr
    | abs ty t => list_hyp' (Some ty :: ctx) t
  end.

Lemma list_hyp'E ctx t :
  list_hyp' ctx t =
  oapp list_hyp [::] (typing ctx t) ++
  match t with
    | var n => [::]
    | app tl tr => list_hyp' ctx tl ++ list_hyp' ctx tr
    | abs ty t => list_hyp' (Some ty :: ctx) t
  end.
Proof. by case: t. Qed.

Lemma ctxleq_list_hyp' ctx ctx' t ty :
  ctx <=c ctx' -> ctx \|- t \: ty -> list_hyp' ctx' t = list_hyp' ctx t.
Proof.
  elim: t ty ctx ctx' => //=.
  - move => n ty ctx ctx' H H0.
    by rewrite -(eqP (ctxleq_preserves_typing H H0)) -(eqP H0).
  - move => tl IHtl tr IHtr tyr ctx ctx' H H0.
    rewrite -(eqP (ctxleq_preserves_typing H H0)) -(eqP H0) /=; congr cat.
    case/typing_appP: H0 => tyl H0 H1.
    by rewrite (IHtl (tyl :->: tyr) ctx ctx') // (IHtr tyl ctx ctx').
  - move => tyl t IHt ty ctx ctx' H H0.
    rewrite -(eqP (ctxleq_preserves_typing H H0)) -(eqP H0) /=; congr cat.
    case/typing_absP: H0 => tyr _ H0.
    by rewrite (IHt tyr (Some tyl :: ctx) (Some tyl :: ctx')) // ctxleqE eqxx.
Qed.

Fixpoint reducible (ctx : context typ) (ty : typ) (t : term) : Prop :=
  match ty with
    | tyvar n => SN t
    | tyl :->: tyr => forall t',
        ctx \|- t' \: tyl -> reducible ctx tyl t' -> reducible ctx tyr (t @ t')
  end.

Lemma CR2 ctx t t' ty :
  t ->b1 t' -> reducible ctx ty t -> reducible ctx ty t'.
Proof.
  elim: ty ctx t t'.
  - by move => /= _ _ t t' H []; apply.
  - move => /= tyl IHtyl tyr IHtyr ctx t1 t2 H H0 t3 H1 H2.
    by apply IHtyr with (t1 @ t3); auto.
Qed.

Hint Resolve CR2.

Lemma CR1_and_CR3 ty :
  (forall (ctx : context typ) t,
   all (fun ty => Some ty \in ctx) (list_hyp ty) ->
   ctx \|- t \: ty -> reducible ctx ty t -> SN t) /\
  (forall ctx t,
   all (fun ty => Some ty \in ctx) (list_hyp ty) ->
   ctx \|- t \: ty -> neutral t ->
   (forall t', t ->b1 t' -> reducible ctx ty t') -> reducible ctx ty t).
Proof.
  elim: ty; first by [].
  move => /= tyl [IHtyl1 IHtyl2] tyr [IHtyr1 IHtyr2]; split => ctx tl.
  - case/andP => /(nthP None) [x _] /esym /eqP H;
      rewrite all_cat; case/andP => H0 H1 H2 H3.
    have H4: ctx \|- tl @ x \: tyr by apply/typing_appP; exists tyl.
    suff: SN ([fun t => t @ x] tl) by apply acc_preservation; constructor.
    by apply (IHtyr1 ctx) => //; apply IHtyr2 => // t' H5;
      apply (CR2 H5); apply H3 => //; apply IHtyl2 => // y H6; inversion H6.
  - case/andP => _; rewrite all_cat; case/andP => H H0 H1 H2 H3 tr H4 H5.
    have H6: SN tr by apply (IHtyl1 ctx).
    move: tr H6 H4 H5; refine (Acc_ind' _) => tr IH H4 H5.
    have H6: ctx \|- tl @ tr \: tyr by apply/typing_appP; exists tyl.
    apply IHtyr2 => // t' H7; move: H2; inversion H7; subst => // _; eauto.
Qed.

Definition CR1 t ty := proj1 (CR1_and_CR3 ty) t.
Definition CR3 t ty := proj2 (CR1_and_CR3 ty) t.

Lemma abs_reducibility (ctx : context typ) t tyl tyr :
  all (fun ty => Some ty \in ctx) (list_hyp (tyl :->: tyr)) ->
  ctx \|- abs tyl t \: tyl :->: tyr ->
  (forall t', ctx \|- t' \: tyl ->
   reducible ctx tyl t' -> reducible ctx tyr (substitute 0 [:: t'] t)) ->
  reducible ctx (tyl :->: tyr) (abs tyl t).
Proof.
  move => /= /andP [] H; rewrite all_cat; case/andP => H0 H1 H2 H3 t' H4 H5.
  have H6: ctx \|- substitute 0 [:: t'] t \: tyr by
    apply (subject_subst0 [:: (t', tyl)]); rewrite /= ?H4 // -typing_absE.
  have {H6} H6: SN t by
    move: (CR1 H1 H6 (H3 t' H4 H5));
      apply acc_preservation => x y; apply subst_betared1.
  move: t t' {H4 H5} H6 (CR1 H0 H4 H5) H2 H3 (H4) (H5);
    refine (Acc_ind2 _) => t t' IHt IHt' H2 H3 H4 H5; apply CR3 => //.
  - by apply/typing_appP; exists tyl.
  - move => t'' H6.
    inversion H6; subst => {H6}; eauto; inversion H10; subst => {H10}.
    apply IHt => //; eauto => t'' ctx'' H6.
    by apply (CR2 (subst_betared1 0 [:: t''] H9)), H3.
Qed.

Lemma reduce_lemma ctx (ctx' : seq (term * typ)) t ty :
  [seq Some p.2 | p <- ctx'] ++ ctx \|- t \: ty ->
  all (fun ty => Some ty \in ctx)
      (list_hyp' ([seq Some p.2 | p <- ctx'] ++ ctx) t) ->
  all (fun p => ctx \|- p.1 \: p.2) ctx' ->
  Forall (fun p => reducible ctx p.2 p.1) ctx' ->
  reducible ctx ty (substitute 0 (unzip1 ctx') t).
Proof.
  elim: t ty ctx ctx'.
  - move => /= n ty ctx ctx' H.
    rewrite -(eqP H) cats0 subn0 size_map shiftzero /=.
    elim: ctx' n H => [| c' ctx' IH []] /=.
    + move => n H H0 _ _; rewrite nth_nil subn0.
      apply CR3 => // t' H1; inversion H1.
    + case/eqP => ->; tauto.
    + by move => n H H0 /andP [_ H1] [_]; apply IH.
  - move => /= tl IHtl tr IHtr tyr ctx ctx' H.
    rewrite -(eqP H) /=; case/typing_appP: H => tyl H H0.
    rewrite !all_cat; case/and3P => H1 H2 H3 H4 H5.
    move: (IHtl (tyl :->: tyr) ctx ctx') => /=; apply; auto.
    by apply subject_subst0.
  - move => /= tyl t IHt ty ctx ctx' H.
    rewrite -(eqP H) /=; case/typing_absP: H => tyr -> H.
    rewrite all_cat; case/andP => H0 H1 H2 H3.
    simpl substitute; apply abs_reducibility => //;
      first by apply (@subject_subst0 (abs tyl t)) => //; rewrite typing_absE.
    move => /= t2 H4 H5.
    rewrite subst_app /=.
    apply (IHt tyr ctx ((t2, tyl) :: ctx')) => //=.
    by rewrite H4.
Qed.

Theorem typed_term_is_sn ctx t ty : ctx \|- t \: ty -> SN t.
Proof.
  move => H.
  have H0: ctx ++ map some (list_hyp' ([::] ++ ctx) t) \|- t \: ty by
    move: H; apply ctxleq_preserves_typing, ctxleq_appr.
  move: (@reduce_lemma _ [::] _ _ H0) => /=.
  rewrite (ctxleq_list_hyp' (ctxleq_appr ctx _) H).
  have ->: forall xs ys, all (fun x => Some x \in xs ++ map some ys) ys by
    move => A xs ys; apply/allP => x H1;
      rewrite mem_cat; apply/orP/or_intror/map_f.
  move/(_ erefl erefl I); rewrite subst_nil; apply CR1 => //.
  by apply/allP => /= ty' H1; rewrite list_hyp'E mem_cat;
    apply/orP/or_intror/map_f; rewrite mem_cat -(eqP H) H1.
Qed.

End strong_normalization_proof_typed.
