Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.Relations_ext LCAC.lib.ssrnat_ext LCAC.lib.seq_ext.

Require LCAC.LC.Debruijn.Untyped.
Module U := LCAC.LC.Debruijn.Untyped.
Import U.Lambda_tactics.

Set Implicit Arguments.

Inductive typ := tyvar of nat | tyfun of typ & typ | tyabs of typ.

Inductive term
  := var  of nat                       (* variable *)
   | app  of term & term               (* value application *)
   | abs  of typ & term                (* value abstraction *)
   | uapp of term & typ                (* universal application *)
   | uabs of term.                     (* universal abstraction *)

Coercion tyvar : nat >-> typ.
Coercion var : nat >-> term.

Ltac elimif_omega :=
  elimif;
  try (match goal with
    | |- var _ = var _ => f_equal
    | |- tyvar _ = tyvar _ => f_equal
    | |- nth ?x ?xs _ = nth ?x ?xs _ => f_equal
    | |- _ => idtac
  end; ssromega).

Fixpoint shift_typ d c t :=
  match t with
    | tyvar n => tyvar (if c <= n then n + d else n)
    | tyfun tl tr => tyfun (shift_typ d c tl) (shift_typ d c tr)
    | tyabs t => tyabs (shift_typ d c.+1 t)
  end.

Definition subst_typv ts m n :=
  shift_typ n 0 (nth (tyvar (m - n - size ts)) ts (m - n)).

Fixpoint subst_typ n ts t :=
  match t with
    | tyvar m => if n <= m then subst_typv ts m n else m
    | tyfun tl tr => tyfun (subst_typ n ts tl) (subst_typ n ts tr)
    | tyabs t => tyabs (subst_typ n.+1 ts t)
  end.

Fixpoint shift_term d c t :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | app tl tr => app (shift_term d c tl) (shift_term d c tr)
    | abs ty t => abs ty (shift_term d c.+1 t)
    | uapp t ty => uapp (shift_term d c t) ty
    | uabs t => uabs (shift_term d c t)
  end.

Definition subst_termv ts m n :=
  shift_term n 0 (nth (var (m - n - size ts)) ts (m - n)).

Fixpoint subst_term n ts t :=
  match t with
    | var m => if n <= m then subst_termv ts m n else m
    | app tl tr => app (subst_term n ts tl) (subst_term n ts tr)
    | abs ty t => abs ty (subst_term n.+1 ts t)
    | uapp t ty => uapp (subst_term n ts t) ty
    | uabs t => uabs (subst_term n ts t)
  end.

Fixpoint type_map (f : nat -> typ -> typ) n t :=
  match t with
    | var m => var m
    | app tl tr => app (type_map f n tl) (type_map f n tr)
    | abs ty t => abs (f n ty) (type_map f n t)
    | uapp t ty => uapp (type_map f n t) (f n ty)
    | uabs t => uabs (type_map f n.+1 t)
  end.

Definition shift_context d c ctx := map (Option.map (shift_typ d c)) ctx.

Reserved Notation "t ->r1 t'" (at level 70, no associativity).
Reserved Notation "t ->rp t'" (at level 70, no associativity).

Inductive reduction1 : relation term :=
  | red1fst  : forall ty t1 t2, app (abs ty t1) t2 ->r1 subst_term 0 [:: t2] t1
  | red1snd  : forall t ty,
               uapp (uabs t) ty ->r1 type_map (subst_typ^~ [:: ty]) 0 t
  | red1appl : forall t1 t1' t2, t1 ->r1 t1' -> app t1 t2 ->r1 app t1' t2
  | red1appr : forall t1 t2 t2', t2 ->r1 t2' -> app t1 t2 ->r1 app t1 t2'
  | red1abs  : forall ty t t', t ->r1 t' -> abs ty t ->r1 abs ty t'
  | red1uapp : forall t t' ty, t ->r1 t' -> uapp t ty ->r1 uapp t' ty
  | red1uabs : forall t t', t ->r1 t' -> uabs t ->r1 uabs t'
  where "t ->r1 t'" := (reduction1 t t').

Notation reduction := [* reduction1].
Infix "->r" := reduction (at level 70, no associativity).

Inductive parred : relation term :=
  | parredfst  : forall ty t1 t1' t2 t2', t1 ->rp t1' -> t2 ->rp t2' ->
                 app (abs ty t1) t2 ->rp subst_term 0 [:: t2'] t2'
  | parredsnd  : forall t t' ty, t ->rp t' ->
                 uapp (uabs t) ty ->rp type_map (subst_typ^~ [:: ty]) 0 t'
  | parredapp  : forall t1 t1' t2 t2',
                 t1 ->rp t1' -> t2 ->rp t2' -> app t1 t2 ->rp app t1' t2'
  | parredabs  : forall ty t t', t ->rp t' -> abs ty t ->rp abs ty t'
  | parreduapp : forall t t' ty, t ->rp t' -> uapp t ty ->rp uapp t' ty
  | parreduabs : forall t t', t ->rp t' -> uabs t ->rp uabs t'
  where "t ->rp t'" := (parred t t').

Inductive typing : context typ -> term -> typ -> Prop :=
  | typvar  : forall ctx n ty, ctxindex ctx n ty -> typing ctx (var n) ty
  | typapp  : forall ctx t1 t2 ty1 ty2,
              typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
              typing ctx (app t1 t2) ty2
  | typabs  : forall ctx t ty1 ty2,
              typing (Some ty1 :: ctx) t ty2 ->
              typing ctx (abs ty1 t) (tyfun ty1 ty2)
  | typuapp : forall ctx t ty1 ty2,
              typing ctx t (tyabs ty1) ->
              typing ctx (uapp t ty2) (subst_typ 0 [:: ty2] ty1)
  | typuabs : forall ctx t ty,
              typing (shift_context 1 0 ctx) t ty ->
              typing ctx (uabs t) (tyabs ty).

Lemma shiftzero_ty : forall n t, shift_typ 0 n t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  by move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add_ty :
  forall d d' c c' t, c <= c' <= d + c ->
  shift_typ d' c' (shift_typ d c t) = shift_typ (d' + d) c t.
Proof.
  move => d d' c c' t; elim: t c c' => /=.
  - move => n c c' H; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => t IH c c' ?; rewrite IH // addnS !ltnS.
Qed.

Lemma shift_shift_distr_ty :
  forall d c d' c' t,
  c' <= c -> shift_typ d' c' (shift_typ d c t) =
  shift_typ d (d' + c) (shift_typ d' c' t).
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' ?; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => t' IH c c' ?; rewrite -addnS IH.
Qed.

Lemma subst_shift_distr_ty :
  forall n d c ts t,
  shift_typ d (n + c) (subst_typ n ts t) =
  subst_typ n (map (shift_typ d c) ts) (shift_typ d (size ts + n + c) t).
Proof.
  move => n d c ts t; elim: t n => /=.
  - move => m n; rewrite /subst_typv size_map; elimif_omega.
    - rewrite !nth_default ?size_map /=; try ssromega.
      rewrite (subnAC _ n) subnK; elimif_omega.
    - rewrite -shift_shift_distr_ty // nth_map' /=.
      f_equal; apply nth_equal; rewrite size_map; elimif_omega.
  - congruence.
  - by move => t IH n; rewrite (IH n.+1) addnS addSn.
Qed.

Lemma shift_subst_distr_ty :
  forall n d c t ts, c <= n ->
  shift_typ d c (subst_typ n ts t) = subst_typ (d + n) ts (shift_typ d c t).
Proof.
  move => n d c t ts; elim: t n c => /=.
  - move => n m c H; elimif_omega.
    by rewrite /subst_typv shift_add_ty ?addn0 // (addnC n) subnDl.
  - move => tl IHl tr IHr n c H; f_equal; auto.
  - move => t IH n c H; f_equal; rewrite -addnS IH //.
Qed.

Lemma subst_shift_cancel_ty :
  forall n d c t ts, n <= d ->
  subst_typ (c + n) ts (shift_typ (size ts + d) c t) = shift_typ d c t.
Proof.
  move => n d c t ts; elim: t c => /=.
  - move => v c H; elimif_omega.
    rewrite /subst_typv nth_default /=; f_equal; ssromega.
  - by move => tl IHtl tr IHtr c H; rewrite IHtl // IHtr.
  - by move => t IH c H; rewrite -addSn IH.
Qed.

Lemma subst_subst_distr_ty :
  forall n m t xs ys,
  subst_typ (m + n) xs (subst_typ m ys t) =
  subst_typ m (map (subst_typ n xs) ys) (subst_typ (size ys + m + n) xs t).
Proof.
  move => n m t; elim: t m => /=.
  - move => v m xs ys; elimif_omega; rewrite /subst_typv.
    - rewrite -{5}(add0n m) -addnA -{2}(size_map (subst_typ n xs) ys)
        subst_shift_cancel_ty; last apply leq_addr.
      rewrite nth_default /=; last ssromega.
      rewrite /subst_typv subnAC subnK ?subnDA; elimif_omega.
    - rewrite -shift_subst_distr_ty // size_map nth_map'; f_equal.
      apply nth_equal; rewrite size_map /=; elimif_omega.
  - congruence.
  - by move => t IH m xs ys; rewrite -addSn IH addnS addSn.
Qed.

Lemma subst_app_ty :
  forall n t xs ys,
  subst_typ n xs (subst_typ (size xs + n) ys t) = subst_typ n (xs ++ ys) t.
Proof.
  move => n t xs ys; elim: t n => /=.
  - move => v n; elimif_omega; rewrite /subst_typv.
    - rewrite -{1}(add0n n) subst_shift_cancel_ty //
        nth_cat size_cat !subnDA (subnAC _ (size xs)); f_equal; elimif_omega.
    - rewrite nth_cat; f_equal; elimif_omega; apply nth_equal; ssromega.
  - congruence.
  - by move => t IH n; rewrite -addnS IH.
Qed.

Lemma subst_nil_ty : forall n t, subst_typ n [::] t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  move => v n; rewrite /subst_typv nth_nil /= -fun_if; elimif_omega.
Qed.

Lemma shiftzero : forall n t, shift_term 0 n t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  by move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add :
  forall d d' c c' t, c <= c' <= d + c ->
  shift_term d' c' (shift_term d c t) = shift_term (d' + d) c t.
Proof.
  move => d d' c c' t; elim: t c c' => /=.
  - move => n c c' H; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => ty t IH c c' ?; rewrite IH // addnS !ltnS.
  - by move => t IH ty c c' H; rewrite IH.
  - by move => t IH c c' H; rewrite IH.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift_term d' c' (shift_term d c t) =
  shift_term d (d' + c) (shift_term d' c' t).
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' ?; elimif_omega.
  - move => t1 ? t2 ? c c' ?; f_equal; auto.
  - by move => ty t' IH c c' ?; rewrite -addnS IH.
  - by move => t IH ty c c' H; rewrite IH.
  - by move => t IH c c' H; rewrite IH.
Qed.

Lemma subst_shift_distr :
  forall n d c ts t,
  shift_term d (n + c) (subst_term n ts t) =
  subst_term n (map (shift_term d c) ts) (shift_term d (size ts + n + c) t).
Proof.
  move => n d c ts t; elim: t n => /=; try congruence.
  - move => m n; rewrite /subst_termv size_map; elimif_omega.
    - rewrite !nth_default ?size_map /=; try ssromega.
      rewrite (subnAC _ n) subnK; elimif_omega.
    - rewrite -shift_shift_distr // nth_map' /=.
      f_equal; apply nth_equal; rewrite size_map; elimif_omega.
  - by move => ty t IH n; rewrite (IH n.+1) addnS addSn.
Qed.

Lemma shift_subst_distr :
  forall n d c t ts, c <= n ->
  shift_term d c (subst_term n ts t) = subst_term (d + n) ts (shift_term d c t).
Proof.
  move => n d c t ts; elim: t n c => /=.
  - move => n m c H; elimif_omega.
    by rewrite /subst_termv shift_add ?addn0 // (addnC n) subnDl.
  - move => tl IHl tr IHr n c H; f_equal; auto.
  - move => ty t IH n c H; f_equal; rewrite -addnS IH //.
  - by move => t IH ty n c H; rewrite IH.
  - by move => t IH n c H; rewrite IH.
Qed.

Lemma subst_shift_cancel :
  forall n d c t ts, n <= d ->
  subst_term (c + n) ts (shift_term (size ts + d) c t) = shift_term d c t.
Proof.
  move => n d c t ts; elim: t c => /=.
  - move => v c H; elimif_omega.
    rewrite /subst_termv nth_default /=; f_equal; ssromega.
  - by move => tl IHtl tr IHtr c H; rewrite IHtl // IHtr.
  - by move => ty t IH c H; rewrite -addSn IH.
  - by move => t IH ty c H; rewrite IH.
  - by move => t IH c H; rewrite IH.
Qed.

Lemma subst_subst_distr :
  forall n m t xs ys,
  subst_term (m + n) xs (subst_term m ys t) =
  subst_term m (map (subst_term n xs) ys) (subst_term (size ys + m + n) xs t).
Proof.
  move => n m t; elim: t m => /=; try congruence.
  - move => v m xs ys; elimif_omega; rewrite /subst_termv.
    - rewrite -{5}(add0n m) -addnA -{2}(size_map (subst_term n xs) ys)
        subst_shift_cancel; last apply leq_addr.
      rewrite nth_default /=; last ssromega.
      rewrite /subst_termv subnAC subnK ?subnDA; elimif_omega.
    - rewrite -shift_subst_distr // size_map nth_map'; f_equal.
      apply nth_equal; rewrite size_map /=; elimif_omega.
  - by move => ty t IH m xs ys; rewrite -addSn IH addnS addSn.
Qed.

Lemma subst_app :
  forall n t xs ys,
  subst_term n xs (subst_term (size xs + n) ys t) = subst_term n (xs ++ ys) t.
Proof.
  move => n t xs ys; elim: t n => /=; try congruence.
  - move => v n; elimif_omega; rewrite /subst_termv.
    - rewrite -{1}(add0n n) subst_shift_cancel //
        nth_cat size_cat !subnDA (subnAC _ (size xs)); f_equal; elimif_omega.
    - rewrite nth_cat; f_equal; elimif_omega; apply nth_equal; ssromega.
  - by move => ty t IH n; rewrite -addnS IH.
Qed.

Lemma subst_nil : forall n t, subst_term n [::] t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  move => v n; rewrite /subst_termv nth_nil /= -fun_if; elimif_omega.
Qed.
