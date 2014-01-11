Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.lib.Relations_ext LCAC.lib.ssrnat_ext LCAC.lib.seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive typ := tyvar of nat | tyfun of typ & typ | tyabs of typ.

Inductive term
  := var  of nat                       (* variable *)
   | app  of term & term & typ         (* value application *)
   | abs  of term                      (* value abstraction *)
   | uapp of term & typ & typ          (* universal application *)
   | uabs of term.                     (* universal abstraction *)

Coercion tyvar : nat >-> typ.
Coercion var : nat >-> term.

Notation "ty :->: ty'" := (tyfun ty ty') (at level 70, no associativity).
Notation "t @{ t' \: ty }" := (app t t' ty) (at level 60, no associativity).
Notation "{ t \: ty }@ ty'" := (uapp t ty ty') (at level 60, no associativity).

Fixpoint eqtyp t1 t2 :=
  match t1, t2 with
    | tyvar n, tyvar m => n == m
    | t1l :->: t1r, t2l :->: t2r => eqtyp t1l t2l && eqtyp t1r t2r
    | tyabs tl, tyabs tr => eqtyp tl tr
    | _, _ => false
  end.

Lemma eqtypP : Equality.axiom eqtyp.
Proof.
  elim => [n | ty1l IHl ty1r IHr | ty1 IH];
    case => //= [m | ty2l ty2r | ty2]; try by constructor.
  - case_eq (n == m); move/eqP; constructor; congruence.
  - case_eq (eqtyp ty1l ty2l); move/IHl; case_eq (eqtyp ty1r ty2r); move/IHr;
      constructor; congruence.
  - case_eq (eqtyp ty1 ty2); move/IH; constructor; congruence.
Defined.

Canonical typ_eqMixin := EqMixin eqtypP.
Canonical typ_eqType := Eval hnf in EqType typ typ_eqMixin.

Fixpoint eqterm t1 t2 :=
  match t1, t2 with
    | var n, var m => n == m
    | t1l @{t1r \: ty1}, t2l @{t2r \: ty2} =>
      [&& eqterm t1l t2l, eqterm t1r t2r & ty1 == ty2]
    | abs t1, abs t2 => eqterm t1 t2
    | {t1 \: ty1l}@ ty1r, {t2 \: ty2l}@ ty2r =>
      [&& eqterm t1 t2, ty1l == ty2l & ty1r == ty2r]
    | uabs t1, uabs t2 => eqterm t1 t2
    | _, _ => false
  end.

Lemma eqtermP : Equality.axiom eqterm.
Proof.
  elim => [n | t1l IHl t1r IHr ty1 | t1 IH | t1 IH ty1l ty1r | t1 IH];
    case => //= [m | t2l t2r ty2 | t2 | t2 ty2l ty2r | t2]; try by constructor.
  - case_eq (n == m); move/eqP; constructor; congruence.
  - case_eq (eqterm t1l t2l); move/IHl; case_eq (eqterm t1r t2r); move/IHr;
      case_eq (ty1 == ty2); move/eqP; constructor; congruence.
  - case_eq (eqterm t1 t2); move/IH; constructor; congruence.
  - case_eq (eqterm t1 t2); move/IH; case_eq (ty1l == ty2l); move/eqP;
      case_eq (ty1r == ty2r); move/eqP; constructor; congruence.
  - case_eq (eqterm t1 t2); move/IH; constructor; congruence.
Defined.

Canonical term_eqMixin := EqMixin eqtermP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Fixpoint shift_typ d c t :=
  match t with
    | tyvar n => tyvar (if c <= n then n + d else n)
    | tl :->: tr => shift_typ d c tl :->: shift_typ d c tr
    | tyabs t => tyabs (shift_typ d c.+1 t)
  end.

Definition subst_typv ts m n :=
  shift_typ n 0 (nth (tyvar (m - n - size ts)) ts (m - n)).

Fixpoint subst_typ n ts t :=
  match t with
    | tyvar m => if n <= m then subst_typv ts m n else m
    | tl :->: tr => subst_typ n ts tl :->: subst_typ n ts tr
    | tyabs t => tyabs (subst_typ n.+1 ts t)
  end.

Fixpoint typemap (f : nat -> typ -> typ) n t :=
  match t with
    | var m => var m
    | tl @{tr \: ty} => typemap f n tl @{typemap f n tr \: f n ty}
    | abs t => abs (typemap f n t)
    | {t \: ty1}@ ty2 => {typemap f n t \: f n.+1 ty1}@ f n ty2
    | uabs t => uabs (typemap f n.+1 t)
  end.

Fixpoint shift_term d c t :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | tl @{tr \: ty} => shift_term d c tl @{shift_term d c tr \: ty}
    | abs t => abs (shift_term d c.+1 t)
    | {t \: ty1}@ ty2 => {shift_term d c t \: ty1}@ ty2
    | uabs t => uabs (shift_term d c t)
  end.

Definition subst_termv ts m n n' :=
  typemap (shift_typ n') 0
    (shift_term n 0
      (nth (var (m - n - size ts)) ts (m - n))).

Fixpoint subst_term n n' ts t :=
  match t with
    | var m => if n <= m then subst_termv ts m n n' else m
    | tl @{tr \: ty} => subst_term n n' ts tl @{subst_term n n' ts tr \: ty}
    | abs t => abs (subst_term n.+1 n' ts t)
    | {t \: ty1}@ ty2 => {subst_term n n' ts t \: ty1}@ ty2
    | uabs t => uabs (subst_term n n'.+1 ts t)
  end.

Fixpoint typing (ctx : context typ) (t : term) (ty : typ) : bool :=
  match t, ty with
    | var n, _ => ctxindex ctx n ty
    | tl @{tr \: ty'}, _ => typing ctx tl (ty' :->: ty) && typing ctx tr ty'
    | abs t, tyl :->: tyr => typing (Some tyl :: ctx) t tyr
    | {t \: ty1}@ ty2, _ =>
      (ty == subst_typ 0 [:: ty2] ty1) && typing ctx t (tyabs ty1)
    | uabs t, tyabs ty => typing (ctxmap (shift_typ 1 0) ctx) t ty
    | _, _ => false
  end.

(*
Record tterm ctx ty : Set :=
  typed_term {
    term_of_tterm :> term ;
    _ : typing ctx term_of_tterm ty
  }.

Arguments typed_term [ctx ty] term_of_tterm _.

Canonical tterm_subType ctx ty := [subType for @term_of_tterm ctx ty].
Definition tterm_eqMixin ctx ty := Eval hnf in [eqMixin of tterm ctx ty by <:].
Canonical tterm_eqType ctx ty :=
  Eval hnf in EqType (tterm ctx ty) (tterm_eqMixin ctx ty).

Definition var_tterm ctx ty n (H : ctxindex ctx n ty) : tterm ctx ty :=
  typed_term n H.

Definition app_tterm ctx tyl tyr
  (tl : tterm ctx (tyl :->: tyr)) (tr : tterm ctx tyl) : tterm ctx tyr :=
  match tl with typed_term tl Hl =>
    match tr with typed_term tr Hr =>
      typed_term (tl @{tr \: tyl}) (introT andP (conj Hl Hr))
    end
  end.

Definition abs_tterm ctx tyl tyr
  (t : tterm (Some tyl :: ctx) tyr) : tterm ctx (tyl :->: tyr) :=
  match t with typed_term t H =>
    @typed_term ctx (tyl :->: tyr) (abs t) H
  end.

Definition uapp_tterm ctx tyl
  (t : tterm ctx (tyabs tyl)) tyr : tterm ctx (subst_typ 0 [:: tyr] tyl) :=
  match t with typed_term t H =>
    @typed_term ctx (subst_typ 0 [:: tyr] tyl) ({t \: tyl}@ tyr)
                (introT andP (conj (eq_refl _) H))
  end.

Definition uabs_tterm ctx ty
  (t : tterm (ctxmap (shift_typ 1 0) ctx) ty) : tterm ctx (tyabs ty) :=
  match t with typed_term t H =>
    @typed_term ctx (tyabs ty) (uabs t) H
  end.
*)

Reserved Notation "t ->r1 t'" (at level 70, no associativity).

Inductive reduction1 : relation term :=
  | red1fst ty t1 t2      : abs t1 @{t2 \: ty} ->r1 subst_term 0 0 [:: t2] t1
  | red1snd t ty1 ty2     : {uabs t \: ty1}@ ty2 ->r1
                            typemap (subst_typ^~ [:: ty2]) 0 t
  | red1appl t1 t1' t2 ty : t1 ->r1 t1' -> t1 @{t2 \: ty} ->r1 t1' @{t2 \: ty}
  | red1appr t1 t2 t2' ty : t2 ->r1 t2' -> t1 @{t2 \: ty} ->r1 t1 @{t2' \: ty}
  | red1abs t t'          : t ->r1 t' -> abs t ->r1 abs t'
  | red1uapp t t' ty1 ty2 : t ->r1 t' -> {t \: ty1}@ ty2 ->r1 {t' \: ty1}@ ty2
  | red1uabs t t'         : t ->r1 t' -> uabs t ->r1 uabs t'
  where "t ->r1 t'" := (reduction1 t t').

Notation reduction := [* reduction1].
Infix "->r" := reduction (at level 70, no associativity).

Hint Constructors reduction1.

Ltac elimif :=
  (case: ifP => //=; elimif; let hyp := fresh "H" in move => hyp) || idtac.

Ltac elimif_omega :=
  elimif;
  try (match goal with
    | |- var _ = var _ => f_equal
    | |- tyvar _ = tyvar _ => f_equal
    | |- nth ?x ?xs _ = nth ?x ?xs _ => f_equal
    | |- _ => idtac
  end; ssromega).

Lemma shift_zero_ty n t : shift_typ 0 n t = t.
Proof.
  by elim: t n => /=; try congruence; move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add_ty d c d' c' t :
  c <= c' <= c + d ->
  shift_typ d' c' (shift_typ d c t) = shift_typ (d' + d) c t.
Proof.
  case/andP; elimleq; rewrite leq_add2l; elimleq;
    elim: t c c' => /=; try (move: addSn; congruence); move => *; elimif_omega.
Qed.

Lemma shift_shift_distr_ty d c d' c' t :
  c' <= c ->
  shift_typ d' c' (shift_typ d c t) = shift_typ d (d' + c) (shift_typ d' c' t).
Proof.
  elimleq; elim: t c c' => /=;
    try (move: addSn addnS; congruence); move => *; elimif_omega.
Qed.

Lemma shift_subst_distr_ty n d c ts t :
  c <= n ->
  shift_typ d c (subst_typ n ts t) = subst_typ (d + n) ts (shift_typ d c t).
Proof.
  elimleq; elim: t n c => /=;
    try (move: addSn addnS; congruence); move => v n c; elimif_omega.
  by rewrite /subst_typv shift_add_ty ?add0n ?leq_addr // !subnDA addnK addnA.
Qed.

Lemma subst_shift_distr_ty n d c ts t :
  n <= c ->
  shift_typ d c (subst_typ n ts t) =
  subst_typ n (map (shift_typ d (c - n)) ts) (shift_typ d (size ts + c) t).
Proof.
  elimleq; elim: t n => /=; try (move: addnS addSn; congruence);
    move => m n; rewrite /subst_typv size_map; elimif_omega.
  - rewrite !nth_default ?size_map /= ?(subnAC _ n) ?subnK; elimif_omega.
  - rewrite -shift_shift_distr_ty // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_shift_cancel_ty n d c ts t :
  c <= n -> size ts + n <= d + c ->
  subst_typ n ts (shift_typ d c t) = shift_typ (d - size ts) c t.
Proof.
  elimleq; rewrite addnAC leq_add2r; elimleq.
  elim: t n c => /=; try (move: addSn; congruence); move => v n c;
    elimif_omega; rewrite /subst_typv nth_default /=; f_equal; ssromega.
Qed.

Lemma subst_subst_distr_ty n m xs ys t :
  m <= n ->
  subst_typ n xs (subst_typ m ys t) =
  subst_typ m (map (subst_typ (n - m) xs) ys) (subst_typ (size ys + n) xs t).
Proof.
  elimleq; elim: t m => /=; try (move: addnS addSn; congruence);
    move => v m; elimif_omega; rewrite /subst_typv.
  - rewrite (@subst_shift_cancel_ty m) // ?size_map; last ssromega.
    rewrite -{1}addnA addKn nth_default /= /subst_typv; elimif_omega.
    by rewrite !subnDA addnK (subnAC v).
  - rewrite size_map -shift_subst_distr_ty // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_app_ty n xs ys t :
  subst_typ n xs (subst_typ (size xs + n) ys t) = subst_typ n (xs ++ ys) t.
Proof.
  elim: t n => /=; try (move: addnS; congruence);
    move => v n; elimif_omega; rewrite /subst_typv.
  - rewrite subst_shift_cancel_ty ?addn0 //
      size_cat nth_cat !subnDA addKn (subnAC v); elimif_omega.
  - rewrite nth_cat; f_equal; elimif_omega; apply nth_equal; ssromega.
Qed.

Lemma subst_nil_ty n t : subst_typ n [::] t = t.
Proof.
  elim: t n => /=; try congruence;
    move => v n; rewrite /subst_typv nth_nil /= -fun_if; elimif_omega.
Qed.

Lemma typemap_compose f g n m t :
  typemap f n (typemap g m t) =
  typemap (fun i ty => f (i + n) (g (i + m) ty)) 0 t.
Proof.
  elim: t n m => //=.
  - by move => tl IHtl tr IHtr ty n m; rewrite IHtl IHtr.
  - by move => t IH n m; rewrite IH.
  - by move => t IH ty1 ty2 n m; rewrite IH.
  - move => t IH n m; rewrite {}IH; f_equal.
    elim: t (0) => //=; move: addSnnS; congruence.
Qed.

Lemma typemap_eq' f g n m t :
  (forall o t, f (o + n) t = g (o + m) t) -> typemap f n t = typemap g m t.
Proof.
  move => H; elim: t n m H => //=.
  - by move => tl IHtl tr IHtr ty n m H; f_equal; auto; apply (H 0).
  - by move => t IH n m H; f_equal; auto; rewrite -(add0n n) -(add0n m).
  - by move => t IH ty1 ty2 n m H; f_equal; auto; [apply (H 1) | apply (H 0)].
  - by move => t IH n m H; f_equal; apply IH => o ty; rewrite -!addSnnS.
Qed.

Lemma typemap_eq f g n t :
  (forall n t, f n t = g n t) -> typemap f n t = typemap g n t.
Proof.
  move => H; apply typemap_eq' => {t} o; apply H.
Qed.

Lemma shifttyp_zero c t : typemap (shift_typ 0) c t = t.
Proof.
  elim: t c => /=; move: shift_zero_ty; congruence.
Qed.

Lemma shifttyp_add d c d' c' t :
  c <= c' <= c + d ->
  typemap (shift_typ d') c' (typemap (shift_typ d) c t) =
  typemap (shift_typ (d' + d)) c t.
Proof.
  rewrite typemap_compose => H; apply typemap_eq' => {t} n t.
  by rewrite addn0 shift_add_ty // -addnA !leq_add2l.
Qed.

Lemma shifttyp_shifttyp_distr d c d' c' t :
  c' <= c ->
  typemap (shift_typ d') c' (typemap (shift_typ d) c t) =
  typemap (shift_typ d) (d' + c) (typemap (shift_typ d') c' t).
Proof.
  rewrite !typemap_compose => H; apply typemap_eq => {t} n t.
  by rewrite shift_shift_distr_ty ?leq_add2l // addnCA.
Qed.

Lemma shifttyp_substtyp_distr n d c ts t :
  c <= n ->
  typemap (shift_typ d) c (typemap (subst_typ^~ ts) n t) =
  typemap (subst_typ^~ ts) (d + n) (typemap (shift_typ d) c t).
Proof.
  rewrite !typemap_compose => H; apply typemap_eq => {t} n' t.
  by rewrite shift_subst_distr_ty ?leq_add2l // addnCA.
Qed.

Lemma substtyp_shifttyp_distr n d c ts t :
  n <= c ->
  typemap (shift_typ d) c (typemap (subst_typ^~ ts) n t) =
  typemap (subst_typ^~ (map (shift_typ d (c - n)) ts)) n
    (typemap (shift_typ d) (size ts + c) t).
Proof.
  rewrite !typemap_compose => H; apply typemap_eq => {t} n' t.
  by rewrite subst_shift_distr_ty ?leq_add2l // subnDl addnCA addnA.
Qed.

Lemma substtyp_substtyp_distr n m xs ys t :
  m <= n ->
  typemap (subst_typ^~ xs) n (typemap (subst_typ^~ ys) m t) =
  typemap (subst_typ^~ (map (subst_typ (n - m) xs) ys)) m
    (typemap (subst_typ^~ xs) (size ys + n) t).
Proof.
  rewrite !typemap_compose => H; apply typemap_eq => {t} n' t.
  by rewrite subst_subst_distr_ty ?leq_add2l // subnDl addnCA addnA.
Qed.

Lemma shift_typemap_distr f d c n t :
  shift_term d c (typemap f n t) = typemap f n (shift_term d c t).
Proof.
  elim: t d c n => /=; congruence.
Qed.

Lemma subst_shifttyp_distr n m d c ts t :
  c + d <= m ->
  subst_term n m ts (typemap (shift_typ d) c t) =
  typemap (shift_typ d) c (subst_term n (m - d) ts t).
Proof.
  elimleq; rewrite addnAC addnK; elim: t n m c => /=;
    try (move: addSn; congruence); move => v n m c; elimif_omega.
  by rewrite /subst_termv -!shift_typemap_distr
    shifttyp_add addnC // addn0 leq_addr.
Qed.

Lemma shifttyp_subst_distr d c n m ts t :
  m <= c ->
  typemap (shift_typ d) c (subst_term n m ts t) =
  subst_term n m (map (typemap (shift_typ d) (c - m)) ts)
    (typemap (shift_typ d) c t).
Proof.
  elimleq; elim: t n m => /=; try (move: addSn; congruence);
    move => v n m; elimif_omega.
  by rewrite /subst_termv size_map -!shift_typemap_distr
    -shifttyp_shifttyp_distr // (nth_map' (typemap _ _)).
Qed.

Lemma subst_substtyp_distr n m m' tys ts t :
  m' <= m ->
  subst_term n m ts (typemap (subst_typ^~ tys) m' t) =
  typemap (subst_typ^~ tys) m' (subst_term n (size tys + m) ts t).
Proof.
  elimleq; elim: t n m m' => /=; try (move: addSn addnS; congruence);
    move => v n m m'; elimif_omega.
  rewrite /subst_termv -!shift_typemap_distr typemap_compose.
  f_equal; apply typemap_eq => {v n ts H} n t.
  rewrite subst_shift_cancel_ty; f_equal; ssromega.
Qed.

Lemma substtyp_subst_distr n m m' tys ts t :
  m <= m' ->
  typemap (subst_typ^~ tys) m' (subst_term n m ts t) =
  subst_term n m (map (typemap (subst_typ^~ tys) (m' - m)) ts)
    (typemap (subst_typ^~ tys) m' t).
Proof.
  elimleq; elim: t n m m' => /=; try (move: addSn; congruence);
    move => v n m m'; elimif_omega.
  by rewrite /subst_termv size_map -!shift_typemap_distr
    -shifttyp_substtyp_distr // (nth_map' (typemap _ _)).
Qed.

Lemma shift_zero n t : shift_term 0 n t = t.
Proof.
  by elim: t n => /=; try congruence; move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add d c d' c' t :
  c <= c' <= c + d ->
  shift_term d' c' (shift_term d c t) = shift_term (d' + d) c t.
Proof.
  case/andP; elimleq; rewrite leq_add2l; elimleq;
    elim: t c c' => /=; try (move: addSn; congruence); move => *; elimif_omega.
Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <= c ->
  shift_term d' c' (shift_term d c t) =
  shift_term d (d' + c) (shift_term d' c' t).
Proof.
  elimleq; elim: t c c' => /=; try (move: addSn addnS; congruence);
    move => v c c'; elimif_omega.
Qed.

Lemma subst_shift_distr n m d c ts t :
  n <= c ->
  shift_term d c (subst_term n m ts t) =
  subst_term n m (map (shift_term d (c - n)) ts) (shift_term d (size ts + c) t).
Proof.
  elimleq; elim: t n m => /=; try (move: addSn addnS; congruence);
    move => v n m; rewrite /subst_termv size_map; elimif_omega.
  - rewrite shift_typemap_distr !nth_default ?size_map /=; try ssromega.
    rewrite (subnAC v) subnK; elimif_omega.
  - rewrite shift_typemap_distr -shift_shift_distr // nth_map' /=.
    do 2 f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma shift_subst_distr n m d c ts t :
  c <= n ->
  shift_term d c (subst_term n m ts t) =
  subst_term (d + n) m ts (shift_term d c t).
Proof.
  elimleq; elim: t n m c => /=; try (move: addSn addnS; congruence);
    move => v n m c; elimif_omega.
  by rewrite /subst_termv shift_typemap_distr shift_add
    ?add0n ?leq_addr // !subnDA addnK addnA.
Qed.

Lemma subst_shift_cancel n m d c ts t :
  c <= n -> size ts + n <= d + c ->
  subst_term n m ts (shift_term d c t) = shift_term (d - size ts) c t.
Proof.
  elimleq; rewrite addnAC leq_add2r; elimleq; elim: t n m c => /=;
    try (move: addSn; congruence); move => v n m c; elimif_omega.
  rewrite /subst_termv nth_default /=; f_equal; ssromega.
Qed.

Lemma subst_subst_distr n n' m m' xs ys t :
  n' <= n -> m' <= m ->
  subst_term n m xs (subst_term n' m' ys t) =
  subst_term n' m' (map (subst_term (n - n') (m - m') xs) ys)
    (subst_term (size ys + n) m xs t).
Proof.
  elimleq; elimleq; elim: t n' m' => /=; try (move: addSn addnS; congruence);
    move => v n' m'; elimif_omega; rewrite /subst_termv.
  - rewrite -!shift_typemap_distr (@subst_shift_cancel n') // size_map
      ?addn0 ?leq_addr // nth_default /= /subst_termv; elimif_omega.
    by rewrite shift_typemap_distr -addnA !subnDA addKn addnK (subnAC v).
  - rewrite -!shift_typemap_distr -shift_subst_distr // subst_shifttyp_distr
      ?add0n ?leq_addr // addKn nth_map' /= /subst_termv.
    do 2 f_equal; apply nth_equal.
    rewrite size_map; elimif_omega.
Qed.

Lemma subst_app n m xs ys t :
  subst_term n m xs (subst_term (size xs + n) m ys t) =
  subst_term n m (xs ++ ys) t.
Proof.
  elim: t n m => /=; try (move: addnS; congruence).
  move => v n m; rewrite /subst_termv nth_cat size_cat; elimif_omega.
  - by rewrite -!shift_typemap_distr subst_shift_cancel
      ?addn0 // addKn addnC !subnDA.
  - rewrite /subst_termv; do 2 f_equal; apply nth_equal; ssromega.
Qed.

Lemma subst_nil n m t : subst_term n m [::] t = t.
Proof.
  elim: t n m => /=; try congruence.
  move => v n m; rewrite /subst_termv nth_nil /= -fun_if; elimif_omega.
Qed.

Lemma subst_shifttyp_app n m m' ts t :
  subst_term n m (map (typemap (shift_typ m') 0) ts) t =
  subst_term n (m' + m) ts t.
Proof.
  elim: t n m m' => /=; try (move: addnS; congruence).
  move => v n m m'; rewrite /subst_termv size_map; elimif_omega.
  move: H; elimleq.
  rewrite -!shift_typemap_distr !(nth_map' (typemap _ _)) /=; do 2 f_equal.
  elim: ts => //= t ts ->; f_equal.
  rewrite typemap_compose; apply typemap_eq => {n t ts} n t.
  by rewrite addn0 shift_add_ty ?leqnn ?leq_addr // addnC.
Qed.

Lemma redappl t1 t1' t2 ty : t1 ->r t1' -> t1 @{t2 \: ty} ->r t1' @{t2 \: ty}.
Proof.
  elim => // {t1 t1'} t1 t1' t1'' H H0 H1.
  by apply rt1n_trans with (t1' @{t2 \: ty}) => //; constructor.
Qed.

Lemma redappr t1 t2 t2' ty : t2 ->r t2' -> t1 @{t2 \: ty} ->r t1 @{t2' \: ty}.
Proof.
  elim => // {t2 t2'} t2 t2' t2'' H H0 H1.
  by apply rt1n_trans with (t1 @{t2' \: ty}) => //; constructor.
Qed.

Lemma redabs t t' : t ->r t' -> abs t ->r abs t'.
Proof.
  elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (abs t') => //; constructor.
Qed.

Lemma reduapp t t' ty1 ty2 : t ->r t' -> {t \: ty1}@ ty2 ->r {t' \: ty1}@ ty2.
Proof.
  elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with ({t' \: ty1}@ ty2) => //; constructor.
Qed.

Lemma reduabs t t' : t ->r t' -> uabs t ->r uabs t'.
Proof.
  elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (uabs t') => //; constructor.
Qed.

Hint Resolve redappl redappr redabs reduapp reduabs.

Module confluence_proof.

Reserved Notation "t ->rp t'" (at level 70, no associativity).

Inductive parred : relation term :=
  | parredfst t1 t1' t2 t2' ty :
    t1 ->rp t1' -> t2 ->rp t2' ->
    abs t1 @{t2 \: ty} ->rp subst_term 0 0 [:: t2'] t1'
  | parredsnd  t t' ty1 ty2 :
    t ->rp t' -> {uabs t \: ty1}@ ty2 ->rp typemap (subst_typ^~ [:: ty2]) 0 t'
  | parredvar n : var n ->rp var n
  | parredapp t1 t1' t2 t2' ty :
    t1 ->rp t1' -> t2 ->rp t2' -> t1 @{t2 \: ty} ->rp t1' @{t2' \: ty}
  | parredabs t t' : t ->rp t' -> abs t ->rp abs t'
  | parreduapp t t' ty1 ty2 : t ->rp t' -> {t \: ty1}@ ty2 ->rp {t' \: ty1}@ ty2
  | parreduabs t t' : t ->rp t' -> uabs t ->rp uabs t'
  where "t ->rp t'" := (parred t t').

Fixpoint reduce_all_redex t : term :=
  match t with
    | var _ => t
    | abs t1 @{t2 \: ty} =>
      subst_term 0 0 [:: reduce_all_redex t2] (reduce_all_redex t1)
    | t1 @{t2 \: ty} => reduce_all_redex t1 @{reduce_all_redex t2 \: ty}
    | abs t' => abs (reduce_all_redex t')
    | {uabs t \: ty1}@ ty2 =>
      typemap (subst_typ^~ [:: ty2]) 0 (reduce_all_redex t)
    | {t \: ty1}@ ty2 => {reduce_all_redex t \: ty1}@ ty2
    | uabs t => uabs (reduce_all_redex t)
  end.

Lemma parred_refl t : parred t t.
Proof.
  by elim: t; constructor.
Qed.

Hint Constructors parred.
Hint Resolve parred_refl.

Lemma betared1_in_parred : inclusion reduction1 parred.
Proof.
  by apply reduction1_ind; constructor.
Qed.

Lemma parred_in_betared : inclusion parred reduction.
Proof.
  apply parred_ind => //; auto.
  - move => t1 t1' t2 t2' ty H H0 H1 H2.
    apply rtc_trans' with (abs t1' @{t2 \: ty}); auto.
    apply rtc_trans' with (abs t1' @{t2' \: ty}); auto.
    by apply rtc_step.
  - move => t t' ty1 ty2 H H0.
    apply rtc_trans' with ({uabs t' \: ty1}@ ty2); auto.
    by apply rtc_step.
  - move => t1 t1' t2 t2' ty H H0 H1 H2.
    by apply rtc_trans' with (t1 @{t2' \: ty}); auto.
Qed.

Lemma shift_parred t t' d c :
  t ->rp t' -> shift_term d c t ->rp shift_term d c t'.
Proof.
  move => H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _) => //=; try by constructor.
  - by move => t1 t1' t2 t2' ty H H0 H1 H2 d c;
      rewrite subst_shift_distr //= subn0 add1n; auto.
  - by move => t t' ty1 ty2 H H0 d c; rewrite shift_typemap_distr; auto.
Qed.

Lemma shifttyp_parred t t' d c :
  t ->rp t' -> typemap (shift_typ d) c t ->rp typemap (shift_typ d) c t'.
Proof.
  move => H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => t1 t1' t2 t2' ty H H0 H1 H2 d c;
      rewrite shifttyp_subst_distr //= subn0; auto.
  - by move => t t' ty1 ty2 H H0 n m;
      rewrite substtyp_shifttyp_distr //= subn0 add1n; auto.
Qed.

Lemma substtyp_parred n tys t t' :
  t ->rp t' ->
  typemap (subst_typ^~ tys) n t ->rp typemap (subst_typ^~ tys) n t'.
Proof.
  move => H; move: t t' H n.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => t1 t1' t2 t2' ty H H0 H1 H2 n;
      rewrite substtyp_subst_distr //= subn0; auto.
  - by move => t t' ty1 ty2 H H0 n;
      rewrite substtyp_substtyp_distr //= subn0 add1n; auto.
Qed.

Lemma subst_parred n m ps t t' :
  Forall (prod_curry parred) ps -> t ->rp t' ->
  subst_term n m [seq fst p | p <- ps] t ->rp
  subst_term n m [seq snd p | p <- ps] t'.
Proof.
  move => H H0; move: t t' H0 n m.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => tl tl' tr tr' ty H0 H1 H2 H3 n m;
      rewrite subst_subst_distr //= !subn0 add1n; auto.
  - by move => t t' ty1 ty2 H0 H1 n m; rewrite subst_substtyp_distr //=; auto.
  - move => v n m.
    rewrite /subst_termv !size_map.
    case: ifP => // _.
    elim: ps H (v - n) => //= {v} [[t t']] ts IH [H H0] [| v] //=.
    - by apply shifttyp_parred, shift_parred.
    - by rewrite subSS; apply IH.
Qed.

Lemma parred_all_lemma t t' : t ->rp t' -> t' ->rp reduce_all_redex t.
Proof with auto.
  move: t t'; fix 3 => t t' H; inversion H; subst => {H} /=; auto.
  - apply (@subst_parred 0 0 [:: (t2', reduce_all_redex t2)]) => /=; auto.
  - by apply substtyp_parred; apply parred_all_lemma.
  - by destruct t1; auto; inversion H0; auto.
  - by destruct t0; auto; inversion H0; auto.
Qed.

Lemma parred_confluent : confluent parred.
Proof.
  by move => t1 t2 t3 H H0;
    exists (reduce_all_redex t1); split; apply parred_all_lemma.
Qed.

Theorem betared_confluent : confluent reduction.
Proof.
  apply (rtc_confluent'
    betared1_in_parred parred_in_betared parred_confluent).
Qed.

End confluence_proof.

Module subject_reduction_proof.

Lemma ctxleq_preserves_typing ctx1 ctx2 t ty :
  ctx1 <=c ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  elim: t ty ctx1 ctx2 =>
    [n | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - by move => ty ctx1 ctx2; move/ctxleqP; apply.
  - by move => ty ctx1 ctx2 H; case/andP; move/(IHtl _ _ _ H) => ->; apply IHtr.
  - by move => tyl tyr ctx1 ctx2 H; apply IHt; rewrite ctxleqss eqxx.
  - by move => ty ctx1 ctx2 H; case/andP => ->; apply IHt.
  - by move => ty ctx1 ctx2 H; apply IHt, ctxleq_map.
Qed.

Lemma shifttyp_preserves_typing d c ctx t ty :
  typing ctx t ty ->
  typing (ctxmap (shift_typ d c) ctx)
    (typemap (shift_typ d) c t) (shift_typ d c ty).
Proof.
  elim: t ty d c ctx =>
    [n | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - by move => ty d c ctx; apply ctxindex_map.
  - by move => ty d c ctx; case/andP; move/IHtl => ->; apply IHtr.
  - by move => tyl tyr d c ctx; move/(IHt _ d c).
  - move => ty d c ctx; case/andP; move/eqP => ?; subst ty; move/IHt => ->.
    by rewrite subst_shift_distr_ty //= subn0 add1n eqxx.
  - move => ty d c ctx; move/(IHt _ d c.+1).
    rewrite /is_true => <-; f_equal.
    rewrite -!map_comp.
    apply eq_map; case => //= ty'.
    by rewrite (shift_shift_distr_ty d).
Qed.

Lemma substtyp_preserves_typing n tys ctx t ty :
  typing ctx t ty ->
  typing (ctxmap (subst_typ n tys) ctx)
    (typemap (subst_typ^~ tys) n t) (subst_typ n tys ty).
Proof.
  elim: t ty n ctx =>
    [m | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - by move => ty n ctx; apply ctxindex_map.
  - by move => ty n ctx; case/andP; move/IHtl => ->; apply IHtr.
  - by move => tyl tyr n ctx; move/(IHt _ n).
  - move => ty n ctx; case/andP; move/eqP => ?; subst ty; move/IHt => ->.
    by rewrite subst_subst_distr_ty //= subn0 add1n eqxx.
  - move => ty n ctx; move/(IHt _ n.+1).
    rewrite /is_true => <-; f_equal.
    rewrite -!map_comp.
    apply eq_map; case => //= ty'.
    by rewrite shift_subst_distr_ty.
Qed.

Lemma subject_shift t ty c ctx1 ctx2 :
  typing ctx1 t ty ->
  typing (ctxinsert ctx2 ctx1 c) (shift_term (size ctx2) c t) ty.
Proof.
  elim: t ty c ctx1 ctx2 =>
    [m | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - move => ty c ctx1 ctx2.
    by move/eqP => ->; apply/eqP; rewrite nth_ctxinsert; elimif_omega.
  - by move => ty c ctx1 ctx2; case/andP; move/IHtl => ->; apply IHtr.
  - by move => tyl tyr c ctx1 ctx2; move/(IHt _ c.+1 _ ctx2).
  - by move => ty c ctx1 ctx2; case/andP => ->; apply IHt.
  - move => ty c ctx1 ctx2; move/(IHt _ c _ (ctxmap (shift_typ 1 0) ctx2)).
    by rewrite map_ctxinsert size_map.
Qed.

Lemma subject_subst t ty n ctx ctx' :
  all (fun p => typing (drop n ctx) p.1 p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (subst_term n 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  elim: t ty n ctx ctx' =>
    [m | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - move => ty n ctx ctx' H.
    rewrite /subst_termv shifttyp_zero nth_ctxinsert !size_map; elimif_omega.
    + move: H0 H1 {H2}; elimleq; rewrite ltn_add2l => H0.
      rewrite !(nth_map (var 0, tyvar 0)) //.
      case/eqP => ?; subst ty.
      case: {m H0} (nth _ _ _) (all_nthP (var 0, tyvar 0) H m H0) => /= t ty.
      move/(subject_shift 0 (ctxinsert [::] (take n ctx) n)).
      rewrite size_ctxinsert size_take minnC minKn add0n.
      apply ctxleq_preserves_typing.
      rewrite /ctxinsert take0 sub0n take_minn minnn size_take minnE subKn
              ?leq_subr //= drop_take_nil cats0 drop0 -catA
              -{4}(cat_take_drop n ctx) ctxleq_appl.
      case/orP: (leq_total n (size ctx)).
      * by rewrite -subn_eq0; move/eqP => ->; apply ctxleqxx.
      * by move => H0; rewrite drop_oversize // cats0 ctxleql0 size_nseq.
    + move: H0 H1 {H2}; elimleq; move/negbT; rewrite -leqNgt leq_add2l => H0 H1.
      rewrite nth_default ?size_map //=.
      by move: H0 H1; elimleq; rewrite addnAC addnK addnC.
  - by move => ty n ctx ctx' H; case/andP; move/IHtl => -> //=; apply IHtr.
  - by move => tyl tyr n ctx ctx' H H0; apply IHt.
  - by move => ty n ctx ctx' H; case/andP => ->; apply IHt.
  - move => ty n ctx ctx' H H0.
    rewrite -{2}(addn0 1) -subst_shifttyp_app.
    set ctx'' := (map _ (map _ _)).
    have {ctx''} ->: ctx'' = [seq p.1 | p <-
        [seq (typemap (shift_typ 1) 0 p.1, shift_typ 1 0 p.2) | p <- ctx']]
      by rewrite /ctx'' -!map_comp /funcomp /=.
    apply IHt.
    + move: H {t ty IHt H0}; rewrite all_map; apply sub_all.
      rewrite /subpred /preim /pred_of_simpl; case => /= t ty.
      rewrite -map_drop; apply shifttyp_preserves_typing.
    + by move: H0; rewrite map_ctxinsert -!map_comp.
Qed.

Theorem subject_reduction ctx t t' ty :
  t ->r1 t' -> typing ctx t ty -> typing ctx t' ty.
Proof.
  move => H; move: t t' H ctx ty.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=.
  - move => ty' t1 t2 ctx ty; case/andP => H H0.
    apply (@subject_subst _ _ 0 ctx [:: (t2, ty')]) => //=.
    - by rewrite drop0 H0.
    - by rewrite /ctxinsert take0 drop0.
  - move => t tyl tyr ctx ty; case/andP; move/eqP => ?; subst ty.
    move/(substtyp_preserves_typing 0 [:: tyr]).
    set ctx' := ctxmap _ _; have {ctx'} -> //: ctx' = ctx.
      rewrite /ctx' -map_comp -{2}(map_id ctx).
      apply eq_map; case => //= ty.
      by rewrite subst_shift_cancel_ty //= shift_zero_ty.
  - by move => t1 t1' t2 ty _ H ctx ty0; case/andP; move/H => ->.
  - by move => t1 t2 t2' ty _ H ctx ty0; case/andP => ->; apply H.
  - by move => t t' _ H ctx [] //= tyl tyr; apply H.
  - by move => t t' tyl tyr _ H ctx ty; case/andP => ->; apply H.
  - by move => t t' _ H ctx [] //=; apply H.
Qed.

End subject_reduction_proof.

Module strong_normalization_proof.

Import subject_reduction_proof.

Definition SNorm (t : term) : Prop := Acc (fun x y => reduction1 y x) t.

Lemma snorm_appl tl tr ty : SNorm (tl @{tr \: ty}) -> SNorm tl.
Proof.
  move: tl.
  fix IH 2 => tl [H]; constructor => tl' H0.
  by apply IH, H; constructor.
Qed.

Definition neutral (t : term) : bool :=
  match t with
    | abs _ => false
    | uabs _ => false
    | _ => true
  end.

Definition CR1 ctx ty (P : forall t, typing ctx t ty -> Prop) :=
  forall t (H : typing ctx t ty), P t H -> SNorm t.

Definition CR2 ctx ty (P : forall t, typing ctx t ty -> Prop) :=
  forall t t' (H : typing ctx t ty) (H' : typing ctx t' ty),
    t ->r1 t' -> P t H -> P t' H'.

Definition CR3 ctx ty (P : forall t, typing ctx t ty -> Prop) :=
  forall t (H : typing ctx t ty), neutral t ->
    (forall t' (H' : t ->r1 t'), P t' (subject_reduction H' H)) -> P t H.

Record RC ctx ty (P : forall t, typing ctx t ty -> Prop) : Prop :=
  reducibility_candidate {
    rc_cr1 : CR1 P ;
    rc_cr2 : CR2 P ;
    rc_cr3 : CR3 P
  }.

Lemma CR4
  ctx ty (P : forall t, typing ctx t ty -> Prop) t (H : typing ctx t ty) :
  RC P -> neutral t -> (forall t', ~ t ->r1 t') -> P t H.
Proof. by case => _ _ H0 H1 H2; apply H0 => // t' H3; move: (H2 _ H3). Qed.

Lemma CR4' ctx ty (P : forall t, typing ctx t ty -> Prop)
  v (H : ctxindex ctx v ty) : RC P -> P v H.
Proof. move/CR4; apply => // t' H0; inversion H0. Qed.

Lemma rcfun_isrc ctx tyl tyr
  (P : forall t, typing ctx t tyl -> Prop)
  (Q : forall t, typing ctx t tyr -> Prop)
  t (H : typing ctx t tyl) :
  RC P -> RC Q -> P t H ->
  RC (fun u H' => forall v H'', P v H'' ->
    Q (u @{v \: tyl}) (introT andP (conj H' H''))).
Proof.
  move => [CR1l CR2l CR3l] [CR1r CR2r CR3r] Ht; constructor.
  - by move => /= f Hf; move/(_ t H Ht)/CR1r/snorm_appl.
  - by move => /= t1 t2 H0 H1 H2 H3 t3 H4; move/H3; apply CR2r; constructor.
  - move => /= t1 H0 H1 H2 t2 H3 H4.
    move: (CR1l t2 H3 H4) => H5; move: t2 H5 H3 H4.
    refine (Acc_ind _ _) => t2 _ H3 H4 H5.
    apply CR3r => // t3 H6; move: H1;
      inversion H6; subst => //= H7; apply CR3r => // t' H8.
    + by apply (CR2r (t1' @{t2 \: tyl}) t'
        (introT andP (conj (subject_reduction H10 H0) H4)) _ H8), H2.
    + by apply (CR2r (t1 @{t2' \: tyl}) t'
        (introT andP (conj H0 (subject_reduction H10 H4))) _ H8),
        (H3 _ H10), (CR2l t2 t2' H4 (subject_reduction H10 H4) H10).
Qed.



End strong_normalization_proof.
