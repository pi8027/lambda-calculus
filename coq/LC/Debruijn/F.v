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

Fixpoint typemap (f : nat -> typ -> typ) n t :=
  match t with
    | var m => var m
    | app tl tr => app (typemap f n tl) (typemap f n tr)
    | abs ty t => abs (f n ty) (typemap f n t)
    | uapp t ty => uapp (typemap f n t) (f n ty)
    | uabs t => uabs (typemap f n.+1 t)
  end.

Fixpoint shift_term d c t :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | app tl tr => app (shift_term d c tl) (shift_term d c tr)
    | abs ty t => abs ty (shift_term d c.+1 t)
    | uapp t ty => uapp (shift_term d c t) ty
    | uabs t => uabs (shift_term d c t)
  end.

Definition subst_termv ts m n n' :=
  typemap (shift_typ n') 0
    (shift_term n 0
      (nth (var (m - n - size ts)) ts (m - n))).

Fixpoint subst_term n n' ts t :=
  match t with
    | var m => if n <= m then subst_termv ts m n n' else m
    | app tl tr => app (subst_term n n' ts tl) (subst_term n n' ts tr)
    | abs ty t => abs ty (subst_term n.+1 n' ts t)
    | uapp t ty => uapp (subst_term n n' ts t) ty
    | uabs t => uabs (subst_term n n'.+1 ts t)
  end.

Definition shift_context d c ctx := map (Option.map (shift_typ d c)) ctx.

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

Reserved Notation "t ->r1 t'" (at level 70, no associativity).

Inductive reduction1 : relation term :=
  | red1fst  : forall ty t1 t2,
               app (abs ty t1) t2 ->r1 subst_term 0 0 [:: t2] t1
  | red1snd  : forall t ty,
               uapp (uabs t) ty ->r1 typemap (subst_typ^~ [:: ty]) 0 t
  | red1appl : forall t1 t1' t2, t1 ->r1 t1' -> app t1 t2 ->r1 app t1' t2
  | red1appr : forall t1 t2 t2', t2 ->r1 t2' -> app t1 t2 ->r1 app t1 t2'
  | red1abs  : forall ty t t', t ->r1 t' -> abs ty t ->r1 abs ty t'
  | red1uapp : forall t t' ty, t ->r1 t' -> uapp t ty ->r1 uapp t' ty
  | red1uabs : forall t t', t ->r1 t' -> uabs t ->r1 uabs t'
  where "t ->r1 t'" := (reduction1 t t').

Notation reduction := [* reduction1].
Infix "->r" := reduction (at level 70, no associativity).

Hint Resolve typvar typapp typabs typuapp typuabs
  red1fst red1snd red1appl red1appr red1abs red1uapp red1uabs.

Lemma shiftzero_ty : forall n t, shift_typ 0 n t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  by move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add_ty :
  forall d c d' c' t, c <= c' <= d + c ->
  shift_typ d' c' (shift_typ d c t) = shift_typ (d' + d) c t.
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' H; elimif_omega.
  - by move => tl IHtl tr IHtr c c' ?; rewrite IHtl // IHtr.
  - by move => t IH c c' ?; rewrite IH // addnS !ltnS.
Qed.

Lemma shift_shift_distr_ty :
  forall d c d' c' t,
  c' <= c -> shift_typ d' c' (shift_typ d c t) =
  shift_typ d (d' + c) (shift_typ d' c' t).
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' ?; elimif_omega.
  - by move => tl IHtl tr IHtr c c' ?; rewrite IHtl // IHtr.
  - by move => t' IH c c' ?; rewrite -addnS IH.
Qed.

Lemma shift_subst_distr_ty :
  forall n d c ts t, c <= n ->
  shift_typ d c (subst_typ n ts t) = subst_typ (d + n) ts (shift_typ d c t).
Proof.
  move => n d c ts t; elim: t n c => /=.
  - move => n m c H; elimif_omega.
    by rewrite /subst_typv shift_add_ty ?addn0 // (addnC n) subnDl.
  - by move => tl IHtl tr IHtr n c H; rewrite IHtl // IHtr.
  - by move => t IH n c H; rewrite -addnS IH.
Qed.

Lemma subst_shift_distr_ty :
  forall n d c ts t,
  shift_typ d (n + c) (subst_typ n ts t) =
  subst_typ n (map (shift_typ d c) ts) (shift_typ d (size ts + n + c) t).
Proof.
  move => n d c ts t; elim: t n => /=; try (move: addnS addSn; congruence).
  move => m n; rewrite /subst_typv size_map; elimif_omega.
  - rewrite !nth_default ?size_map /=; try ssromega.
    rewrite (subnAC _ n) subnK; elimif_omega.
  - rewrite -shift_shift_distr_ty // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_shift_cancel_ty :
  forall n d c ts t, c <= n -> size ts <= d -> n - c <= d - size ts ->
  subst_typ n ts (shift_typ d c t) = shift_typ (d - size ts) c t.
Proof.
  move => n d c ts t; elim: t n c => /=.
  - move => v n c H H0 H1; elimif_omega.
    rewrite /subst_typv nth_default /=; f_equal; ssromega.
  - by move => tl IHtl tr IHtr n c H H0 H1; rewrite IHtl // IHtr.
  - by move => t IH n c H H0 H1; rewrite IH.
Qed.

Lemma subst_subst_distr_ty :
  forall n m xs ys t,
  subst_typ (m + n) xs (subst_typ m ys t) =
  subst_typ m (map (subst_typ n xs) ys) (subst_typ (size ys + m + n) xs t).
Proof.
  move => n m xs ys t; elim: t m => /=; try (move: addnS addSn; congruence).
  move => v m; elimif_omega; rewrite /subst_typv.
  - rewrite (subst_shift_cancel_ty m) // size_map; try ssromega.
    rewrite -{1}addnA addKn nth_default /=; last ssromega.
    rewrite /subst_typv subnAC subnK ?subnDA; elimif_omega.
  - rewrite -shift_subst_distr_ty // size_map nth_map'; f_equal.
    apply nth_equal; rewrite size_map /=; elimif_omega.
Qed.

Lemma subst_app_ty :
  forall n xs ys t,
  subst_typ n xs (subst_typ (size xs + n) ys t) = subst_typ n (xs ++ ys) t.
Proof.
  move => n xs ys t; elim: t n => /=; try (move: addnS; congruence).
  move => v n; elimif_omega; rewrite /subst_typv.
  - rewrite subst_shift_cancel_ty; try ssromega.
    rewrite size_cat nth_cat !subnDA addKn (subnAC _ (size xs)); elimif_omega.
  - rewrite nth_cat; f_equal; elimif_omega; apply nth_equal; ssromega.
Qed.

Lemma subst_nil_ty : forall n t, subst_typ n [::] t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  move => v n; rewrite /subst_typv nth_nil /= -fun_if; elimif_omega.
Qed.

Lemma typemap_compose :
  forall f g n m t,
  typemap f n (typemap g m t) =
  typemap (fun i ty => f (i + n) (g (i + m) ty)) 0 t.
Proof.
  move => f g n m t; elim: t n m => //=.
  - by move => tl IHtl tr IHtr n m; rewrite IHtl IHtr.
  - by move => ty t IH n m; rewrite IH.
  - by move => t IH ty n m; rewrite IH.
  - move => t IH n m; rewrite {}IH; f_equal.
    elim: t (0) => //=; move: addSnnS; congruence.
Qed.

Lemma typemap_eq' :
  forall f g n m t,
  (forall o t, f (o + n) t = g (o + m) t) -> typemap f n t = typemap g m t.
Proof.
  move => f g n m t H; elim: t n m H => //=.
  - by move => tl IHtl tr IHtr n m H; f_equal; auto.
  - by move => ty t IH n m H; f_equal; auto; rewrite -(add0n n) -(add0n m).
  - by move => t IH ty n m H; f_equal; auto; rewrite -(add0n n) -(add0n m).
  - by move => t IH n m H; f_equal; apply IH => o ty; rewrite -!addSnnS.
Qed.

Lemma typemap_eq :
  forall f g n t, (forall n t, f n t = g n t) -> typemap f n t = typemap g n t.
Proof.
  move => f g n t H; apply typemap_eq' => {t} o; apply H.
Qed.

Lemma shifttyp_add :
  forall d c d' c' t, c <= c' <= d + c ->
  typemap (shift_typ d') c' (typemap (shift_typ d) c t) =
  typemap (shift_typ (d' + d)) c t.
Proof.
  move => d c d' c' t H.
  rewrite typemap_compose. apply typemap_eq' => {t} n t.
  by rewrite addn0 shift_add_ty // addnCA !leq_add2l.
Qed.

Lemma shifttyp_shifttyp_distr :
  forall d c d' c' t, c' <= c ->
  typemap (shift_typ d') c' (typemap (shift_typ d) c t) =
  typemap (shift_typ d) (d' + c) (typemap (shift_typ d') c' t).
Proof.
  move => d c d' c' t H.
  rewrite !typemap_compose; apply typemap_eq => {t} n t.
  by rewrite shift_shift_distr_ty ?leq_add2l // addnCA.
Qed.

Lemma shifttyp_substtyp_distr :
  forall n d c ts t, c <= n ->
  typemap (shift_typ d) c (typemap (subst_typ^~ ts) n t) =
  typemap (subst_typ^~ ts) (d + n) (typemap (shift_typ d) c t).
Proof.
  move => n d c ts t H.
  rewrite !typemap_compose; apply typemap_eq => {t} n' t.
  by rewrite shift_subst_distr_ty ?leq_add2l // addnCA.
Qed.

Lemma substtyp_shifttyp_distr :
  forall n d c ts t,
  typemap (shift_typ d) (n + c) (typemap (subst_typ^~ ts) n t) =
  typemap (subst_typ^~ (map (shift_typ d c) ts)) n
    (typemap (shift_typ d) (size ts + n + c) t).
Proof.
  move => n d c ts t.
  rewrite !typemap_compose; apply typemap_eq => {t} n' t.
  by rewrite addnA subst_shift_distr_ty !addnA (addnC (size _)).
Qed.

Lemma substtyp_substtyp_distr :
  forall n m xs ys t,
  typemap (subst_typ^~ xs) (m + n) (typemap (subst_typ^~ ys) m t) =
  typemap (subst_typ^~ (map (subst_typ n xs) ys)) m
    (typemap (subst_typ^~ xs) (size ys + m + n) t).
Proof.
  move => n m xs ys t.
  rewrite !typemap_compose; apply typemap_eq => {t} n' t.
  by rewrite addnA subst_subst_distr_ty !addnA (addnC (size _)).
Qed.

Lemma shift_typemap_distr :
  forall f d c n t,
  shift_term d c (typemap f n t) = typemap f n (shift_term d c t).
Proof.
  move => f d c n t; elim: t d c n => /=; congruence.
Qed.

Lemma subst_shifttyp_distr :
  forall n m d c ts t, c <= m ->
  subst_term n (d + m) ts (typemap (shift_typ d) c t) =
  typemap (shift_typ d) c (subst_term n m ts t).
Proof.
  move => n m d c ts t; elim: t n m c => /=.
  - move => v n m c H; rewrite /subst_termv; elimif_omega.
    by rewrite -!shift_typemap_distr shifttyp_add // addn0.
  - by move => tl IHtl tr IHtr n m c H; rewrite IHtl // IHtr.
  - by move => ty t IH n m c H; rewrite IH.
  - by move => t IH ty n m c H; rewrite IH.
  - by move => t IH n m c H; rewrite -addnS IH.
Qed.

Lemma shifttyp_subst_distr :
  forall d c n m ts t,
  typemap (shift_typ d) (m + c) (subst_term n m ts t) =
  subst_term n m (map (typemap (shift_typ d) c) ts)
    (typemap (shift_typ d) (m + c) t).
Proof.
  move => d c n m ts t; elim: t n m => /=; try (move: addSn; congruence).
  move => v n m; elimif_omega.
  by rewrite /subst_termv size_map -!shift_typemap_distr
    -shifttyp_shifttyp_distr // (nth_map' (typemap _ _)).
Qed.

Lemma subst_substtyp_distr :
  forall n m m' tys ts t, m' <= m ->
  subst_term n m ts (typemap (subst_typ^~ tys) m' t) =
  typemap (subst_typ^~ tys) m' (subst_term n (size tys + m) ts t).
Proof.
  move => n m m' tys ts t; elim: t n m m' => /=.
  - move => v n m m' H; elimif_omega.
    rewrite /subst_termv -!shift_typemap_distr typemap_compose.
    f_equal; apply typemap_eq => {v n ts H0} n t.
    by rewrite addn0 subst_shift_cancel_ty ?addKn // leq_addr.
  - by move => tl IHtl tr IHtr n m m' H; rewrite IHtl // IHtr.
  - by move => ty t IH n m m' H; rewrite IH.
  - by move => t IH ty n m m' H; rewrite IH.
  - by move => t IH n m m' H; rewrite IH // addnS.
Qed.

Lemma substtyp_subst_distr :
  forall n m m' tys ts t, m <= m' ->
  typemap (subst_typ^~ tys) m' (subst_term n m ts t) =
  subst_term n m (map (typemap (subst_typ^~ tys) (m' - m)) ts)
    (typemap (subst_typ^~ tys) m' t).
Proof.
  move => n m m' tys ts t; elim: t n m m' => /=.
  - move => v n m m' H; elimif_omega.
    by rewrite /subst_termv size_map -!shift_typemap_distr
      -{1}(subnKC H) -shifttyp_substtyp_distr // (nth_map' (typemap _ _)) /=.
  - by move => tl IHtl tr IHtr n m m' H; rewrite IHtl // IHtr.
  - by move => ty t IH n m m' H; rewrite IH.
  - by move => t IH ty n m m' H; rewrite IH.
  - by move => t IH n m m' H; rewrite IH.
Qed.

Lemma shiftzero : forall n t, shift_term 0 n t = t.
Proof.
  move => n t; elim: t n => /=; try congruence.
  by move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add :
  forall d c d' c' t, c <= c' <= d + c ->
  shift_term d' c' (shift_term d c t) = shift_term (d' + d) c t.
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' H; elimif_omega.
  - move => t1 H t2 H0 c c' H1; f_equal; auto.
  - by move => ty t IH c c' H; rewrite IH // addnS !ltnS.
  - by move => t IH ty c c' H; rewrite IH.
  - by move => t IH c c' H; rewrite IH.
Qed.

Lemma shift_shift_distr :
  forall d c d' c' t,
  c' <= c -> shift_term d' c' (shift_term d c t) =
  shift_term d (d' + c) (shift_term d' c' t).
Proof.
  move => d c d' c' t; elim: t c c' => /=.
  - move => n c c' H; elimif_omega.
  - move => tl IHtl tr IHtr c c' H; f_equal; auto.
  - by move => ty t' IH c c' H; rewrite -addnS IH.
  - by move => t IH ty c c' H; rewrite IH.
  - by move => t IH c c' H; rewrite IH.
Qed.

Lemma subst_shift_distr :
  forall n m d c ts t,
  shift_term d (n + c) (subst_term n m ts t) =
  subst_term n m (map (shift_term d c) ts) (shift_term d (size ts + n + c) t).
Proof.
  move => n m d c ts t; elim: t n m => /=; try (move: addnS addSn; congruence).
  move => v n m; rewrite /subst_termv size_map; elimif_omega.
  - rewrite shift_typemap_distr !nth_default ?size_map /=; try ssromega.
    rewrite (subnAC _ n) subnK; elimif_omega.
  - rewrite shift_typemap_distr -shift_shift_distr // nth_map' /=.
    do 2 f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma shift_subst_distr :
  forall n m d c ts t, c <= n ->
  shift_term d c (subst_term n m ts t) =
  subst_term (d + n) m ts (shift_term d c t).
Proof.
  move => n m d c ts t; elim: t n m c => /=.
  - move => v n m c H; elimif_omega.
    by rewrite /subst_termv shift_typemap_distr
      shift_add ?addn0 // (addnC v) subnDl.
  - move => tl IHl tr IHr n m c H; f_equal; auto.
  - move => ty t IH n m c H; f_equal; rewrite -addnS IH //.
  - by move => t IH ty n m c H; rewrite IH.
  - by move => t IH n m c H; rewrite IH.
Qed.

Lemma subst_shift_cancel :
  forall n m d c ts t, c <= n -> size ts <= d -> n - c <= d - size ts ->
  subst_term n m ts (shift_term d c t) = shift_term (d - size ts) c t.
Proof.
  move => n m d c ts t; elim: t n m c => /=.
  - move => v n m c H H0 H1; elimif_omega.
    rewrite /subst_termv nth_default /=; f_equal; ssromega.
  - by move => tl IHtl tr IHtr n m c H H0 H1; rewrite IHtl // IHtr.
  - by move => ty t IH n m c H H0 H1; rewrite IH.
  - by move => t IH ty n m c H H0 H1; rewrite IH.
  - by move => t IH n m c H H0 H1; rewrite IH.
Qed.

Lemma subst_subst_distr :
  forall n n' m m' xs ys t,
  subst_term (n' + n) (m' + m) xs (subst_term n' m' ys t) =
  subst_term n' m' (map (subst_term n m xs) ys)
    (subst_term (size ys + n' + n) (m' + m) xs t).
Proof.
  move => n n' m m' xs ys t; elim: t n' m' => /=;
    try (move: addSn addnS; congruence).
  move => v n' m'; elimif_omega; rewrite /subst_termv.
  - rewrite -!shift_typemap_distr (subst_shift_cancel n') // size_map
      ?subn0 -?addnA ?addKn ?leq_addr // nth_default /=; last ssromega.
    rewrite /subst_termv subnAC subnK /subnDA; last ssromega.
    rewrite shift_typemap_distr !subnDA; elimif_omega.
  - rewrite -!shift_typemap_distr -shift_subst_distr //
      subst_shifttyp_distr // (nth_map' (subst_term _ _ _)) /= /subst_termv.
    do 2 f_equal; apply nth_equal.
    rewrite size_map; elimif_omega.
Qed.

Lemma subst_app :
  forall n m xs ys t,
  subst_term n m xs (subst_term (size xs + n) m ys t) =
  subst_term n m (xs ++ ys) t.
Proof.
  move => n m xs ys t; elim: t n m => /=; try (move: addnS; congruence).
  move => v n m; elimif_omega; rewrite /subst_termv.
  - rewrite -!shift_typemap_distr subst_shift_cancel //
      ?leq_addr ?subn0 ?addKn // nth_cat size_cat !subnDA (subnAC _ (size xs)).
    f_equal; elimif_omega.
  - rewrite nth_cat; do 2 f_equal; elimif_omega; apply nth_equal; ssromega.
Qed.

Lemma subst_nil : forall n m t, subst_term n m [::] t = t.
Proof.
  move => n m t; elim: t n m => /=; try congruence.
  move => v n m; rewrite /subst_termv nth_nil /= -fun_if; elimif_omega.
Qed.

Lemma redappl :
  forall t1 t1' t2, t1 ->r t1' -> app t1 t2 ->r app t1' t2.
Proof.
  move => t1 t1' t2; elim => // {t1 t1'} t1 t1' t1'' H H0 H1.
  by apply rt1n_trans with (app t1' t2) => //; constructor.
Qed.

Lemma redappr :
  forall t1 t2 t2', t2 ->r t2' -> app t1 t2 ->r app t1 t2'.
Proof.
  move => t1 t2 t2'; elim => // {t2 t2'} t2 t2' t2'' H H0 H1.
  by apply rt1n_trans with (app t1 t2') => //; constructor.
Qed.

Lemma redabs : forall ty t t', t ->r t' -> abs ty t ->r abs ty t'.
Proof.
  move => ty t t'; elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (abs ty t') => //; constructor.
Qed.

Lemma reduapp : forall t t' ty, t ->r t' -> uapp t ty ->r uapp t' ty.
Proof.
  move => t t' ty; elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (uapp t' ty) => //; constructor.
Qed.

Lemma reduabs : forall t t', t ->r t' -> uabs t ->r uabs t'.
Proof.
  move => t t'; elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (uabs t') => //; constructor.
Qed.

Hint Resolve redappl redappr redabs reduapp reduabs.

Module confluence_proof.

Reserved Notation "t ->rp t'" (at level 70, no associativity).

Inductive parred : relation term :=
  | parredfst  : forall ty t1 t1' t2 t2', t1 ->rp t1' -> t2 ->rp t2' ->
                 app (abs ty t1) t2 ->rp subst_term 0 0 [:: t2'] t1'
  | parredsnd  : forall t t' ty, t ->rp t' ->
                 uapp (uabs t) ty ->rp typemap (subst_typ^~ [:: ty]) 0 t'
  | parredvar  : forall n, var n ->rp var n
  | parredapp  : forall t1 t1' t2 t2',
                 t1 ->rp t1' -> t2 ->rp t2' -> app t1 t2 ->rp app t1' t2'
  | parredabs  : forall ty t t', t ->rp t' -> abs ty t ->rp abs ty t'
  | parreduapp : forall t t' ty, t ->rp t' -> uapp t ty ->rp uapp t' ty
  | parreduabs : forall t t', t ->rp t' -> uabs t ->rp uabs t'
  where "t ->rp t'" := (parred t t').

Fixpoint reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs ty t1) t2 =>
      subst_term 0 0 [:: reduce_all_redex t2] (reduce_all_redex t1)
    | app t1 t2 => app (reduce_all_redex t1) (reduce_all_redex t2)
    | abs ty t' => abs ty (reduce_all_redex t')
    | uapp (uabs t) ty =>
      typemap (subst_typ^~ [:: ty]) 0 (reduce_all_redex t)
    | uapp t ty => uapp (reduce_all_redex t) ty
    | uabs t => uabs (reduce_all_redex t)
  end.

Lemma parred_refl : forall t, parred t t.
Proof.
  by elim; constructor.
Qed.

Hint Resolve
  parredfst parredsnd parredvar parredapp parredabs parreduapp parreduabs
  parred_refl.

Lemma betared1_in_parred : inclusion reduction1 parred.
Proof.
  by apply reduction1_ind; constructor.
Qed.

Lemma parred_in_betared : inclusion parred reduction.
Proof.
  apply parred_ind => //; auto.
  - move => ty t1 t1' t2 t2' H H0 H1 H2.
    apply rtc_trans' with (app (abs ty t1') t2); auto.
    apply rtc_trans' with (app (abs ty t1') t2'); auto.
    by apply rtc_step.
  - move => t t' ty H H0.
    apply rtc_trans' with (uapp (uabs t') ty); auto.
    by apply rtc_step.
  - move => t1 t1' t2 t2' H H0 H1 H2; apply rtc_trans' with (app t1 t2'); auto.
Qed.

Lemma shift_parred :
  forall t t' d c, t ->rp t' -> shift_term d c t ->rp shift_term d c t'.
Proof.
  move => t t' d c H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _ _) => //=; try by constructor.
  - by move => ty t1 t1' t2 t2' H H0 H1 H2 d c;
      rewrite (subst_shift_distr 0) /= !add1n; auto.
  - by move => t t' ty H H0 d c; rewrite shift_typemap_distr; auto.
Qed.

Lemma shifttyp_parred :
  forall t t' d c,
  t ->rp t' -> typemap (shift_typ d) c t ->rp typemap (shift_typ d) c t'.
Proof.
  move => t t' d c H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _ _) => /=; auto.
  - by move => ty t1 t1' t2 t2' H H0 H1 H2 d c;
      rewrite (shifttyp_subst_distr d c 0 0) add0n /=; auto.
  - by move => t t' ty H H0 n m;
      rewrite -{3}(add0n m) substtyp_shifttyp_distr /= 2!add1n; auto.
Qed.

Lemma substtyp_parred :
  forall n tys t t', t ->rp t' ->
  typemap (subst_typ^~ tys) n t ->rp typemap (subst_typ^~ tys) n t'.
Proof.
  move => n tys t t' H; move: t t' H n.
  refine (parred_ind _ _ _ _ _ _ _ _) => /=; auto.
  - by move => ty t1 t1' t2 t2' H H0 H1 H2 n;
      rewrite substtyp_subst_distr //= subn0; auto.
  - by move => t t' ty H H0 n;
      rewrite -{3}(add0n n) substtyp_substtyp_distr /= 2!add1n; auto.
Qed.

Lemma subst_parred :
  forall n m ps t t', Forall (prod_curry parred) ps -> t ->rp t' ->
  subst_term n m [seq fst p | p <- ps] t ->rp
  subst_term n m [seq snd p | p <- ps] t'.
Proof.
  move => n m ps t t' H H0; move: t t' H0 n m.
  refine (parred_ind _ _ _ _ _ _ _ _) => /=; auto.
  - by move => ty tl tl' tr tr' H0 H1 H2 H3 n m;
      rewrite (subst_subst_distr n 0 m 0) /= 2!add1n add0n; auto.
  - by move => t t' ty H0 H1 n m; rewrite subst_substtyp_distr //=; auto.
  - move => v n m.
    rewrite /subst_termv !size_map.
    case: ifP => // _.
    elim: ps H (v - n) => //= {v} [[t t']] ts IH [H H0] [| v] //=.
    - by apply shifttyp_parred, shift_parred.
    - by rewrite subSS; apply IH.
Qed.

Lemma parred_all_lemma : forall t t', t ->rp t' -> t' ->rp reduce_all_redex t.
Proof with auto.
  fix 3 => t t' H; inversion H; subst => {H} /=; try by constructor; auto.
  - apply (subst_parred 0 0 [:: (t2', reduce_all_redex t2)]) => /=; auto.
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
  apply (rtc_confluent' parred
    betared1_in_parred parred_in_betared parred_confluent).
Qed.

End confluence_proof.
