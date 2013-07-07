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

Inductive typing : context typ -> term -> typ -> Prop :=
  | typvar ctx n ty :
    ctxindex ctx n ty -> typing ctx (var n) ty
  | typapp ctx t1 t2 ty1 ty2 :
    typing ctx t1 (tyfun ty1 ty2) -> typing ctx t2 ty1 ->
    typing ctx (app t1 t2) ty2
  | typabs ctx t ty1 ty2 :
    typing (some ty1 :: ctx) t ty2 -> typing ctx (abs ty1 t) (tyfun ty1 ty2)
  | typuapp ctx t ty1 ty2 :
    typing ctx t (tyabs ty1) ->
    typing ctx (uapp t ty2) (subst_typ 0 [:: ty2] ty1)
  | typuabs ctx t ty :
    typing (ctxmap (shift_typ 1 0) ctx) t ty -> typing ctx (uabs t) (tyabs ty).

Reserved Notation "t ->r1 t'" (at level 70, no associativity).

Inductive reduction1 : relation term :=
  | red1fst ty t1 t2   : app (abs ty t1) t2 ->r1 subst_term 0 0 [:: t2] t1
  | red1snd t ty       : uapp (uabs t) ty ->r1 typemap (subst_typ^~ [:: ty]) 0 t
  | red1appl t1 t1' t2 : t1 ->r1 t1' -> app t1 t2 ->r1 app t1' t2
  | red1appr t1 t2 t2' : t2 ->r1 t2' -> app t1 t2 ->r1 app t1 t2'
  | red1abs ty t t'    : t ->r1 t' -> abs ty t ->r1 abs ty t'
  | red1uapp t t' ty   : t ->r1 t' -> uapp t ty ->r1 uapp t' ty
  | red1uabs t t'      : t ->r1 t' -> uabs t ->r1 uabs t'
  where "t ->r1 t'" := (reduction1 t t').

Notation reduction := [* reduction1].
Infix "->r" := reduction (at level 70, no associativity).

Hint Constructors typing reduction1.

Lemma shift_zero_ty n t : shift_typ 0 n t = t.
Proof.
  by elim: t n => /=; try congruence; move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add_ty d c d' c' t :
  c <= c' <= d + c ->
  shift_typ d' c' (shift_typ d c t) = shift_typ (d' + d) c t.
Proof.
  case/andP; elimleq; rewrite leq_add2r; elimleq;
    elim: t c c' => /=; try (move: addnS; congruence); move => *; elimif_omega.
Qed.

Lemma shift_shift_distr_ty d c d' c' t :
  c' <= c ->
  shift_typ d' c' (shift_typ d c t) = shift_typ d (d' + c) (shift_typ d' c' t).
Proof.
  elimleq; elim: t c c' => /=;
    try (move: addnS; congruence); move => *; elimif_omega.
Qed.

Lemma shift_subst_distr_ty n d c ts t :
  c <= n ->
  shift_typ d c (subst_typ n ts t) = subst_typ (d + n) ts (shift_typ d c t).
Proof.
  elimleq; elim: t n c => /=;
    try (move: addnS; congruence); move => v n c; elimif_omega.
  by rewrite /subst_typv shift_add_ty ?addn0 ?leq_addl // !subnDA addnK.
Qed.

Lemma subst_shift_distr_ty n d c ts t :
  shift_typ d (n + c) (subst_typ n ts t) =
  subst_typ n (map (shift_typ d c) ts) (shift_typ d (size ts + n + c) t).
Proof.
  elim: t n => /=; try (move: addnS addSn; congruence);
    move => m n; rewrite /subst_typv size_map; elimif_omega.
  - rewrite !nth_default ?size_map /=; try ssromega.
    rewrite (subnAC _ n) subnK; elimif_omega.
  - rewrite -shift_shift_distr_ty // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_shift_cancel_ty n d c ts t :
  c <= n -> size ts + n <= d + c ->
  subst_typ n ts (shift_typ d c t) = shift_typ (d - size ts) c t.
Proof.
  elimleq; rewrite addnA leq_add2r; elimleq.
  elim: t n c => /=; try (move: addnS; congruence); move => v n c;
    elimif_omega; rewrite /subst_typv nth_default /=; f_equal; ssromega.
Qed.

Lemma subst_subst_distr_ty n m xs ys t :
  subst_typ (m + n) xs (subst_typ m ys t) =
  subst_typ m (map (subst_typ n xs) ys) (subst_typ (size ys + m + n) xs t).
Proof.
  elim: t m => /=; try (move: addnS addSn; congruence);
    move => v m; elimif_omega; rewrite /subst_typv.
  - rewrite (subst_shift_cancel_ty m) // size_map
      ?addn0 ?leq_addr // -{1}addnA addKn nth_default /=; last ssromega.
    rewrite /subst_typv subnAC subnK ?subnDA; elimif_omega.
  - rewrite -shift_subst_distr_ty // size_map nth_map'; f_equal.
    apply nth_equal; rewrite size_map /=; elimif_omega.
Qed.

Lemma subst_app_ty n xs ys t :
  subst_typ n xs (subst_typ (size xs + n) ys t) = subst_typ n (xs ++ ys) t.
Proof.
  elim: t n => /=; try (move: addnS; congruence);
    move => v n; elimif_omega; rewrite /subst_typv.
  - rewrite subst_shift_cancel_ty ?addn0 //
      size_cat nth_cat !subnDA addKn (subnAC _ (size xs)); elimif_omega.
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
  - by move => tl IHtl tr IHtr n m; rewrite IHtl IHtr.
  - by move => ty t IH n m; rewrite IH.
  - by move => t IH ty n m; rewrite IH.
  - move => t IH n m; rewrite {}IH; f_equal.
    elim: t (0) => //=; move: addSnnS; congruence.
Qed.

Lemma typemap_eq' f g n m t :
  (forall o t, f (o + n) t = g (o + m) t) -> typemap f n t = typemap g m t.
Proof.
  move => H; elim: t n m H => //=.
  - by move => tl IHtl tr IHtr n m H; f_equal; auto.
  - by move => ty t IH n m H; f_equal; auto; rewrite -(add0n n) -(add0n m).
  - by move => t IH ty n m H; f_equal; auto; rewrite -(add0n n) -(add0n m).
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
  c <= c' <= d + c ->
  typemap (shift_typ d') c' (typemap (shift_typ d) c t) =
  typemap (shift_typ (d' + d)) c t.
Proof.
  rewrite typemap_compose => H; apply typemap_eq' => {t} n t.
  by rewrite addn0 shift_add_ty // addnCA !leq_add2l.
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
  typemap (shift_typ d) (n + c) (typemap (subst_typ^~ ts) n t) =
  typemap (subst_typ^~ (map (shift_typ d c) ts)) n
    (typemap (shift_typ d) (size ts + n + c) t).
Proof.
  rewrite !typemap_compose; apply typemap_eq => {t} n' t.
  by rewrite addnA subst_shift_distr_ty !addnA (addnC (size _)).
Qed.

Lemma substtyp_substtyp_distr n m xs ys t :
  typemap (subst_typ^~ xs) (m + n) (typemap (subst_typ^~ ys) m t) =
  typemap (subst_typ^~ (map (subst_typ n xs) ys)) m
    (typemap (subst_typ^~ xs) (size ys + m + n) t).
Proof.
  rewrite !typemap_compose; apply typemap_eq => {t} n' t.
  by rewrite addnA subst_subst_distr_ty !addnA (addnC (size _)).
Qed.

Lemma shift_typemap_distr f d c n t :
  shift_term d c (typemap f n t) = typemap f n (shift_term d c t).
Proof.
  elim: t d c n => /=; congruence.
Qed.

Lemma subst_shifttyp_distr n m d c ts t :
  c <= m ->
  subst_term n (d + m) ts (typemap (shift_typ d) c t) =
  typemap (shift_typ d) c (subst_term n m ts t).
Proof.
  elimleq; elim: t n m c => /=; try (move: addnS; congruence);
    move => v n m c; elimif_omega.
  by rewrite /subst_termv -!shift_typemap_distr shifttyp_add // addn0 leq_addl.
Qed.

Lemma shifttyp_subst_distr d c n m ts t :
  typemap (shift_typ d) (m + c) (subst_term n m ts t) =
  subst_term n m (map (typemap (shift_typ d) c) ts)
    (typemap (shift_typ d) (m + c) t).
Proof.
  elim: t n m => /=; try (move: addSn; congruence); move => v n m; elimif_omega.
  by rewrite /subst_termv size_map -!shift_typemap_distr
    -shifttyp_shifttyp_distr // (nth_map' (typemap _ _)).
Qed.

Lemma subst_substtyp_distr n m m' tys ts t :
  m' <= m ->
  subst_term n m ts (typemap (subst_typ^~ tys) m' t) =
  typemap (subst_typ^~ tys) m' (subst_term n (size tys + m) ts t).
Proof.
  elimleq; elim: t n m m' => /=; try (move: addnS; congruence);
    move => v n m m'; elimif_omega.
  rewrite /subst_termv -!shift_typemap_distr typemap_compose.
  f_equal; apply typemap_eq => {v n ts H} n t.
  rewrite addn0 subst_shift_cancel_ty ?addKn //; ssromega.
Qed.

Lemma substtyp_subst_distr n m m' tys ts t :
  m <= m' ->
  typemap (subst_typ^~ tys) m' (subst_term n m ts t) =
  subst_term n m (map (typemap (subst_typ^~ tys) (m' - m)) ts)
    (typemap (subst_typ^~ tys) m' t).
Proof.
  elimleq; elim: t n m m' => /=; try (move: addnS; congruence);
    move => v n m m'; elimif_omega.
  by rewrite /subst_termv size_map -!shift_typemap_distr
    addnC -shifttyp_substtyp_distr // (nth_map' (typemap _ _)) /=.
Qed.

Lemma shift_zero n t : shift_term 0 n t = t.
Proof.
  by elim: t n => /=; try congruence; move => m n; rewrite addn0 if_same.
Qed.

Lemma shift_add d c d' c' t :
  c <= c' <= d + c ->
  shift_term d' c' (shift_term d c t) = shift_term (d' + d) c t.
Proof.
  case/andP; elimleq; rewrite leq_add2r; elimleq;
    elim: t c c' => /=; try (move: addnS; congruence); move => *; elimif_omega.
Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <= c ->
  shift_term d' c' (shift_term d c t) =
  shift_term d (d' + c) (shift_term d' c' t).
Proof.
  elimleq; elim: t c c' => /=; try (move: addnS; congruence);
    move => v c c'; elimif_omega.
Qed.

Lemma subst_shift_distr n m d c ts t :
  shift_term d (n + c) (subst_term n m ts t) =
  subst_term n m (map (shift_term d c) ts) (shift_term d (size ts + n + c) t).
Proof.
  elim: t n m => /=; try (move: addnS addSn; congruence);
    move => v n m; rewrite /subst_termv size_map; elimif_omega.
  - rewrite shift_typemap_distr !nth_default ?size_map /=; try ssromega.
    rewrite (subnAC _ n) subnK; elimif_omega.
  - rewrite shift_typemap_distr -shift_shift_distr // nth_map' /=.
    do 2 f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma shift_subst_distr n m d c ts t :
  c <= n ->
  shift_term d c (subst_term n m ts t) =
  subst_term (d + n) m ts (shift_term d c t).
Proof.
  elimleq; elim: t n m c => /=; try (move: addnS; congruence);
    move => v n m c; elimif_omega.
  by rewrite /subst_termv shift_typemap_distr
    (subnDA d) addnK shift_add // addn0 leq_addl.
Qed.

Lemma subst_shift_cancel n m d c ts t :
  c <= n -> size ts + n <= d + c ->
  subst_term n m ts (shift_term d c t) = shift_term (d - size ts) c t.
Proof.
  elimleq; rewrite addnA leq_add2r; elimleq; elim: t n m c => /=;
    try (move: addnS; congruence); move => v n m c; elimif_omega.
  rewrite /subst_termv nth_default /=; f_equal; ssromega.
Qed.

Lemma subst_subst_distr n n' m m' xs ys t :
  subst_term (n' + n) (m' + m) xs (subst_term n' m' ys t) =
  subst_term n' m' (map (subst_term n m xs) ys)
    (subst_term (size ys + n' + n) (m' + m) xs t).
Proof.
  elim: t n' m' => /=; try (move: addSn addnS; congruence);
    move => v n' m'; elimif_omega; rewrite /subst_termv.
  - rewrite -!shift_typemap_distr (subst_shift_cancel n') // size_map
      ?addn0 ?leq_addr // nth_default /= /subst_termv; elimif_omega.
    by rewrite shift_typemap_distr -addnA addKn subnDA addnK addnCA !subnDA.
  - rewrite -!shift_typemap_distr -shift_subst_distr //
      subst_shifttyp_distr // (nth_map' (subst_term _ _ _)) /= /subst_termv.
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
  by rewrite addn0 shift_add_ty ?leqnn ?leq_addl // addnC.
Qed.

Lemma redappl t1 t1' t2 : t1 ->r t1' -> app t1 t2 ->r app t1' t2.
Proof.
  elim => // {t1 t1'} t1 t1' t1'' H H0 H1.
  by apply rt1n_trans with (app t1' t2) => //; constructor.
Qed.

Lemma redappr t1 t2 t2' : t2 ->r t2' -> app t1 t2 ->r app t1 t2'.
Proof.
  elim => // {t2 t2'} t2 t2' t2'' H H0 H1.
  by apply rt1n_trans with (app t1 t2') => //; constructor.
Qed.

Lemma redabs ty t t' : t ->r t' -> abs ty t ->r abs ty t'.
Proof.
  elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (abs ty t') => //; constructor.
Qed.

Lemma reduapp t t' ty : t ->r t' -> uapp t ty ->r uapp t' ty.
Proof.
  elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (uapp t' ty) => //; constructor.
Qed.

Lemma reduabs t t' : t ->r t' -> uabs t ->r uabs t'.
Proof.
  elim => // {t t'} t t' t'' H H0 H1.
  by apply rt1n_trans with (uabs t') => //; constructor.
Qed.

Hint Resolve redappl redappr redabs reduapp reduabs.

Lemma typvar_seqindex ctx n ty : typing ctx (var n) ty <-> ctxindex ctx n ty.
Proof.
  split => H.
  - by inversion H.
  - by constructor.
Qed.

Module confluence_proof.

Reserved Notation "t ->rp t'" (at level 70, no associativity).

Inductive parred : relation term :=
  | parredfst ty t1 t1' t2 t2' :
    t1 ->rp t1' -> t2 ->rp t2' ->
    app (abs ty t1) t2 ->rp subst_term 0 0 [:: t2'] t1'
  | parredsnd  t t' ty :
    t ->rp t' -> uapp (uabs t) ty ->rp typemap (subst_typ^~ [:: ty]) 0 t'
  | parredvar n : var n ->rp var n
  | parredapp t1 t1' t2 t2' :
    t1 ->rp t1' -> t2 ->rp t2' -> app t1 t2 ->rp app t1' t2'
  | parredabs ty t t' : t ->rp t' -> abs ty t ->rp abs ty t'
  | parreduapp t t' ty : t ->rp t' -> uapp t ty ->rp uapp t' ty
  | parreduabs t t' : t ->rp t' -> uabs t ->rp uabs t'
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
  - move => ty t1 t1' t2 t2' H H0 H1 H2.
    apply rtc_trans' with (app (abs ty t1') t2); auto.
    apply rtc_trans' with (app (abs ty t1') t2'); auto.
    by apply rtc_step.
  - move => t t' ty H H0.
    apply rtc_trans' with (uapp (uabs t') ty); auto.
    by apply rtc_step.
  - move => t1 t1' t2 t2' H H0 H1 H2; apply rtc_trans' with (app t1 t2'); auto.
Qed.

Lemma shift_parred t t' d c :
  t ->rp t' -> shift_term d c t ->rp shift_term d c t'.
Proof.
  move => H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _ _) => //=; try by constructor.
  - by move => ty t1 t1' t2 t2' H H0 H1 H2 d c;
      rewrite (subst_shift_distr 0) /= !add1n; auto.
  - by move => t t' ty H H0 d c; rewrite shift_typemap_distr; auto.
Qed.

Lemma shifttyp_parred t t' d c :
  t ->rp t' -> typemap (shift_typ d) c t ->rp typemap (shift_typ d) c t'.
Proof.
  move => H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _ _) => /=; auto.
  - by move => ty t1 t1' t2 t2' H H0 H1 H2 d c;
      rewrite (shifttyp_subst_distr d c 0 0) add0n /=; auto.
  - by move => t t' ty H H0 n m;
      rewrite -{3}(add0n m) substtyp_shifttyp_distr /= 2!add1n; auto.
Qed.

Lemma substtyp_parred n tys t t' :
  t ->rp t' ->
  typemap (subst_typ^~ tys) n t ->rp typemap (subst_typ^~ tys) n t'.
Proof.
  move => H; move: t t' H n.
  refine (parred_ind _ _ _ _ _ _ _ _) => /=; auto.
  - by move => ty t1 t1' t2 t2' H H0 H1 H2 n;
      rewrite substtyp_subst_distr //= subn0; auto.
  - by move => t t' ty H H0 n;
      rewrite -{3}(add0n n) substtyp_substtyp_distr /= 2!add1n; auto.
Qed.

Lemma subst_parred n m ps t t' :
  Forall (prod_curry parred) ps -> t ->rp t' ->
  subst_term n m [seq fst p | p <- ps] t ->rp
  subst_term n m [seq snd p | p <- ps] t'.
Proof.
  move => H H0; move: t t' H0 n m.
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

Lemma parred_all_lemma t t' : t ->rp t' -> t' ->rp reduce_all_redex t.
Proof with auto.
  move: t t'; fix 3 => t t' H; inversion H; subst => {H} /=; auto.
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

Module subject_reduction_proof.

Lemma ctxleq_preserves_typing ctx1 ctx2 t ty :
  ctx1 <=c ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  move => H H0; move: ctx1 t ty H0 ctx2 H.
  refine (typing_ind _ _ _ _ _ _); eauto.
  by move => ctx t ty1 ty2 _ H ctx2 H0; constructor; apply H; case.
Qed.

Lemma shifttyp_preserves_typing d c ctx t ty :
  typing ctx t ty ->
  typing (ctxmap (shift_typ d c) ctx)
    (typemap (shift_typ d) c t) (shift_typ d c ty).
Proof.
  move => H; move: ctx t ty H d c.
  refine (typing_ind _ _ _ _ _ _) => /=.
  - by move => ctx n ty H d c; apply typvar, ctxindex_map.
  - move => ctx t1 t2 ty1 ty2 _ H _ H0 d c.
    by apply typapp with (shift_typ d c ty1); auto.
  - by move => ctx t ty1 ty2 _ H d c; constructor; auto.
  - move => ctx t ty1 ty2 _ H d c.
    rewrite -{4}(add0n c) subst_shift_distr_ty /=.
    by constructor; rewrite !add1n; apply H.
  - move => ctx t ty _ H d c.
    constructor; move: {H} (H d c.+1).
    rewrite -!map_comp /funcomp.
    set ctx1 := map _ _.
    set ctx2 := map _ _.
    have -> //: ctx1 = ctx2.
      rewrite {}/ctx1 {}/ctx2.
      elim: {t ty} ctx => //= [[ty |]] ctx -> //=.
      by do 2 f_equal; rewrite (shift_shift_distr_ty d c).
Qed.

Lemma substtyp_preserves_typing n tys ctx t ty :
  typing ctx t ty ->
  typing (ctxmap (subst_typ n tys) ctx)
    (typemap (subst_typ^~ tys) n t) (subst_typ n tys ty).
Proof.
  move => H; move: ctx t ty H n.
  refine (typing_ind _ _ _ _ _ _) => /=.
  - move => ctx n ty H v; constructor.
    by rewrite -(nth_map' (omap (subst_typ v tys)) None) -H.
  - move => ctx t1 t2 ty1 ty2 _ H _ H0 n.
    by apply typapp with (subst_typ n tys ty1); auto.
  - by constructor.
  - move => ctx t ty1 ty2 _ H n.
    rewrite -{4}(add0n n) subst_subst_distr_ty /= !add1n.
    by constructor.
  - move => ctx t ty _ H n; constructor.
    move: {H} (H n.+1); apply ssr_congr_arrow; f_equal; first by move ->.
    elim: ctx {t ty} => //= [[ty |]] ctx -> //=.
    by rewrite shift_subst_distr_ty.
Qed.

Lemma subject_shift t ty c ctx1 ctx2 :
  typing ctx1 t ty ->
  typing (ctxinsert ctx2 ctx1 c) (shift_term (size ctx2) c t) ty.
Proof.
  move => H; move: ctx1 t ty H c ctx2.
  refine (typing_ind _ _ _ _ _ _) => /=; auto.
  - move => ctx1 n ty H c ctx2; constructor.
    rewrite {}H nth_ctxinsert; elimif_omega.
  - by move => ctx1 t1 t2 ty1 ty2 _ H _ H0 c ctx2; apply typapp with ty1; auto.
  - by move => ctx1 t ty1 ty2 _ H c ctx2; apply typabs, (H c.+1).
  - move => ctx1 t ty _ H c ctx2; constructor.
    by rewrite map_ctxinsert -(size_map (omap (shift_typ 1 0)) ctx2).
Qed.

Lemma subject_subst t ty n ctx ctx' :
  Forall (fun p => typing (drop n ctx) p.1 p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (subst_term n 0 [seq p.1 | p <- ctx'] t) ty.
Proof.
  move => H.
  move: {2 3}(ctxinsert _ _ _)
    (erefl (ctxinsert [seq Some p.2 | p <- ctx'] ctx n)) => ctx'' H0 H1.
  move: ctx'' t ty H1 n ctx ctx' H H0.
  refine (typing_ind _ _ _ _ _ _) => /=.
  - move => ? v ty H n ctx ctx' H0 ?; subst; move: H.
    rewrite /subst_termv nth_ctxinsert !size_map; elimif_omega.
    - by constructor.
    - move: H {H1 H2}; elimleq.
      elim: ctx' v H0 => //= [| [t ty'] ctx' IH] [| v] //= [H H0].
      - case => {H0 IH} H0; subst.
        rewrite shifttyp_zero.
        move/(subject_shift 0 (ctxinsert [::] (take n ctx) n)): H.
        rewrite size_ctxinsert size_take minnC minKn /= add0n.
        apply ctxleq_preserves_typing.
        rewrite /ctxinsert take0 drop0 take_minn minnn
          drop_take_nil size_take -!catA /= -{4}(cat_take_drop n ctx).
        apply ctxleq_app => //; case/orP: (leq_total n (size ctx)).
        - by move/minn_idPl => ->; rewrite subnn.
        - by move => H m x; rewrite (drop_oversize H) cats0 nth_nseq if_same.
      - by rewrite subSS; apply IH.
    - move: H H1 {H2}; elimleq; move/negbT;
        rewrite -leqNgt addnC leq_add2r => H H1.
      rewrite nth_default ?size_map //=.
      constructor; rewrite H1; f_equal; ssromega.
  - move => ? t1 t2 ty1 ty2 _ H0 _ H1 n ctx ctx' H ?; subst.
    by apply typapp with ty1; auto.
  - move => ? t ty1 ty2 _ H n ctx ctx' H0 ?; subst.
    by constructor; apply H.
  - move => ? t ty1 ty2 _ H n ctx ctx' H0 ?; subst.
    by constructor; apply H.
  - move => ctx'' t ty _ H n ctx ctx' H0 H1; subst.
    constructor; rewrite -{2}(addn0 1) -subst_shifttyp_app.
    set ctx'' := (map _ (map _ _)).
    have ->: ctx'' = [seq p.1 | p <-
        [seq (typemap (shift_typ 1) 0 p.1, shift_typ 1 0 p.2) | p <- ctx']]
      by rewrite /ctx'' -!map_comp /funcomp /=.
    apply H => {ctx'' H}.
    - apply Forall_map; move: H0; apply Forall_impl => {t ty ctx'} [[t ty]] /=.
      rewrite -map_drop; apply shifttyp_preserves_typing.
    - by rewrite map_ctxinsert -!map_comp.
Qed.

Theorem subject_reduction ctx t t' ty :
  t ->r1 t' -> typing ctx t ty -> typing ctx t' ty.
Proof.
  move => H; move: t t' H ctx ty.
  refine (reduction1_ind _ _ _ _ _ _ _ _) => /=.
  - move => ty' t1 t2 ctx ty H.
    inversion H; subst; inversion H3; subst => {H H3}.
    apply (subject_subst 0 ctx [:: (t2, ty1)]) => /=.
    - by rewrite drop0.
    - by rewrite /ctxinsert take0 drop0.
  - move => t ty' ctx ty H.
    inversion H; subst => {H}; inversion H4; subst => {H4}.
    move: {H2} (substtyp_preserves_typing 0 [:: ty'] H2).
    apply ssr_congr_arrow; f_equal; first by move ->.
    elim: ctx {t ty1} => //= [[ty |]] ctx {1}-> //=.
    by rewrite subst_shift_cancel_ty //= subnn shift_zero_ty.
  - move => t1 t1' t2 H IH ctx ty H0; inversion H0; subst; eauto.
  - move => t1 t2 t2' H IH ctx ty H0; inversion H0; subst; eauto.
  - move => ty' t t' H IH ctx ty H0; inversion H0; subst; eauto.
  - move => t t' ty' H IH ctx ty H0; inversion H0; subst; eauto.
  - move => t t' H IH ctx ty H0; inversion H0; subst; eauto.
Qed.

End subject_reduction_proof.

Module strong_normalization_proof.

Import subject_reduction_proof.

Notation SNorm t := (Acc (fun x y => reduction1 y x) t).



End strong_normalization_proof.
