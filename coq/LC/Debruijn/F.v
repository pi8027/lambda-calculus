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
  move => t1 t2; apply: (iffP idP) => [| <-].
  - by elim: t1 t2 => [n | t1l IHt1l t1r IHt1r | t1 IHt1]
      [// m /eqP -> | //= t2l t2r /andP [] /IHt1l -> /IHt1r -> |
       // t2 /IHt1 ->].
  - by elim: t1 => //= t ->.
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
  move => t1 t2; apply: (iffP idP) => [| <-].
  - by elim: t1 t2 =>
      [n | t1l IHt1l t1r IHt1r ty1 | t1 IHt1 | t1 IHt1 ty1l ty1r | t1 IHt1]
      [// m /eqP -> | //= t2l t2r ty2 /and3P [] /IHt1l -> /IHt1r -> /eqP -> |
       // t2 /IHt1 -> | //= t2 ty2l ty2r /and3P [] /IHt1 -> /eqP -> /eqP -> |
       // t2 /IHt1 -> ].
  - by elim: t1 => //= [t -> t' -> | t ->] *; rewrite !eqxx.
Defined.

Canonical term_eqMixin := EqMixin eqtermP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Fixpoint shift_typ d c t :=
  match t with
    | tyvar n => tyvar (if c <= n then n + d else n)
    | tl :->: tr => shift_typ d c tl :->: shift_typ d c tr
    | tyabs t => tyabs (shift_typ d c.+1 t)
  end.

Notation subst_typv ts m n :=
  (shift_typ n 0 (nth (tyvar (m - n - size ts)) ts (m - n))) (only parsing).

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

Notation subst_termv ts m n n' :=
  (typemap (shift_typ n') 0
    (shift_term n 0 (nth (var (m - n - size ts)) ts (m - n)))) (only parsing).

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

Notation SN := (Acc (fun x y => reduction1 y x)).

Definition neutral (t : term) : bool :=
  match t with abs _ => false | uabs _ => false | _ => true end.

Ltac congruence' := move => /=; try (move: addSn addnS; congruence).

Lemma shift_zero_ty n t : shift_typ 0 n t = t.
Proof. by elim: t n; congruence' => m n; rewrite addn0 if_same. Qed.

Lemma shift_add_ty d c d' c' t :
  c <= c' <= c + d ->
  shift_typ d' c' (shift_typ d c t) = shift_typ (d' + d) c t.
Proof. case/andP; do 2 elimleq; elim: t c; congruence' => *; elimif_omega. Qed.

Lemma shift_shift_distr_ty d c d' c' t :
  c' <= c ->
  shift_typ d' c' (shift_typ d c t) = shift_typ d (d' + c) (shift_typ d' c' t).
Proof. elimleq; elim: t c'; congruence' => *; elimif_omega. Qed.

Lemma shift_subst_distr_ty n d c ts t :
  c <= n ->
  shift_typ d c (subst_typ n ts t) = subst_typ (d + n) ts (shift_typ d c t).
Proof.
  elimleq; elim: t n c; congruence' => v n c;
    elimif_omega; rewrite shift_add_ty; elimif_omega.
Qed.

Lemma subst_shift_distr_ty n d c ts t :
  n <= c ->
  shift_typ d c (subst_typ n ts t) =
  subst_typ n (map (shift_typ d (c - n)) ts) (shift_typ d (size ts + c) t).
Proof.
  elimleq; elim: t n; congruence' => v n; rewrite size_map; elimif_omega.
  - rewrite !nth_default ?size_map /=; elimif_omega.
  - rewrite -shift_shift_distr_ty // nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_nil_ty n t : subst_typ n [::] t = t.
Proof. elim: t n; congruence' => v n; rewrite nth_nil /=; elimif_omega. Qed.

Lemma subst_shift_cancel_ty1 n d c ts t :
  c <= n ->
  subst_typ n ts (shift_typ d c t) =
  subst_typ n (drop (c + d - n) ts)
    (shift_typ (d - minn (c + d - n) (size ts)) c t).
Proof.
  elimleq; elim: t c; congruence' => v c; rewrite size_drop nth_drop.
  case (leqP' d n); elimif_omega; elimleq.
  case (leqP' d.+1 (size ts)) => H0; elimif_omega.
  rewrite !nth_default //; ssromega.
Qed.

Lemma subst_shift_cancel_ty2 n d c ts t :
  c <= n -> size ts + n <= d + c ->
  subst_typ n ts (shift_typ d c t) = shift_typ (d - size ts) c t.
Proof.
  move => H H0; rewrite subst_shift_cancel_ty1 ?drop_oversize ?subst_nil_ty;
    f_equal; ssromega.
Qed.

Lemma subst_shift_cancel_ty3 n d c ts t :
  n <= c <= n + size ts ->
  subst_typ n ts (shift_typ d c t) =
  subst_typ n (take (c - n) ts ++ drop (c + d - n) ts)
    (shift_typ (c + d - (n + size ts)) c t).
Proof.
  case/andP; elimleq => H; elim: t n; congruence' => v n.
  rewrite size_cat size_take size_drop nth_cat nth_drop
           size_take (minn_idPl H); elimif_omega; f_equal.
  - case (leqP' (c + d) (size ts)) => H0.
    + rewrite addn0; f_equal; first f_equal; ssromega.
    + rewrite subn0 !nth_default; first f_equal; ssromega.
  - rewrite nth_take; first apply nth_equal; elimif_omega.
Qed.

Lemma subst_shift_cancel_ty4 n c ts ts' t t' :
  c <= size ts ->
  subst_typ n (insert ts' ts t' c) (shift_typ (size ts') (n + c) t) =
  subst_typ n ts t.
Proof.
  rewrite subst_shift_cancel_ty3 ?size_insert; last ssromega.
  rewrite -addnA subnDA !addKn subnDA addnK take_insert drop_insert /leq.
  move/eqP => -> /=;
    rewrite cats0 cat_take_drop (_ : _ - _ = 0) ?shift_zero_ty //; ssromega.
Qed.

Lemma subst_app_ty n xs ys t :
  subst_typ n xs (subst_typ (size xs + n) ys t) = subst_typ n (xs ++ ys) t.
Proof.
  elim: t n; congruence' => v n; rewrite size_cat nth_cat; elimif_omega.
  rewrite subst_shift_cancel_ty2; elimif_omega.
Qed.

Lemma subst_subst_distr_ty n m xs ys t :
  m <= n ->
  subst_typ n xs (subst_typ m ys t) =
  subst_typ m (map (subst_typ (n - m) xs) ys) (subst_typ (size ys + n) xs t).
Proof.
  elimleq; elim: t m; congruence' => v m; elimif_omega.
  - rewrite (@subst_shift_cancel_ty2 m) ?size_map 1?nth_default //=;
      elimif_omega.
  - rewrite size_map -shift_subst_distr_ty //= nth_map' /=.
    f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_subst_compose_ty n m xs ys t :
  m <= size xs ->
  subst_typ n xs (subst_typ (n + m) ys t) =
  subst_typ n (insert (map (subst_typ 0 (drop m xs)) ys) xs 0 m) t.
Proof.
  move => H; elim: t n; congruence' => v n.
  rewrite size_insert nth_insert size_map; elimif_omega.
  - by rewrite (maxn_idPr H) nth_default /= 1?addnCA ?leq_addr //= addKn addnC.
  - rewrite (nth_map (tyvar (v - size ys))) // shift_subst_distr_ty //
            addn0 subst_shift_cancel_ty1 //=; elimif_omega.
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
Proof. move => H; apply typemap_eq' => {t} o; apply H. Qed.

Lemma shifttyp_zero c t : typemap (shift_typ 0) c t = t.
Proof. elim: t c => /=; move: shift_zero_ty; congruence. Qed.

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
Proof. elim: t c n => /=; congruence. Qed.

Lemma subst_shifttyp_distr n m d c ts t :
  c + d <= m ->
  subst_term n m ts (typemap (shift_typ d) c t) =
  typemap (shift_typ d) c (subst_term n (m - d) ts t).
Proof.
  elimleq; elim: t n c; congruence' => v n c; elimif_omega.
  rewrite -!shift_typemap_distr shifttyp_add; elimif_omega.
Qed.

Lemma shifttyp_subst_distr d c n m ts t :
  m <= c ->
  typemap (shift_typ d) c (subst_term n m ts t) =
  subst_term n m (map (typemap (shift_typ d) (c - m)) ts)
    (typemap (shift_typ d) c t).
Proof.
  by elimleq; elim: t n m; congruence' => v n m; elimif_omega;
    rewrite size_map -!shift_typemap_distr -shifttyp_shifttyp_distr // nth_map'.
Qed.

Lemma subst_substtyp_distr n m m' tys ts t :
  m' <= m ->
  subst_term n m ts (typemap (subst_typ^~ tys) m' t) =
  typemap (subst_typ^~ tys) m' (subst_term n (size tys + m) ts t).
Proof.
  elimleq; elim: t n m'; congruence' => v n m'; elimif_omega.
  rewrite -!shift_typemap_distr typemap_compose.
  f_equal; apply typemap_eq => {v n ts} n t.
  rewrite subst_shift_cancel_ty2; f_equal; ssromega.
Qed.

Lemma substtyp_subst_distr n m m' tys ts t :
  m <= m' ->
  typemap (subst_typ^~ tys) m' (subst_term n m ts t) =
  subst_term n m (map (typemap (subst_typ^~ tys) (m' - m)) ts)
    (typemap (subst_typ^~ tys) m' t).
Proof.
  elimleq; elim: t n m; congruence' => v n m; elimif_omega.
  by rewrite size_map -!shift_typemap_distr
             -shifttyp_substtyp_distr // (nth_map' (typemap _ _)).
Qed.

Lemma shift_zero n t : shift_term 0 n t = t.
Proof. by elim: t n => /=; congruence' => m n; rewrite addn0 if_same. Qed.

Lemma shift_add d c d' c' t :
  c <= c' <= c + d ->
  shift_term d' c' (shift_term d c t) = shift_term (d' + d) c t.
Proof. case/andP; do 2 elimleq; elim: t c; congruence' => *; elimif_omega. Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <= c ->
  shift_term d' c' (shift_term d c t) =
  shift_term d (d' + c) (shift_term d' c' t).
Proof. elimleq; elim: t c'; congruence' => v c'; elimif_omega. Qed.

Lemma subst_shift_distr n m d c ts t :
  n <= c ->
  shift_term d c (subst_term n m ts t) =
  subst_term n m (map (shift_term d (c - n)) ts) (shift_term d (size ts + c) t).
Proof.
  elimleq; elim: t n m; congruence' => v n m; rewrite size_map; elimif_omega.
  - rewrite !nth_default ?size_map /=; elimif_omega.
  - rewrite shift_typemap_distr -shift_shift_distr // nth_map' /=.
    do 2 f_equal; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma shift_subst_distr n m d c ts t :
  c <= n ->
  shift_term d c (subst_term n m ts t) =
  subst_term (d + n) m ts (shift_term d c t).
Proof.
  elimleq; elim: t m c; congruence' => v m c; elimif_omega.
  rewrite shift_typemap_distr shift_add; elimif_omega.
Qed.

Lemma subst_shift_cancel n m d c ts t :
  c <= n -> size ts + n <= d + c ->
  subst_term n m ts (shift_term d c t) = shift_term (d - size ts) c t.
Proof.
  do 2 elimleq; elim: t m c; congruence' => v m c; elimif_omega.
  rewrite nth_default /=; f_equal; ssromega.
Qed.

Lemma subst_subst_distr n n' m m' xs ys t :
  n' <= n -> m' <= m ->
  subst_term n m xs (subst_term n' m' ys t) =
  subst_term n' m' (map (subst_term (n - n') (m - m') xs) ys)
    (subst_term (size ys + n) m xs t).
Proof.
  do 2 elimleq; elim: t n' m'; congruence' => v n' m'; elimif_omega.
  - rewrite nth_default /=; elimif_omega.
    rewrite -!shift_typemap_distr (@subst_shift_cancel n') // size_map;
      elimif_omega.
  - rewrite -!shift_typemap_distr -shift_subst_distr //
            subst_shifttyp_distr; elimif_omega.
    rewrite nth_map' /=; do 2 f_equal;
      apply nth_equal; rewrite !size_map; elimif_omega.
Qed.

Lemma subst_app n m xs ys t :
  subst_term n m xs (subst_term (size xs + n) m ys t) =
  subst_term n m (xs ++ ys) t.
Proof.
  elim: t n m; congruence' => v n m; rewrite nth_cat size_cat; elimif_omega.
  rewrite -!shift_typemap_distr subst_shift_cancel; elimif_omega.
Qed.

Lemma subst_nil n m t : subst_term n m [::] t = t.
Proof.
  elim: t n m; congruence' => v n m; rewrite nth_nil /= -fun_if; elimif_omega.
Qed.

Lemma subst_shifttyp_app n m m' ts t :
  subst_term n m (map (typemap (shift_typ m') 0) ts) t =
  subst_term n (m' + m) ts t.
Proof.
  elim: t n m; congruence' => v n m; rewrite size_map; elimif_omega.
  rewrite -!shift_typemap_distr !(nth_map' (typemap _ _)) /=; do 2 f_equal.
  elim: ts => //= t ts ->; f_equal.
  rewrite typemap_compose; apply typemap_eq => {n t ts} n t.
  rewrite addn0 shift_add_ty; elimif_omega.
Qed.

Lemma redappl t1 t1' t2 ty : t1 ->r t1' -> t1 @{t2 \: ty} ->r t1' @{t2 \: ty}.
Proof. apply (rtc_map' (fun x y => @red1appl x y t2 ty)). Qed.

Lemma redappr t1 t2 t2' ty : t2 ->r t2' -> t1 @{t2 \: ty} ->r t1 @{t2' \: ty}.
Proof. apply (rtc_map' (fun x y => @red1appr t1 x y ty)). Qed.

Lemma redapp t1 t1' t2 t2' ty :
  t1 ->r t1' -> t2 ->r t2' -> t1 @{t2 \: ty} ->r t1' @{t2' \: ty}.
Proof.
  by move => H H0; eapply rtc_trans' with (t1' @{t2 \: ty});
    [apply redappl | apply redappr].
Qed.

Lemma redabs t t' : t ->r t' -> abs t ->r abs t'.
Proof. apply (rtc_map' red1abs). Qed.

Lemma reduapp t t' ty1 ty2 : t ->r t' -> {t \: ty1}@ ty2 ->r {t' \: ty1}@ ty2.
Proof. apply (rtc_map' (fun x y => @red1uapp x y ty1 ty2)). Qed.

Lemma reduabs t t' : t ->r t' -> uabs t ->r uabs t'.
Proof. apply (rtc_map' red1uabs). Qed.

Hint Resolve redappl redappr redapp redabs reduapp reduabs.

Lemma shifttyp_reduction1 t t' d c :
  t ->r1 t' -> typemap (shift_typ d) c t ->r1 typemap (shift_typ d) c t'.
Proof.
  move => H; move: t t' H d c.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 d c; rewrite shifttyp_subst_distr //= subn0.
  - by move => t ty1 ty2 d c; rewrite substtyp_shifttyp_distr //= subn0 add1n.
Qed.

Lemma shift_reduction1 t t' d c :
  t ->r1 t' -> shift_term d c t ->r1 shift_term d c t'.
Proof.
  move => H; move: t t' H d c.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 d c; rewrite subst_shift_distr //= subn0 add1n.
  - by move => t ty1 ty2 d c; rewrite shift_typemap_distr.
Qed.

Lemma substtyp_reduction1 t t' tys n :
  t ->r1 t' ->
  typemap (subst_typ^~ tys) n t ->r1 typemap (subst_typ^~ tys) n t'.
Proof.
  move => H; move: t t' H tys n.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 tys n;
      rewrite substtyp_subst_distr // subn0; constructor.
  - by move => t ty1 ty2 tys n; rewrite substtyp_substtyp_distr //= add1n subn0.
Qed.

Lemma subst_reduction1 t t' n m ts :
  t ->r1 t' -> subst_term n m ts t ->r1 subst_term n m ts t'.
Proof.
  move => H; move: t t' H n m ts.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 n m ts; rewrite subst_subst_distr //= !subn0.
  - by move => t ty1 ty2 n m ts; rewrite subst_substtyp_distr.
Qed.

Lemma subst_reduction t n m ts :
  Forall (fun t => t.1 ->r t.2) ts ->
  subst_term n m (unzip1 ts) t ->r subst_term n m (unzip2 ts) t.
Proof.
  move => H; elim: t n m => //=;
    auto => v n m; rewrite !size_map; elimif_omega.
  elim: ts v H => //= [[t t']] ts IH [[H _] | v] //=.
  - move: H.
    apply (rtc_map' (f := fun x =>
      typemap (shift_typ m) 0 (shift_term n 0 x))) => t1 t2 H.
    by apply shifttyp_reduction1, shift_reduction1.
  - by case => _ H; rewrite subSS; apply IH.
Qed.

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
Proof. by elim: t; constructor. Qed.

Hint Constructors parred.
Hint Resolve parred_refl.

Lemma betared1_in_parred : inclusion reduction1 parred.
Proof. by apply reduction1_ind; constructor. Qed.

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
  subst_term n m (unzip1 ps) t ->rp subst_term n m (unzip2 ps) t'.
Proof.
  move => H H0; move: t t' H0 n m.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => tl tl' tr tr' ty H0 H1 H2 H3 n m;
      rewrite subst_subst_distr //= !subn0 add1n; auto.
  - by move => t t' ty1 ty2 H0 H1 n m; rewrite subst_substtyp_distr //=; auto.
  - move => v n m; rewrite !size_map; case: ifP => //; elimleq.
    elim: ps H v => //= [[t t']] ts IH [H H0] [| v] //=.
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
  apply (rtc_confluent' betared1_in_parred parred_in_betared parred_confluent).
Qed.

End confluence_proof.

Module subject_reduction_proof.

Lemma ctxleq_preserves_typing ctx1 ctx2 t ty :
  ctx1 <=c ctx2 -> typing ctx1 t ty -> typing ctx2 t ty.
Proof.
  elim: t ty ctx1 ctx2 =>
    [n | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - by move => ty ctx1 ctx2 /ctxleqP; apply.
  - by move => ty ctx1 ctx2 H /andP [] /(IHtl _ _ _ H) ->; apply IHtr.
  - by move => tyl tyr ctx1 ctx2 H; apply IHt; rewrite ctxleqE eqxx.
  - by move => ty ctx1 ctx2 H /andP [] ->; apply IHt.
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
  - by move => ty d c ctx /andP [] /IHtl => ->; apply IHtr.
  - by move => tyl tyr d c ctx /(IHt _ d c).
  - by move => ty d c ctx /andP [] /eqP -> /IHt ->;
      rewrite subst_shift_distr_ty //= subn0 add1n eqxx.
  - move => ty d c ctx /(IHt _ d c.+1).
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
  - by move => ty n ctx /andP [] /IHtl ->; apply IHtr.
  - by move => tyl tyr n ctx /(IHt _ n).
  - by move => ty n ctx /andP [] /eqP -> /IHt ->;
      rewrite subst_subst_distr_ty //= subn0 add1n eqxx.
  - move => ty n ctx /(IHt _ n.+1).
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
  - move => ty c ctx1 ctx2 /eqP ->; apply/eqP; rewrite nth_insert; elimif_omega.
  - by move => ty c ctx1 ctx2 /andP [] /IHtl -> /IHtr ->.
  - by move => tyl tyr c ctx1 ctx2 /(IHt _ c.+1 _ ctx2).
  - by move => ty c ctx1 ctx2 /andP [] -> /IHt ->.
  - move => ty c ctx1 ctx2 /(IHt _ c _ (ctxmap (shift_typ 1 0) ctx2)).
    by rewrite map_insert size_map.
Qed.

Lemma subject_subst t ty n m ctx ctx' :
  all (fun p => typing (drop n ctx) (typemap (shift_typ m) 0 p.1) p.2) ctx' ->
  typing (ctxinsert [seq Some p.2 | p <- ctx'] ctx n) t ty ->
  typing ctx (subst_term n m (unzip1 ctx') t) ty.
Proof.
  elim: t ty n m ctx ctx' =>
    [v | tl IHtl tr IHtr tty | t IHt [] | t IHt ty1 ty2 | t IHt []] //=.
  - move => ty n m ctx ctx' H.
    rewrite nth_insert !size_map; elimif_omega.
    + by move => H0; rewrite nth_default ?size_map /= addnC // leq_addl.
    + rewrite !(nth_map (var 0, tyvar 0)) // => /eqP [] ->.
      case: {ty v H0} (nth _ _ _) (all_nthP (var 0, tyvar 0) H v H0) =>
        /= t ty /(subject_shift 0 (ctxinsert [::] (take n ctx) n)).
      rewrite size_insert size_take minnC minKn add0n shift_typemap_distr.
      apply ctxleq_preserves_typing.
      rewrite /insert take0 sub0n take_minn minnn size_take minnE subKn
              ?leq_subr //= drop_take_nil cats0 drop0 -catA
              -{4}(cat_take_drop n ctx) ctxleq_appl.
      by case (leqP' n (size ctx)) => //= H0;
        rewrite drop_oversize ?(ltnW H0) //= cats0;
        apply/ctxleqP => /= i ty' /eqP; rewrite nth_nseq if_same.
  - by move => ty n m ctx ctx' H /andP [] /IHtl -> //=; apply IHtr.
  - by move => tyl tyr n m ctx ctx' H H0; apply IHt.
  - by move => ty n m ctx ctx' H /andP [] ->; apply IHt.
  - move => ty n m ctx ctx' H H0.
    rewrite -(addn0 m.+1) -subst_shifttyp_app.
    set ctx'' := (map _ (map _ _)).
    have {ctx''} ->: ctx'' = unzip1
        [seq (typemap (shift_typ m.+1) 0 p.1, shift_typ 1 0 p.2) | p <- ctx']
      by rewrite /unzip1 /ctx'' -!map_comp /comp /=.
    apply IHt.
    + move: H {t ty IHt H0}; rewrite all_map; apply sub_all.
      rewrite /subpred /preim /pred_of_simpl; case => /= t ty.
      rewrite -map_drop shifttyp_zero -(@shifttyp_add m _ 1 0) //.
      apply shifttyp_preserves_typing.
    + by move: H0; rewrite map_insert -!map_comp.
Qed.

Lemma subject_subst0 t ty ctx ctx' :
  all (fun p => typing ctx p.1 p.2) ctx' ->
  typing ([seq Some p.2 | p <- ctx'] ++ ctx) t ty ->
  typing ctx (subst_term 0 0 (unzip1 ctx') t) ty.
Proof.
  move => H; move: (@subject_subst t ty 0 0 ctx ctx');
    rewrite /insert take0 sub0n drop0 /=; apply; move: H.
  by apply sub_all; case => t' ty' /=; rewrite shifttyp_zero.
Qed.

Theorem subject_reduction ctx t t' ty :
  t ->r1 t' -> typing ctx t ty -> typing ctx t' ty.
Proof.
  move => H; move: t t' H ctx ty; refine (reduction1_ind _ _ _ _ _ _ _) => /=
    [ty' t1 t2 ctx ty /andP [] H H0 |
     t tyl tyr ctx ty /andP [] /eqP -> {ty} |
     t1 t1' t2 ty _ H ctx ty0 /andP [] /H -> |
     t1 t2 t2' ty _ H ctx ty0 /andP [] -> /H |
     t t' _ H ctx [] //= tyl tyr /H |
     t t' tyl tyr _ H ctx ty /andP [] -> /H |
     t t' _ H ctx [] //= t0 /H] //=.
  - by apply (@subject_subst0 _ _ ctx [:: (t2, ty')]) => //=; rewrite H0.
  - move/(substtyp_preserves_typing 0 [:: tyr]).
    set ctx' := ctxmap _ _; have {ctx'} -> //: ctx' = ctx.
    rewrite {}/ctx' -map_comp -{2}(map_id ctx).
    apply eq_map; case => //= ty.
    by rewrite subst_shift_cancel_ty2 //= shift_zero_ty.
Qed.

End subject_reduction_proof.

Module strong_normalization_proof_typefree.

Section CRs.
Variable (P : term -> Prop).
Definition CR1 := forall t, P t -> SN t.
Definition CR2 := forall t t', t ->r1 t' -> P t -> P t'.
Definition CR3 := forall t,
  neutral t -> (forall t', t ->r1 t' -> P t') -> P t.
End CRs.

Record RC (P : term -> Prop) : Prop :=
  reducibility_candidate {
    rc_cr1 : CR1 P ;
    rc_cr2 : CR2 P ;
    rc_cr3 : CR3 P
  }.

Lemma CR2' P t t' : RC P -> t ->r t' -> P t -> P t'.
Proof.
  move => H; move: t t'.
  refine (clos_refl_trans_1n_ind _ _ _ _ _) => //= x y z H0 H1 H2 H3.
  by apply H2, (rc_cr2 H H0).
Qed.

Lemma CR4 P t : RC P -> neutral t -> (forall t', ~ t ->r1 t') -> P t.
Proof. by case => _ _ H H0 H1; apply H => // t' /H1. Qed.

Lemma CR4' P (v : nat) : RC P -> P v.
Proof. by move/CR4; apply => // t' H; inversion H. Qed.

Lemma snorm_isrc : RC SN.
Proof.
  constructor; move => /=; try tauto.
  - by move => t t' H []; apply.
  - by move => t H H0; constructor => t' H1; apply H0.
Qed.

Lemma rcfun_isrc tyl P Q :
  RC P -> RC Q -> RC (fun u => forall v, P v -> Q (u @{v \: tyl})).
Proof.
  move => H H0; constructor; move => /=.
  - by move => t /(_ 0 (CR4' _ H)) /(rc_cr1 H0);
      apply (acc_preservation (f := app^~_^~_)); constructor.
  - by move => t t' H1 H2 v /H2; apply (rc_cr2 H0); constructor.
  - move => t1 H1 H2 t2 H3; move: t2 {H3} (rc_cr1 H H3) (H3).
    refine (Acc_ind _ _) => t2 _ H3 H4.
    apply (rc_cr3 H0) => //= t3 H5; move: H1; inversion H5;
      subst => //= _; auto; apply H3 => //; apply (rc_cr2 H H9 H4).
Qed.

Fixpoint reducible ty (preds : seq (typ * (term -> Prop))) : term -> Prop :=
  match ty with
    | tyvar v => nth SN (unzip2 preds) v
    | tyfun tyl tyr => fun t => forall t',
      reducible tyl preds t' ->
      reducible tyr preds (t @{t' \: subst_typ 0 (unzip1 preds) tyl})
    | tyabs ty => fun t => forall ty' P, RC P ->
      reducible ty ((ty', P) :: preds)
        ({t \: subst_typ 1 (unzip1 preds) ty}@ ty')
  end.

Lemma reducibility_isrc ty preds :
  Forall (fun p => RC p.2) preds -> RC (reducible ty preds).
Proof.
  elim: ty preds => /= [n | tyl IHtyl tyr IHtyr | ty IHty] preds.
  - rewrite /unzip2 -(nth_map' _ (tyvar 0, SN)).
    move/Forall_nth /(_ _ n); case: (ltnP n (size preds)).
    + by move => _; apply.
    + by move => H _; rewrite (nth_default _ H); apply snorm_isrc.
  - by move => H; apply rcfun_isrc; [apply IHtyl | apply IHtyr].
  - move => H; constructor.
    + move => /= t /(_ 0 SN snorm_isrc)
        /(rc_cr1 (IHty ((_, _) :: _) (conj snorm_isrc H))).
      by apply (acc_preservation (f := uapp^~_^~_)) => x y H0; constructor.
    + move => /= t t' H0 H1 ty' P H2; move: (H1 ty' _ H2).
      by apply (rc_cr2 (IHty ((_, _) :: _) (conj H2 H))); constructor.
    + move => /= t H0 H1 ty' P H2.
      apply (rc_cr3 (IHty ((_, _) :: _) (conj H2 H))) => //= t' H3.
      by move: H0; inversion H3; subst => //= _; apply H1.
Qed.

Lemma shift_reducibility c ty preds preds' t :
  c <= size preds ->
  (reducible (shift_typ (size preds') c ty)
     (insert preds' preds (tyvar 0, SN) c) t <->
   reducible ty preds t).
Proof.
  have submaxn m n : m - maxn m n = 0 by ssromega.
  elim: ty c preds t => [v | tyl IHtyl tyr IHtyr | ty IHty] c preds t H.
  - rewrite /= /unzip2 map_insert nth_insert size_map; elimif_omega.
  - rewrite /= /unzip1 map_insert -(size_map (@fst _ _)) -{2}(add0n c)
            subst_shift_cancel_ty4 ?size_map //.
    by split => /= H0 t' /(IHtyl c _ _ H) /H0 /(IHtyr c _ _ H).
  - rewrite /= /unzip1 map_insert -(size_map (@fst _ _)) -add1n
            subst_shift_cancel_ty4 ?size_map //.
    by split => H0 ty' P H1; apply (IHty c.+1 ((ty', P) :: preds));
      rewrite ?ltnS ?H //; apply H0.
Qed.

Lemma subst_reducibility ty preds n tys t :
  n <= size preds ->
  (reducible (subst_typ n tys ty) preds t <->
   reducible ty
     (insert [seq (subst_typ 0 (drop n (unzip1 preds)) ty,
                   reducible ty (drop n preds)) | ty <- tys]
             preds (tyvar 0, SN) n)
     t).
Proof.
  elim: ty preds n tys t => [v | tyl IHtyl tyr IHtyr | ty IHty] preds n tys t.
  - rewrite /= /unzip2 map_insert /= -map_comp /comp /=
            nth_insert size_map -/unzip2; elimif_omega.
    + by rewrite nth_default ?leq_addr //= addnC.
    + move => H0.
      rewrite (nth_map (tyvar (v - size tys))) //=.
      move: (shift_reducibility (nth (tyvar (v - size tys)) tys v)
        (take n preds) t (leq0n (size (drop n preds)))).
      rewrite /insert take0 drop0 sub0n /= cat_take_drop size_take.
      by move/minn_idPl: H0 => ->.
  - by move => H /=; split => H1 t' /IHtyl => /(_ H) /H1 /IHtyr => /(_ H);
      rewrite /unzip1 map_insert -map_comp /comp /=
              subst_subst_compose_ty // size_map.
  - move => H /=; rewrite /unzip1 map_insert -!map_comp /comp /=
      -subst_subst_compose_ty ?size_map // add1n -/unzip1.
    split => H0 ty' P /(H0 ty') {H0}.
    + by move/IHty => /= /(_ H); rewrite /insert /= subSS.
    + by move => H0; apply IHty.
Qed.

Lemma abs_reducibility t tyl tyr preds :
  Forall (fun p => RC p.2) preds ->
  (forall t',
   reducible tyl preds t' ->
   reducible tyr preds (subst_term 0 0 [:: t'] t)) ->
  reducible (tyl :->: tyr) preds (abs t).
Proof.
  move => /= H.
  move: (reducible tyl preds) (reducible tyr preds) (reducibility_isrc tyl H)
    (reducibility_isrc tyr H) => {H} P Q HP HQ H t' H0.
  have H1: SN t by
    move: (rc_cr1 HQ (H _ H0));
      apply acc_preservation => x y; apply subst_reduction1.
  move: t H1 t' {H H0} (rc_cr1 HP H0) (H0) (H _ H0).
  refine (Acc_ind _ _) => t1 _ H; refine (Acc_ind _ _) => t2 _ H0 H1 H2.
  apply rc_cr3 => // t' H3; inversion H3; subst => //.
  - inversion H8; subst; apply H; auto.
    + apply (rc_cr1 HP H1).
    + by apply (rc_cr2 HQ (subst_reduction1 0 0 [:: t2] H5)).
  - apply H0 => //; first by apply (rc_cr2 HP H8).
    move: H2; apply (CR2' HQ).
    apply (@subst_reduction t1 0 0 [:: (t2, t2')]) => //=; split => //.
    by apply rtc_step.
Qed.

Lemma uabs_reducibility t ty preds :
  Forall (fun p => RC p.2) preds ->
  (forall v P, RC P ->
   reducible ty ((v, P) :: preds) (typemap (subst_typ^~ [:: v]) 0 t)) ->
  reducible (tyabs ty) preds (uabs t).
Proof.
  move => /= H H0 ty' P H1.
  move: (reducible _ _) (@reducibility_isrc ty ((ty', P) :: preds))
    (H0 ty' P H1) => P' /= /(_ (conj H1 H)) {H H0 H1} H H0.
  have H1: SN t by
    move: (rc_cr1 H H0);
      apply acc_preservation => x y; apply substtyp_reduction1.
  move: t H1 H0; refine (Acc_ind _ _) => t _ H0 H1.
  apply (rc_cr3 H) => //= t' H2; inversion H2; subst => //.
  inversion H7; subst; apply H0 => //.
  apply (rc_cr2 H (substtyp_reduction1 _ _ H4) H1).
Qed.

Lemma uapp_reducibility t ty ty' preds :
  Forall (fun p => RC p.2) preds -> reducible (tyabs ty) preds t ->
  reducible (subst_typ 0 [:: ty'] ty) preds
    ({t \: subst_typ 1 (unzip1 preds) ty}@ subst_typ 0 (unzip1 preds) ty').
Proof.
  move => /= H H0.
  apply subst_reducibility => //=.
  rewrite /insert take0 sub0n !drop0 /=.
  by apply H0, reducibility_isrc.
Qed.

Lemma reduce_lemma ctx preds t ty :
  typing [seq Some c.2 | c <- ctx] t ty ->
  Forall (fun p => RC p.2) preds ->
  Forall (fun c => reducible c.2 preds c.1) ctx ->
  reducible ty preds
    (subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t)).
Proof.
  elim: t ty ctx preds => /=.
  - move => v ty ctx preds H H0 H1.
    rewrite shifttyp_zero shift_zero subn0 size_map.
    elim: ctx v H H1 => //=; first by case.
    case => t ty' ctx IH [] //=.
    + by case/eqP => <- [].
    + by move => v H [H1 H2]; rewrite subSS; apply IH.
  - move => tl IHtl tr IHtr tty ty ctx preds /andP [H H0] H1 H2.
    by move: (IHtl (tty :->: ty) ctx preds H H1 H2) => /=; apply; apply IHtr.
  - move => t IHt [] // tyl tyr ctx preds H H0 H1.
    apply abs_reducibility => // t' H2.
    rewrite subst_app //=; apply (IHt tyr ((t', tyl) :: ctx)) => //.
  - move => t IHt ttyl ttyr ty ctx preds /andP [] /eqP -> {ty} H H0 H1.
    by apply uapp_reducibility => //; apply IHt.
  - move => t IHt [] // ty ctx preds H H0 H1.
    apply uabs_reducibility => // v P H2.
    rewrite -(subst_substtyp_distr 0 [:: v]) // typemap_compose /=.
    have /(typemap_eq 0 t) -> : forall i ty,
      subst_typ (i + 0) [:: v] (subst_typ (i + 1) (unzip1 preds) ty) =
      subst_typ i (unzip1 ((v, P) :: preds)) ty by
        move => i ty'; rewrite addn0 addn1 subst_app_ty.
    move: (IHt ty [seq (c.1, shift_typ 1 0 c.2) | c <- ctx] ((v, P) :: preds)).
    rewrite /unzip1 -!map_comp /comp /=; apply => //=.
    + by move: H; rewrite -map_comp /comp /=.
    + apply Forall_map; move: H1; rewrite /comp /=; apply Forall_impl =>
        {t ty IHt H H0 H2} [[t ty]] /=
        /(proj2 (shift_reducibility ty [:: (v, P)] t (leq0n _))).
      by rewrite /insert take0 drop0 sub0n /=; apply.
Qed.

Theorem typed_term_is_snorm ctx t ty : typing ctx t ty -> SN t.
Proof.
  move => H.
  move: (@reduce_lemma
    (map (oapp (pair (var 0)) (var 0, tyvar 0)) ctx) [::] t ty) => /=.
  rewrite -map_comp /comp /=.
  have {H} H: typing
    [seq Some (oapp (pair (var 0)) (var 0, tyvar 0) c).2 | c <- ctx] t ty by
    move: H; apply subject_reduction_proof.ctxleq_preserves_typing;
      elim: ctx {t ty} => //; case => // ty ctx H; rewrite ctxleqE eqxx /=.
  move/(_ H I) {H}.
  have H: Forall (fun c => reducible c.2 [::] c.1)
                 (map (oapp (pair (var 0)) (var 0, tyvar 0)) ctx) by
    apply Forall_map, Forall_nth => /= x m _; rewrite /oapp /snd;
      case: nth => [ty' |]; apply CR4', reducibility_isrc.
  move/(_ H) => {H} /(rc_cr1 (reducibility_isrc _ _)) /= /(_ I).
  set f := subst_term _ _ _; set g := typemap _ _.
  apply (acc_preservation (f := f \o g)) => x y H.
  by apply subst_reduction1, substtyp_reduction1.
Qed.

End strong_normalization_proof_typefree.

Module strong_normalization_proof_typed.

Import subject_reduction_proof.

Section CRs.
Variable (ty : typ) (P : context typ -> term -> Prop).
Definition CR_typed := forall ctx t, P ctx t -> typing ctx t ty.
Definition CR0 := forall ctx ctx' t, ctx <=c ctx' -> P ctx t -> P ctx' t.
Definition CR1 := forall ctx t, P ctx t -> SN t.
Definition CR2 := forall ctx t t', t ->r1 t' -> P ctx t -> P ctx t'.
Definition CR3 := forall ctx t,
  typing ctx t ty -> neutral t ->
  (forall t', t ->r1 t' -> P ctx t') -> P ctx t.
End CRs.

Record RC (ty : typ) (P : context typ -> term -> Prop) : Prop :=
  reducibility_candidate {
    rc_typed : CR_typed ty P;
    rc_cr0 : CR0 P ;
    rc_cr1 : CR1 P ;
    rc_cr2 : CR2 P ;
    rc_cr3 : CR3 ty P
  }.

Lemma CR2' ty P ctx t t' : RC ty P -> t ->r t' -> P ctx t -> P  ctx t'.
Proof.
  move => H; move: t t'.
  refine (clos_refl_trans_1n_ind _ _ _ _ _) => //= x y z H0 H1 H2 H3.
  by apply H2, (rc_cr2 H H0).
Qed.

Lemma CR4 ty P ctx t : RC ty P ->
  typing ctx t ty -> neutral t -> (forall t', ~ t ->r1 t') -> P ctx t.
Proof. by case => _ _ _ _ H H0 H1 H2; apply H => // t' /H2. Qed.

Lemma CR4' ty P ctx (v : nat) : RC ty P -> ctxindex ctx v ty -> P ctx v.
Proof. move/CR4 => H H0; apply H => // t' H1; inversion H1. Qed.

Notation SN' ty := (fun ctx t => typing ctx t ty /\ SN t).

Lemma snorm_isrc ty : RC ty (SN' ty).
Proof.
  (constructor; move => /=) =>
    [ctx t [] // | ctx ctx' t H [H0 H1] | ctx t [] // |
     ctx t t' H [H0 [H1]] | ctx t ]; split; auto.
  - by apply (ctxleq_preserves_typing H).
  - by apply (subject_reduction H).
  - by constructor => t' /H1 [].
Qed.

Definition rcfun tyl tyr (P Q : context typ -> term -> Prop) ctx u : Prop :=
  typing ctx u (tyl :->: tyr) /\
  forall ctx' v, ctx <=c ctx' -> P ctx' v -> Q ctx' (u @{v \: tyl}).

Lemma rcfun_isrc tyl tyr P Q :
  RC tyl P -> RC tyr Q -> RC (tyl :->: tyr) (rcfun tyl tyr P Q).
Proof.
  move => HP HQ; rewrite /rcfun; constructor; move => /=; first tauto.
  - move => ctx ctx' t H [H0 H1]; split; last move => ctx'' t' H2 H3.
    + by apply (ctxleq_preserves_typing H).
    + by apply (H1 ctx'' t') => //; apply ctxleq_trans with ctx'.
  - move => ctx t [H]
      /(_ _ _ (ctxleq_appr _ _) (CR4' HP (ctxindex_last ctx tyl))) /(rc_cr1 HQ).
    by apply (acc_preservation (f := app^~_^~_)); auto.
  - move => ctx t t' H [H0 H1]; split; last move => ctx' t''.
    + by apply (subject_reduction H).
    + by move => /H1 {H1} H1 /H1 {H1}; apply (rc_cr2 HQ); constructor.
  - move => ctx t H H0 H1; split => // ctx' t' H2 H3.
    move: t' {H3} (rc_cr1 HP H3) (H3).
    refine (Acc_ind _ _) => t' _ IH H3.
    apply (rc_cr3 HQ) => //=; first (apply/andP; split).
    + by apply (ctxleq_preserves_typing H2).
    + by apply (rc_typed HP).
    + move => t'' H4; move: H0; inversion H4; subst => //= _.
      * by apply (proj2 (H1 _ H8) ctx').
      * by apply IH => //; apply (rc_cr2 HP H8).
Qed.

Fixpoint reducible ty (preds : seq (typ * (context typ -> term -> Prop))) :
    context typ -> term -> Prop :=
  match ty with
    | tyvar v => nth (SN' (v - size preds)) (unzip2 preds) v
    | tyfun tyl tyr =>
      let s := subst_typ 0 (unzip1 preds) in
      rcfun (s tyl) (s tyr) (reducible tyl preds) (reducible tyr preds)
    | tyabs ty => fun ctx t => forall ty' P, RC ty' P ->
      reducible ty ((ty', P) :: preds) ctx
        ({t \: subst_typ 1 (unzip1 preds) ty}@ ty')
  end.

Lemma reducibility_isrc ty preds :
  Forall (fun p => RC p.1 p.2) preds ->
  RC (subst_typ 0 (unzip1 preds) ty) (reducible ty preds).
Proof.
  elim: ty preds => /= [n | tyl IHtyl tyr IHtyr | ty IHty] preds.
  - rewrite shift_zero_ty subn0.
    elim: preds n => [| P preds IH []] /=.
    + move => n _; rewrite !nth_nil /= !subn0; apply snorm_isrc.
    + by case.
    + by move => n [H] /(IH n) {IH}; rewrite !subSS.
  - by move => H; apply rcfun_isrc; [apply IHtyl | apply IHtyr].
  - move => H; constructor.
    + by move => /= ctx t /(_ 0 _ (snorm_isrc _)) /=
        /(rc_typed (IHty ((_, _) :: _) (conj (snorm_isrc _) H))) /andP [].
    + move => /= ctx ctx' t H0 H1 ty' P H2.
      move: (rc_cr0 (IHty ((_, _) :: _) (conj H2 H))) => /(_ ctx ctx' _ H0).
      by apply; apply H1.
    + move => /= ctx t /(_ 0 _ (snorm_isrc _))
        /(rc_cr1 (IHty ((_, _) :: _) (conj (snorm_isrc _) H))).
      by apply (acc_preservation (f := uapp^~_^~_)) => x y H0; constructor.
    + move => /= ctx t t' H0 H1 ty' P H2; move: (H1 _ _ H2).
      by apply (rc_cr2 (IHty ((_, _) :: _) (conj H2 H))); constructor.
    + move => /= ctx t H0 H1 H2 ty' P H3.
      apply (rc_cr3 (IHty ((_, _) :: _) (conj H3 H))) => //=.
      * by rewrite subst_app_ty /= eqxx.
      * by move => t' H4; move: H0; inversion H4; subst => //= _; apply H2.
Qed.

Lemma shift_reducibility c ty preds preds' ctx t :
  c <= size preds ->
  (reducible (shift_typ (size preds') c ty)
     (insert preds' preds (tyvar 0, SN' 0) c) ctx t <->
   reducible ty preds ctx t).
Proof.
  have submaxn m n : m - maxn m n = 0 by ssromega.
  elim: ty c preds ctx t => [v | tyl IHtyl tyr IHtyr | ty IHty] c preds ctx t H.
  - rewrite /= /unzip2 map_insert nth_insert size_map size_insert; elimif_omega.
    rewrite (_ : v - size preds = 0) //; ssromega.
  - rewrite /= /rcfun /unzip1 map_insert -(size_map (@fst _ _)) /=
            !subst_shift_cancel_ty4 ?size_map //.
    by split; case => H0 H1; split => // ctx' t' H2
      /(IHtyl c _ _ _ H) /(H1 _ _ H2) /(IHtyr c _ _ _ H).
  - rewrite /= /unzip1 map_insert -(size_map (@fst _ _)) -add1n
            subst_shift_cancel_ty4 ?size_map //.
    by split => H0 ty' P H1; apply (IHty c.+1 ((ty', P) :: preds));
      rewrite ?ltnS ?H //; apply H0.
Qed.

Lemma subst_reducibility ty preds n tys ctx t :
  n <= size preds ->
  (reducible (subst_typ n tys ty) preds ctx t <->
   reducible ty
     (insert [seq (subst_typ 0 (drop n (unzip1 preds)) ty,
                   reducible ty (drop n preds)) | ty <- tys]
             preds (tyvar 0, SN' 0) n)
     ctx t).
Proof.
  elim: ty preds n tys ctx t =>
    [v | tyl IHtyl tyr IHtyr | ty IHty] preds n tys ctx t.
  - rewrite /= size_insert size_map /unzip2 map_insert /= -map_comp /comp /=
            nth_insert size_map -/unzip2; elimif_omega.
    + by move/maxn_idPr => ->; rewrite nth_default ?leq_addr //= addnC.
    + move => H0.
      rewrite (nth_map (tyvar (v - size tys))) //=.
      move: (shift_reducibility (nth (tyvar (v - size tys)) tys v)
        (take n preds) ctx t (leq0n (size (drop n preds)))).
      rewrite /insert take0 drop0 sub0n /= cat_take_drop size_take.
      by move/minn_idPl: H0 => ->.
    + by move => H; rewrite (_ : v - size preds = 0) //; ssromega.
  - move => H /=; rewrite /rcfun /= /unzip1 map_insert -!map_comp /comp /=
      -!subst_subst_compose_ty ?size_map // -/unzip1 add0n.
    by split; case => H1 H2; split =>
      // ctx' t' H3 /IHtyl => /(_ H) /(H2 _ _ H3) /IHtyr => /(_ H);
      rewrite /unzip1 subst_subst_compose_ty ?size_map.
  - move => H /=; rewrite /unzip1 map_insert -!map_comp /comp /=
      -subst_subst_compose_ty ?size_map // add1n -/unzip1.
    split => H0 ty' P /H0 {H0}.
    + by move/IHty => /= /(_ H); rewrite /insert /= subSS.
    + by move => H0; apply IHty.
Qed.

Lemma abs_reducibility tyl tyr preds ctx t :
  typing ctx (abs t) (subst_typ 0 (unzip1 preds) (tyl :->: tyr)) ->
  Forall (fun p => RC p.1 p.2) preds ->
  (forall ctx' t', ctx <=c ctx' ->
   reducible tyl preds ctx' t' ->
   reducible tyr preds ctx' (subst_term 0 0 [:: t'] t)) ->
  reducible (tyl :->: tyr) preds ctx (abs t).
Proof.
  move => /= H H0.
  move: (reducible tyl preds) (reducible tyr preds)
    (reducibility_isrc tyl H0) (reducibility_isrc tyr H0) =>
    {H0} P Q HP HQ H0; split => // ctx' t' H1 H2.
  have H3: SN t by
    move: (rc_cr1 HQ (H0 _ _ H1 H2));
      apply acc_preservation => x y; apply subst_reduction1.
  move: t H3 t' {H0 H2} (rc_cr1 HP H2) H H1 (H2) (H0 _ _ H1 H2).
  refine (Acc_ind _ _) => t1 _ H; refine (Acc_ind _ _) => t2 _ H0 H1 H2 H3 H4.
  apply (rc_cr3 HQ) => //=; first (apply/andP; split).
  - by move: H1; apply ctxleq_preserves_typing; rewrite ctxleqE eqxx.
  - by apply (rc_typed HP).
  - move => t' H5; inversion H5; subst => //.
    + inversion H10; subst; apply H; auto.
      * apply (rc_cr1 HP H3).
      * by move: H1; apply subject_reduction.
      * by apply (rc_cr2 HQ (subst_reduction1 0 0 [:: t2] H7)).
    + apply H0 => //; first by apply (rc_cr2 HP H10).
      move: H4; apply (CR2' HQ).
      apply (@subst_reduction t1 0 0 [:: (t2, t2')]) => //=; split => //.
      by apply rtc_step.
Qed.

Lemma uabs_reducibility ty preds ctx t :
  typing ctx (uabs t) (subst_typ 0 (unzip1 preds) (tyabs ty)) ->
  Forall (fun p => RC p.1 p.2) preds ->
  (forall v P, RC v P ->
   reducible ty ((v, P) :: preds) ctx (typemap (subst_typ^~ [:: v]) 0 t)) ->
  reducible (tyabs ty) preds ctx (uabs t).
Proof.
  move => /= H H0 H1 ty' P H2.
  move: (reducible _ _) (@reducibility_isrc ty ((ty', P) :: preds))
    (H1 ty' P H2) => P' /= /(_ (conj H2 H0)) {H0 H1 H2} H0 H1.
  have H2: SN t by
    move: (rc_cr1 H0 H1);
      apply acc_preservation => x y; apply substtyp_reduction1.
  move: t H2 H H1; refine (Acc_ind _ _) => t _ H1 H H2.
  apply (rc_cr3 H0) => //=.
  - by rewrite subst_app_ty eqxx.
  - move => t' H3; inversion H3; subst => //.
    inversion H8; subst; apply H1 => //.
    + by apply (subject_reduction H5).
    + apply (rc_cr2 H0 (substtyp_reduction1 _ _ H5) H2).
Qed.

Lemma uapp_reducibility ty ty' preds ctx t :
  Forall (fun p => RC p.1 p.2) preds ->
  reducible (tyabs ty) preds ctx t ->
  reducible (subst_typ 0 [:: ty'] ty) preds
    ctx ({t \: subst_typ 1 (unzip1 preds) ty}@ subst_typ 0 (unzip1 preds) ty').
Proof.
  move => /= H H0.
  apply subst_reducibility => //=.
  rewrite /insert take0 sub0n !drop0 /=.
  by apply H0, reducibility_isrc.
Qed.

Lemma reduce_lemma ctx ctx' preds t ty :
  typing [seq Some c.2 | c <- ctx] t ty ->
  Forall (fun p => RC p.1 p.2) preds ->
  Forall (fun c => reducible c.2 preds ctx' c.1) ctx ->
  reducible ty preds ctx'
    (subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t)).
Proof.
  have Hty: forall t ty  ctx ctx' preds,
    typing [seq Some c.2 | c <- ctx] t ty ->
    Forall (fun p => RC p.1 p.2) preds ->
    Forall (fun c => reducible c.2 preds ctx' c.1) ctx ->
    typing ctx'
      (subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t))
      (subst_typ 0 (unzip1 preds) ty).
    clear => t ty ctx ctx' preds H H0 H1.
    move: (fun t ty => @subject_subst0 t ty ctx'
      [seq (c.1, subst_typ 0 (unzip1 preds) c.2) | c <- ctx]).
    rewrite /unzip1 -!map_comp !/comp -/unzip1; apply => /=.
    - by elim: ctx H1 {H} => //= [[]] /= t' ty' ctx IH []
        /(rc_typed (reducibility_isrc ty' H0)) ->.
    - by move: (substtyp_preserves_typing 0 (unzip1 preds) H);
        rewrite -map_comp; apply ctxleq_preserves_typing, ctxleq_appr.
  elim: t ty ctx ctx' preds => /=.
  - move => v ty ctx ctx' preds H H0 H1.
    rewrite shifttyp_zero shift_zero subn0 size_map.
    elim: ctx v H H1 => //=; first by case.
    case => t ty' ctx IH [] //=.
    + by case/eqP => <- [].
    + by move => v H [H1 H2]; rewrite subSS; apply IH.
  - move => tl IHtl tr IHtr tty ty ctx ctx' preds /andP [H H0] H1 H2.
    by move: (IHtl (tty :->: ty) ctx ctx' preds H H1 H2) => /= [_];
      apply => //; apply IHtr.
  - move => t IHt [] // tyl tyr ctx ctx' preds H H0 H1.
    apply abs_reducibility => //; first by apply (Hty (abs t)).
    move => ctx'' t' H2 H3; rewrite subst_app //=.
    apply (IHt tyr ((t', tyl) :: ctx)) => //=; split => //; move: H1.
    by apply Forall_impl => {t' H H3} [[t' ty]] /=;
      apply (rc_cr0 (reducibility_isrc ty H0) H2).
  - move => t IHt ttyl ttyr ty ctx ctx' preds /andP [] /eqP -> {ty} H H0 H1.
    by apply uapp_reducibility => //; apply IHt.
  - move => t IHt [] // ty ctx ctx' preds H H0 H1.
    apply uabs_reducibility => //; first by apply (Hty (uabs t)).
    move => v P H2.
    rewrite -(subst_substtyp_distr 0 [:: v]) // typemap_compose /=.
    have /(typemap_eq 0 t) -> : forall i ty,
      subst_typ (i + 0) [:: v] (subst_typ (i + 1) (unzip1 preds) ty) =
      subst_typ i (unzip1 ((v, P) :: preds)) ty by
        move => i ty'; rewrite addn0 addn1 subst_app_ty.
    move: (IHt ty
      [seq (c.1, shift_typ 1 0 c.2) | c <- ctx] ctx' ((v, P) :: preds)).
    rewrite /unzip1 -!map_comp /comp /=; apply => //=.
    + by move: H; rewrite -map_comp /comp /=.
    + apply Forall_map; move: H1; apply Forall_impl => [[t' ty']] /=.
      case (shift_reducibility ty' [:: (v, P)] ctx' t' (leq0n (size preds))).
      rewrite /insert take0 drop0 sub0n => _ /=; apply.
Qed.

Theorem typed_term_is_snorm ctx t ty : typing ctx t ty -> SN t.
Proof.
  move => H.
  have {H}: typing (map some (map (odflt (tyvar 0)) ctx)) t ty by
    move: H; apply ctxleq_preserves_typing;
      elim: ctx {t ty} => // [[]] // ty ctx H; rewrite ctxleqE eqxx.
  move: {ctx} (map _ ctx) => ctx.
  have ->: map some ctx =
           [seq Some c.2 | c <- zip (map var (iota 0 (size ctx))) ctx] by
    elim: ctx 0 => //= {t ty} ty ctx IH n; rewrite -IH.
  move => /reduce_lemma; move => /(_ (map some ctx) [::] I).
  rewrite unzip1_zip ?size_map ?size_iota ?leqnn; last by [].
  have H: Forall
      (fun c => reducible c.2 [::] (map some ctx) c.1)
      (zip (map var (iota 0 (size ctx))) ctx) by
    apply Forall_nth; case => {t ty} t ty n; rewrite
      size_zip size_map size_iota minnn nth_map' (nth_map' (@fst _ _)) /=
      -/unzip1 -/unzip2 unzip1_zip ?unzip2_zip ?size_map ?size_iota // => H;
      rewrite (nth_map 0 t var) ?size_iota // nth_iota // add0n;
      apply (CR4' (@reducibility_isrc (nth ty ctx n) [::] I)) => //=;
      rewrite subst_nil_ty (nth_map ty).
  move/(_ H) => {H} /(rc_cr1 (reducibility_isrc _ _)) /= /(_ I).
  set f := subst_term _ _ _; set g := typemap _ _.
  apply (acc_preservation (f := f \o g)) => x y H.
  by apply subst_reduction1, substtyp_reduction1.
Qed.

End strong_normalization_proof_typed.
