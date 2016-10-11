From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LCAC Require Import Relations_ext seq_ext_base ssrnat_ext seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive typ := tyvar of nat | tyfun of typ & typ | tyabs of typ.

Inductive term
  := var  of nat                        (* variable *)
   | app  of term & term                (* value application *)
   | abs  of typ & term                 (* value abstraction *)
   | uapp of term & typ                 (* universal application *)
   | uabs of term.                      (* universal abstraction *)

Coercion tyvar : nat >-> typ.
Coercion var : nat >-> term.

Notation "ty :->: ty'" := (tyfun ty ty') (at level 50, no associativity).
Notation "t @ t'" := (app t t') (at level 60, no associativity).
Notation "t @' ty" := (uapp t ty) (at level 60, no associativity).

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
    | t1l @ t1r, t2l @ t2r => eqterm t1l t2l && eqterm t1r t2r
    | abs ty1 t1, abs ty2 t2 => (ty1 == ty2) && eqterm t1 t2
    | t1 @' ty1, t2 @' ty2 => eqterm t1 t2 && (ty1 == ty2)
    | uabs t1, uabs t2 => eqterm t1 t2
    | _, _ => false
  end.

Lemma eqtermP : Equality.axiom eqterm.
Proof.
  move => t1 t2; apply: (iffP idP) => [| <-].
  - by elim: t1 t2 =>
      [n | t1l IHt1l t1r IHt1r | ty1 t1 IHt1 | t1 IHt1 ty1 | t1 IHt1]
      [// m /eqP -> | //= t2l t2r /andP [] /IHt1l -> /IHt1r -> |
       //= ty2 t2 /andP [] /eqP -> /IHt1 -> |
       //= t2 ty2 /andP [] /IHt1 -> /eqP -> | //= t2 /IHt1 ->].
  - by elim: t1 => //= [t -> t' -> | ty t -> | t ->] *; rewrite ?eqxx.
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
    | tl @ tr => typemap f n tl @ typemap f n tr
    | abs ty t => abs (f n ty) (typemap f n t)
    | t @' ty => typemap f n t @' f n ty
    | uabs t => uabs (typemap f n.+1 t)
  end.

Fixpoint shift_term d c t :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | tl @ tr => shift_term d c tl @ shift_term d c tr
    | abs ty t => abs ty (shift_term d c.+1 t)
    | t @' ty => shift_term d c t @' ty
    | uabs t => uabs (shift_term d c t)
  end.

Notation subst_termv ts m n n' :=
  (typemap (shift_typ n') 0
    (shift_term n 0 (nth (var (m - n - size ts)) ts (m - n)))) (only parsing).

Fixpoint subst_term n n' ts t :=
  match t with
    | var m => if n <= m then subst_termv ts m n n' else m
    | tl @ tr => subst_term n n' ts tl @ subst_term n n' ts tr
    | abs ty t => abs ty (subst_term n.+1 n' ts t)
    | t @' ty => subst_term n n' ts t @' ty
    | uabs t => uabs (subst_term n n'.+1 ts t)
  end.

Reserved Notation "t ->r1 t'" (at level 70, no associativity).

Inductive reduction1 : relation term :=
  | red1fst ty t1 t2   : abs ty t1 @ t2 ->r1 subst_term 0 0 [:: t2] t1
  | red1snd t ty       : uabs t @' ty ->r1 typemap (subst_typ^~ [:: ty]) 0 t
  | red1appl t1 t1' t2 : t1 ->r1 t1' -> t1 @ t2 ->r1 t1' @ t2
  | red1appr t1 t2 t2' : t2 ->r1 t2' -> t1 @ t2 ->r1 t1 @ t2'
  | red1abs ty t t'    : t ->r1 t' -> abs ty t ->r1 abs ty t'
  | red1uapp t t' ty   : t ->r1 t' -> t @' ty ->r1 t' @' ty
  | red1uabs t t'      : t ->r1 t' -> uabs t ->r1 uabs t'
  where "t ->r1 t'" := (reduction1 t t').

Notation reduction := [* reduction1].
Infix "->r" := reduction (at level 70, no associativity).

Hint Constructors reduction1.

Fixpoint typing_rec (ctx : context typ) (t : term) : option typ :=
  match t with
    | var n => nth None ctx n
    | tl @ tr =>
      if typing_rec ctx tl is Some (tyl :->: tyr)
        then (if typing_rec ctx tr == Some tyl then Some tyr else None)
        else None
    | abs ty t => omap (tyfun ty) (typing_rec (Some ty :: ctx) t)
    | t @' ty =>
      if typing_rec ctx t is Some (tyabs ty')
        then Some (subst_typ 0 [:: ty] ty')
        else None
    | uabs t => omap tyabs (typing_rec (ctxmap (shift_typ 1 0) ctx) t)
  end.

Definition typing := nosimpl typing_rec.

Notation "ctx \|- t \: ty" := (Some ty == typing ctx t)
  (at level 69, no associativity).
Notation "ctx \|- t \: ty" := (Some (ty : typ) == typing ctx t)
  (at level 69, no associativity, only parsing).

Lemma typing_varE ctx (n : nat) (ty : typ) :
  ctx \|- n \: ty = ctxindex ctx n ty.
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

Lemma typing_absE' ctx t tyl tyl' tyr :
  ctx \|- abs tyl t \: tyl' :->: tyr =
  (tyl == tyl') && (Some tyl :: ctx \|- t \: tyr).
Proof.
  rewrite /typing /=; case: typing_rec => //=.
  - by move => tyr'; rewrite !/eq_op /= /eq_op /= -/eq_op eq_sym.
  - by rewrite andbF.
Qed.

Lemma typing_uappP ctx t ty1 ty2 :
  reflect
    (exists2 ty3, ty2 = subst_typ 0 [:: ty1] ty3 & ctx \|- t \: tyabs ty3)
    (ctx \|- t @' ty1 \: ty2).
Proof.
  apply: (iffP idP); rewrite /typing /=.
  - by move: (typing_rec ctx t) => [] // [] // ty3 /eqP [->]; exists ty3.
  - by case => t3 -> /eqP <-.
Qed.

Lemma typing_uabsP ctx t ty :
  reflect
    (exists2 ty', ty = tyabs ty' & ctxmap (shift_typ 1 0) ctx \|- t \: ty')
    (ctx \|- uabs t \: ty).
Proof.
  apply: (iffP idP); rewrite /typing /=.
  - by case: typing_rec => // ty' /eqP [] ->; exists ty'.
  - by case => ty' -> /eqP; case: typing_rec => // ty'' <-.
Qed.

Lemma typing_uabsE ctx t ty :
  ctx \|- uabs t \: tyabs ty = ctxmap (shift_typ 1 0) ctx \|- t \: ty.
Proof. by rewrite /typing /=; case: typing_rec. Qed.

Notation SN := (Acc (fun x y => reduction1 y x)).

Definition neutral (t : term) : bool :=
  match t with abs _ _ => false | uabs _ => false | _ => true end.

Lemma inj_shift_typ d c ty ty' :
  (shift_typ d c ty == shift_typ d c ty') = (ty == ty').
Proof.
  elim: ty ty' d c =>
    [n | tyl IHtyl tyr IHtyr | ty IHty] [m | tyl' tyr' | ty'] d c //=.
  - apply/eqP; elimif; case: ifP => H0; apply/eqP; move: H0;
      rewrite !eqE /= ?(eqn_add2l, eqn_add2r) //;
      (move => -> // || move/eqP => H; apply/eqP; ssromega).
  - by move: (IHtyl tyl' d c) (IHtyr tyr' d c); rewrite !eqE /= => -> ->.
  - by move: (IHty ty' d c.+1); rewrite !eqE.
Qed.

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
    elimif; rewrite shift_add_ty; elimif_omega.
Qed.

Lemma subst_shift_distr_ty n d c ts t :
  n <= c ->
  shift_typ d c (subst_typ n ts t) =
  subst_typ n (map (shift_typ d (c - n)) ts) (shift_typ d (size ts + c) t).
Proof.
  elimleq; elim: t n; congruence' => v n; rewrite size_map; elimif.
  - rewrite !nth_default ?size_map /=; elimif_omega.
  - rewrite -shift_shift_distr_ty // nth_map' /=.
    congr shift_typ; apply nth_equal; rewrite size_map; elimif_omega.
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
    first congr shift_typ; ssromega.
Qed.

Lemma subst_shift_cancel_ty3 n d c ts t :
  n <= c <= n + size ts ->
  subst_typ n ts (shift_typ d c t) =
  subst_typ n (take (c - n) ts ++ drop (c + d - n) ts)
    (shift_typ (c + d - (n + size ts)) c t).
Proof.
  case/andP; elimleq => H; elim: t n; congruence' => v n.
  rewrite size_cat size_take size_drop nth_cat nth_drop
          size_take (minn_idPl H); elimif_omega; congr shift_typ.
  - case (leqP' (c + d) (size ts)) => H0;
      [rewrite addn0 | rewrite !nth_default]; elimif_omega.
  - rewrite nth_take; elimif_omega.
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
    congr shift_typ; apply nth_equal; rewrite size_map; elimif_omega.
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
  - by move => tl IHtl tr IHtr n m; rewrite IHtl IHtr.
  - by move => ty t IHt n m; rewrite IHt.
  - by move => t IHt ty n m; rewrite IHt.
  - move => t IHt n m; rewrite {}IHt; congr uabs; elim: t 0 => //; congruence'.
Qed.

Lemma typemap_eq' f g n m t :
  (forall o t, f (o + n) t = g (o + m) t) -> typemap f n t = typemap g m t.
Proof.
  move => H; elim: t n m H => //=.
  - move => tl IHtl tr IHtr n m H; congr app; auto; apply (H 0).
  - by move => ty t IHt n m H; congr abs; auto; rewrite -(add0n n) -(add0n m).
  - by move => t IHt ty n m H; congr uapp; auto; apply (H 0).
  - by move => t IHt n m H; congr uabs; apply IHt => o ty; rewrite -!addSnnS.
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
  congr shift_term; apply typemap_eq => {v n ts} n t.
  rewrite subst_shift_cancel_ty2; first congr shift_typ; ssromega.
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
    congr (typemap _ _ (shift_term _ _ _));
      apply nth_equal; rewrite size_map; elimif_omega.
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
  rewrite nth_default /=; first congr var; ssromega.
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
    rewrite nth_map' /=; congr (shift_term _ _ (typemap _ _ _));
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
  rewrite -!shift_typemap_distr !(nth_map' (typemap _ _)) /=.
  congr (shift_term _ _ (nth _ _ _)); elim: ts => //= t ts ->; congr cons.
  rewrite typemap_compose; apply typemap_eq => {n t ts} n t.
  rewrite addn0 shift_add_ty; elimif_omega.
Qed.

Lemma redappl t1 t1' t2 : t1 ->r t1' -> t1 @ t2 ->r t1' @ t2.
Proof. apply (rtc_map' (fun x y => @red1appl x y t2)). Qed.

Lemma redappr t1 t2 t2' : t2 ->r t2' -> t1 @ t2 ->r t1 @ t2'.
Proof. apply (rtc_map' (fun x y => @red1appr t1 x y)). Qed.

Lemma redapp t1 t1' t2 t2' :
  t1 ->r t1' -> t2 ->r t2' -> t1 @ t2 ->r t1' @ t2'.
Proof.
  by move => H H0; eapply rtc_trans' with (t1' @ t2);
    [apply redappl | apply redappr].
Qed.

Lemma redabs ty t t' : t ->r t' -> abs ty t ->r abs ty t'.
Proof. apply (rtc_map' (red1abs ty)). Qed.

Lemma reduapp t t' ty : t ->r t' -> t @' ty ->r t' @' ty.
Proof. apply (rtc_map' (fun x y => @red1uapp x y ty)). Qed.

Lemma reduabs t t' : t ->r t' -> uabs t ->r uabs t'.
Proof. apply (rtc_map' red1uabs). Qed.

Hint Resolve redappl redappr redapp redabs reduapp reduabs.

Lemma shifttyp_reduction1 t t' d c :
  t ->r1 t' -> typemap (shift_typ d) c t ->r1 typemap (shift_typ d) c t'.
Proof.
  move => H; move: t t' H d c.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 d c; rewrite shifttyp_subst_distr //= subn0.
  - by move => t ty d c; rewrite substtyp_shifttyp_distr //= subn0.
Qed.

Lemma shift_reduction1 t t' d c :
  t ->r1 t' -> shift_term d c t ->r1 shift_term d c t'.
Proof.
  move => H; move: t t' H d c.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 d c; rewrite subst_shift_distr //= subn0.
  - by move => t ty d c; rewrite shift_typemap_distr.
Qed.

Lemma substtyp_reduction1 t t' tys n :
  t ->r1 t' ->
  typemap (subst_typ^~ tys) n t ->r1 typemap (subst_typ^~ tys) n t'.
Proof.
  move => H; move: t t' H tys n.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 tys n;
      rewrite substtyp_subst_distr // subn0; constructor.
  - by move => t ty tys n; rewrite substtyp_substtyp_distr //= subn0.
Qed.

Lemma subst_reduction1 t t' n m ts :
  t ->r1 t' -> subst_term n m ts t ->r1 subst_term n m ts t'.
Proof.
  move => H; move: t t' H n m ts.
  refine (reduction1_ind _ _ _ _ _ _ _) => /=; try by constructor.
  - by move => ty t1 t2 n m ts; rewrite subst_subst_distr //= !subn0.
  - by move => t ty n m ts; rewrite subst_substtyp_distr.
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
  | parredfst ty t1 t1' t2 t2' :
    t1 ->rp t1' -> t2 ->rp t2' ->
    abs ty t1 @ t2 ->rp subst_term 0 0 [:: t2'] t1'
  | parredsnd  t t' ty :
    t ->rp t' -> uabs t @' ty ->rp typemap (subst_typ^~ [:: ty]) 0 t'
  | parredvar n : var n ->rp var n
  | parredapp t1 t1' t2 t2' :
    t1 ->rp t1' -> t2 ->rp t2' -> t1 @ t2 ->rp t1' @ t2'
  | parredabs ty t t' : t ->rp t' -> abs ty t ->rp abs ty t'
  | parreduapp t t' ty : t ->rp t' -> t @' ty ->rp t' @' ty
  | parreduabs t t' : t ->rp t' -> uabs t ->rp uabs t'
  where "t ->rp t'" := (parred t t').

Fixpoint reduce_all_redex t : term :=
  match t with
    | var _ => t
    | abs ty t1 @ t2 =>
      subst_term 0 0 [:: reduce_all_redex t2] (reduce_all_redex t1)
    | t1 @ t2 => reduce_all_redex t1 @ reduce_all_redex t2
    | abs ty t' => abs ty (reduce_all_redex t')
    | uabs t @' ty =>
      typemap (subst_typ^~ [:: ty]) 0 (reduce_all_redex t)
    | t @' ty => reduce_all_redex t @' ty
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
  - move => ty t1 t1' t2 t2' H H0 H1 H2.
    apply rtc_trans' with (abs ty t1' @ t2); auto.
    apply rtc_trans' with (abs ty t1' @ t2'); auto.
    by apply rtc_step.
  - move => t t' ty H H0.
    apply rtc_trans' with (uabs t' @' ty); auto.
    by apply rtc_step.
Qed.

Lemma shift_parred t t' d c :
  t ->rp t' -> shift_term d c t ->rp shift_term d c t'.
Proof.
  move => H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _) => //=; try by constructor.
  - by move => t1 t1' t2 t2' ty H H0 H1 H2 d c;
      rewrite subst_shift_distr //= subn0; auto.
  - by move => t t' ty H H0 d c; rewrite shift_typemap_distr; auto.
Qed.

Lemma shifttyp_parred t t' d c :
  t ->rp t' -> typemap (shift_typ d) c t ->rp typemap (shift_typ d) c t'.
Proof.
  move => H; move: t t' H d c.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => t1 t1' t2 t2' ty H H0 H1 H2 d c;
      rewrite shifttyp_subst_distr //= subn0; auto.
  - by move => t t' ty H H0 n m;
      rewrite substtyp_shifttyp_distr //= subn0; auto.
Qed.

Lemma substtyp_parred n tys t t' :
  t ->rp t' ->
  typemap (subst_typ^~ tys) n t ->rp typemap (subst_typ^~ tys) n t'.
Proof.
  move => H; move: t t' H n.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => t1 t1' t2 t2' ty H H0 H1 H2 n;
      rewrite substtyp_subst_distr //= subn0; auto.
  - by move => t t' ty H H0 n;
      rewrite substtyp_substtyp_distr //= subn0; auto.
Qed.

Lemma subst_parred n m ps t t' :
  Forall (prod_curry parred) ps -> t ->rp t' ->
  subst_term n m (unzip1 ps) t ->rp subst_term n m (unzip2 ps) t'.
Proof.
  move => H H0; move: t t' H0 n m.
  refine (parred_ind _ _ _ _ _ _ _) => /=; auto.
  - by move => tl tl' tr tr' ty H0 H1 H2 H3 n m;
      rewrite subst_subst_distr //= !subn0; auto.
  - by move => t t' ty H0 H1 n m; rewrite subst_substtyp_distr //=; auto.
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
  ctx1 <=c ctx2 -> ctx1 \|- t \: ty -> ctx2 \|- t \: ty.
Proof.
  elim: t ty ctx1 ctx2 =>
    [n | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] ty ctx1 ctx2.
  - move/ctxleqP; apply.
  - by move => H /typing_appP [tyl H0 H1]; apply/typing_appP;
      exists tyl; [apply (IHtl _ ctx1) | apply (IHtr _ ctx1)].
  - by move => H /typing_absP [tyr -> H0]; rewrite typing_absE;
      move: H0; apply IHt; rewrite ctxleqE eqxx.
  - by move => H /typing_uappP [tyl -> H0]; apply/typing_uappP;
      exists tyl => //; move: H0; apply IHt.
  - by move => H /typing_uabsP [ty' -> H0]; rewrite typing_uabsE;
      move: H0; apply IHt, ctxleq_map.
Qed.

Lemma typing_shifttyp d c ctx t :
  typing (ctxmap (shift_typ d c) ctx) (typemap (shift_typ d) c t) =
  omap (shift_typ d c) (typing ctx t).
Proof.
  rewrite /typing.
  elim: t d c ctx => /=
    [n | tl IHtl tr IHtr | ty t IHt | t IHt ty | t IHt] d c ctx.
  - by rewrite (nth_map' (omap _)) /=.
  - rewrite IHtl /=; move: (typing_rec ctx tl) => [] // [] //= tyl tyr.
    by rewrite IHtr; case: typing_rec => //= tyl';
      rewrite !eqE /= inj_shift_typ; case: ifP.
  - by move: (IHt d c (Some ty :: ctx)) => /= ->; case: typing_rec.
  - rewrite IHt; move: (typing_rec ctx t) => [] // [] //= t'.
    by rewrite subst_shift_distr_ty //= subn0.
  - have H ty: omap (shift_typ d c) (omap tyabs ty) =
               omap tyabs (omap (shift_typ d c.+1) ty) by case: ty.
    by rewrite {}H -IHt; congr (omap tyabs (typing_rec _ _));
      rewrite -!map_comp; apply eq_map; case => //= ty';
      rewrite shift_shift_distr_ty.
Qed.

Lemma substtyp_preserves_typing n tys ctx t ty :
  ctx \|- t \: ty ->
  ctxmap (subst_typ n tys) ctx \|-
    typemap (subst_typ^~ tys) n t \: subst_typ n tys ty.
Proof.
  elim: t ty n ctx =>
    [m | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] ty n ctx /=.
  - by apply ctxindex_map.
  - by case/typing_appP => tyl H H0; apply/typing_appP;
      exists (subst_typ n tys tyl); [apply (IHtl (tyl :->: ty)) | apply IHtr].
  - by case/typing_absP => tyr -> H; rewrite /= typing_absE; move: H; apply IHt.
  - case/typing_uappP => tyl -> H; apply/typing_uappP;
      exists (subst_typ n.+1 tys tyl).
    + by rewrite subst_subst_distr_ty //= subn0.
    + by move: H; apply IHt.
  - case/typing_uabsP => ty' -> H; rewrite /= typing_uabsE.
    suff ->: ctxmap (shift_typ 1 0) (ctxmap (subst_typ n tys) ctx) =
             ctxmap (subst_typ n.+1 tys) (ctxmap (shift_typ 1 0) ctx) by
      apply IHt.
    by rewrite -!map_comp; apply eq_map;
      case => //= ty''; rewrite shift_subst_distr_ty.
Qed.

Lemma typing_shift t c ctx1 ctx2 :
  typing (ctxinsert ctx2 ctx1 c) (shift_term (size ctx2) c t) = typing ctx1 t.
Proof.
  rewrite /typing; elim: t c ctx1 ctx2 =>
    /= [n | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] c ctx1 ctx2.
  - rewrite nth_insert; elimif_omega.
  - by rewrite IHtl IHtr.
  - by rewrite -(IHt c.+1 _ ctx2).
  - by rewrite IHt.
  - by rewrite map_insert /= -(size_map (omap (shift_typ 1 0)) ctx2) IHt.
Qed.

Lemma subject_subst t ty n m ctx ctx' :
  all (fun p => drop n ctx \|- typemap (shift_typ m) 0 p.1 \: p.2) ctx' ->
  ctxinsert [seq Some p.2 | p <- ctx'] ctx n \|- t \: ty ->
  ctx \|- subst_term n m (unzip1 ctx') t \: ty.
Proof.
  elim: t ty n m ctx ctx' =>
    [v | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] ty n m ctx ctx' H.
  - rewrite /typing /= nth_insert !size_map => /eqP ->; elimif.
    + apply/eqP/esym; rewrite nth_default ?size_map /=; elimif_omega.
    + rewrite -/typing !(nth_map (var 0, tyvar 0)) //.
      case: {ty v H0} (nth _ _ _) (all_nthP (var 0, tyvar 0) H v H0) => t ty.
      rewrite /= -(typing_shift _ 0 _ (ctxinsert [::] (take n ctx) n))
              size_insert size_take minnC minKn add0n shift_typemap_distr.
      apply ctxleq_preserves_typing.
      rewrite /insert take0 sub0n take_minn minnn size_take minnE subKn
              ?leq_subr //= drop_take_nil cats0 drop0 -catA
              -{4}(cat_take_drop n ctx) ctxleq_appl.
      by case (leqP' n (size ctx)) => //= H0;
        rewrite drop_oversize ?(ltnW H0) //= cats0;
        apply/ctxleqP => /= i ty' /eqP; rewrite nth_nseq if_same.
  - by case/typing_appP => /= tyl H0 H1; apply/typing_appP; exists tyl; auto.
  - by case/typing_absP => /= tyr -> H0; rewrite typing_absE; apply IHt.
  - by case/typing_uappP => /= tyl -> H0; apply/typing_uappP; exists tyl; auto.
  - case/typing_uabsP => /= ty' -> H0;
      rewrite typing_uabsE -(addn0 m.+1) -subst_shifttyp_app.
    set ctx'' := (map _ (map _ _)).
    have {ctx''} ->: ctx'' = unzip1
        [seq (typemap (shift_typ m.+1) 0 p.1, shift_typ 1 0 p.2) | p <- ctx']
      by rewrite /unzip1 /ctx'' -!map_comp /comp /=.
    apply IHt.
    + move: H {t ty IHt H0}; rewrite all_map; apply sub_all.
      rewrite /subpred /preim /pred_of_simpl; case => /= t ty.
      by rewrite -map_drop shifttyp_zero -(@shifttyp_add m _ 1 0) //
                 typing_shifttyp; case: typing => // ty'' /eqP [] <-.
    + by move: H0; rewrite map_insert -!map_comp.
Qed.

Lemma subject_subst0 t ty ctx ctx' :
  all (fun p => ctx \|- p.1 \: p.2) ctx' ->
  [seq Some p.2 | p <- ctx'] ++ ctx \|- t \: ty ->
  ctx \|- subst_term 0 0 (unzip1 ctx') t \: ty.
Proof.
  move => H; move: (@subject_subst t ty 0 0 ctx ctx');
    rewrite /insert take0 sub0n drop0 /=; apply; move: H.
  by apply sub_all; case => t' ty' /=; rewrite shifttyp_zero.
Qed.

Lemma subject_subst0' ctx tyl tyr t t' :
  Some tyl :: ctx \|- t \: tyr -> ctx \|- t' \: tyl ->
  ctx \|- subst_term 0 0 [:: t'] t \: tyr.
Proof.
  by move => H H0;
    apply (@subject_subst0 _ _ _ [:: (t', tyl)]); rewrite //= andbT.
Qed.

Theorem subject_reduction ctx t t' ty :
  t ->r1 t' -> ctx \|- t \: ty -> ctx \|- t' \: ty.
Proof.
  move => H; move: t t' H ctx ty; refine (reduction1_ind _ _ _ _ _ _ _) => /=.
  - by move => tyl t1 t2 ctx ty
      /typing_appP [tyl']; rewrite typing_absE' => /andP [] /eqP <- H H0;
      apply (subject_subst0' H).
  - move => t tyr ctx ty /typing_uappP [tyl] ->; rewrite typing_uabsE.
    move/(substtyp_preserves_typing 0 [:: tyr]).
    set ctx' := ctxmap _ _; have {ctx'} -> //: ctx' = ctx.
    rewrite {}/ctx' -map_comp -{2}(map_id ctx).
    apply eq_map; case => //= ty'.
    by rewrite subst_shift_cancel_ty2 //= shift_zero_ty.
  - by move => t1 t1' t2 H H0 ctx ty /typing_appP [tyl H1 H2];
      apply/typing_appP; exists tyl; auto.
  - by move => t1 t2 t2' H H0 ctx ty /typing_appP [tyl H1 H2];
      apply/typing_appP; exists tyl; auto.
  - by move => tyl t t' H H0 ctx ty /typing_absP [tyr -> H1];
      rewrite typing_absE; auto.
  - by move => t t' tyr H H0 ctx ty /typing_uappP [tyl -> H1];
      apply/typing_uappP; exists tyl; auto.
  - by move => t t' H H0 ctx ty /typing_uabsP [ty' -> H1];
      rewrite typing_uabsE; auto.
Qed.

End subject_reduction_proof.

Module strong_normalization_proof_typefree.

Section CRs.
Variable (P : term -> Prop).
Definition CR1 := forall t, P t -> SN t.
Definition CR2 := forall t t', t ->r1 t' -> P t -> P t'.
Definition CR3 := forall t, neutral t -> (forall t', t ->r1 t' -> P t') -> P t.
Record RC : Prop := reducibility_candidate
  { rc_cr1 : CR1 ; rc_cr2 : CR2 ; rc_cr3 : CR3 }.
End CRs.

Lemma CR2' P t t' : RC P -> t ->r t' -> P t -> P t'.
Proof.
  move => H; move: t t'.
  refine (clos_refl_trans_1n_ind _ _ _ _ _) => //= x y z H0 H1 H2 H3.
  by apply H2, (rc_cr2 H H0).
Qed.

Lemma CR4 P t : RC P -> neutral t -> (forall t', ~ t ->r1 t') -> P t.
Proof. by move/rc_cr3 => H H0 H1; apply H => // t' /H1. Qed.

Lemma CR4' P (v : nat) : RC P -> P v.
Proof. by move/CR4; apply => // t' H; inversion H. Qed.

Lemma snorm_isrc : RC SN.
Proof.
  constructor; move => /=; try tauto.
  - by move => t t' H []; apply.
  - by move => t H H0; constructor => t' H1; apply H0.
Qed.

Lemma rcfun_isrc P Q :
  RC P -> RC Q -> RC (fun u => forall v, P v -> Q (u @ v)).
Proof.
  move => H H0; constructor; move => /=.
  - by move => t /(_ 0 (CR4' _ H)) /(rc_cr1 H0);
      apply (acc_preservation (f := app^~_)); constructor.
  - by move => t t' H1 H2 v /H2; apply (rc_cr2 H0); constructor.
  - move => t1 H1 H2 t2 H3; move: t2 {H3} (rc_cr1 H H3) (H3).
    refine (Acc_ind _ _) => t2 _ H3 H4.
    apply (rc_cr3 H0) => //= t3 H5; move: H1; inversion H5;
      subst => //= _; auto; apply H3 => //; apply (rc_cr2 H H8 H4).
Qed.

Fixpoint reducible ty (preds : seq (term -> Prop)) : term -> Prop :=
  match ty with
    | tyvar v => nth SN preds v
    | tyfun tyl tyr => fun t =>
      forall t', reducible tyl preds t' -> reducible tyr preds (t @ t')
    | tyabs ty => fun t =>
      forall ty' P, RC P -> reducible ty (P :: preds) (t @' ty')
  end.

Lemma reducibility_isrc ty preds : Forall RC preds -> RC (reducible ty preds).
Proof.
  elim: ty preds => /= [n | tyl IHtyl tyr IHtyr | ty IHty] preds.
  - move/Forall_nth /(_ _ n); case: (ltnP n (size preds)).
    + by move => _; apply.
    + by move => H _; rewrite (nth_default _ H); apply snorm_isrc.
  - by move => H; apply rcfun_isrc; [apply IHtyl | apply IHtyr].
  - move => H; constructor.
    + move => /= t /(_ 0 SN snorm_isrc)
        /(rc_cr1 (IHty (_ :: _) (conj snorm_isrc H))).
      by apply (acc_preservation (f := uapp^~_)) => x y H0; constructor.
    + move => /= t t' H0 H1 ty' P H2; move: (H1 ty' _ H2).
      by apply (rc_cr2 (IHty (_ :: _) (conj H2 H))); constructor.
    + move => /= t H0 H1 ty' P H2.
      apply (rc_cr3 (IHty (_ :: _) (conj H2 H))) => //= t' H3.
      by move: H0; inversion H3; subst => //= _; apply H1.
Qed.

Lemma shift_reducibility c ty preds preds' t :
  c <= size preds ->
  (reducible (shift_typ (size preds') c ty) (insert preds' preds SN c) t <->
   reducible ty preds t).
Proof.
  elim: ty c preds t => [v | tyl IHtyl tyr IHtyr | ty IHty] c preds t H.
  - rewrite /= nth_insert; elimif_omega.
  - by split => /= H0 t' /(IHtyl c _ _ H) /H0 /(IHtyr c _ _ H).
  - by split => H0 ty' P H1; apply (IHty c.+1 (P :: preds)) => //; apply H0.
Qed.

Lemma subst_reducibility ty preds n tys t :
  n <= size preds ->
  (reducible (subst_typ n tys ty) preds t <->
   reducible ty
     (insert [seq reducible ty (drop n preds) | ty <- tys] preds SN n) t).
Proof.
  elim: ty preds n tys t => [v | tyl IHtyl tyr IHtyr | ty IHty] preds n tys t.
  - rewrite /= nth_insert size_map; elimif_omega.
    + by rewrite nth_default ?leq_addr //= addnC.
    + move => H0.
      rewrite (nth_map (tyvar (v - size tys))) //=.
      move: (shift_reducibility (nth (tyvar (v - size tys)) tys v)
        (take n preds) t (leq0n (size (drop n preds)))).
      by rewrite /insert take0 drop0 /= cat_take_drop size_takel.
  - by move => H /=; split => H0 t' /IHtyl => /(_ H) /H0 /IHtyr => /(_ H).
  - move => H /=; split => H0 ty' P /(H0 ty') {H0}.
    + by move/IHty => /= /(_ H); rewrite /insert /= subSS.
    + by move => H0; apply IHty.
Qed.

Lemma abs_reducibility t tyl tyr tys preds :
  Forall RC preds ->
  (forall t',
   reducible tyl preds t' ->
   reducible tyr preds (subst_term 0 0 [:: t'] t)) ->
  reducible (tyl :->: tyr) preds (abs (subst_typ 0 tys tyl) t).
Proof.
  move => /= H.
  move: (reducible tyl preds) (reducible tyr preds)
        (reducibility_isrc tyl H) (reducibility_isrc tyr H)
    => {H} P Q HP HQ H t' H0.
  have H1: SN t by
    move: (rc_cr1 HQ (H _ H0));
      apply acc_preservation => x y; apply subst_reduction1.
  move: t t' {H H0} H1 (rc_cr1 HP H0) (H0) (H _ H0);
    refine (Acc_ind2 _) => t t' IHt IHt' H H0.
  apply rc_cr3 => // t'' H1; inversion H1; subst => //.
  - by inversion H5; subst; apply IHt => //;
      apply (rc_cr2 HQ (subst_reduction1 0 0 [:: t'] H6)).
  - apply IHt' => //; first by apply (rc_cr2 HP H5).
    move: H0; apply (CR2' HQ).
    by apply (@subst_reduction t 0 0 [:: (t', t2')]) => /=;
      intuition apply rtc_step.
Qed.

Lemma uabs_reducibility t ty preds :
  Forall RC preds ->
  (forall v P, RC P ->
   reducible ty (P :: preds) (typemap (subst_typ^~ [:: v]) 0 t)) ->
  reducible (tyabs ty) preds (uabs t).
Proof.
  move => /= H H0 ty' P H1.
  move: (reducible _ _) (@reducibility_isrc ty (P :: preds))
    (H0 ty' P H1) => P' /= /(_ (conj H1 H)) {H H0 H1} H H0.
  have H1: SN t by
    move: (rc_cr1 H H0);
      apply acc_preservation => x y; apply substtyp_reduction1.
  move: t H1 H0; refine (Acc_ind _ _) => t _ H0 H1.
  apply (rc_cr3 H) => //= t' H2; inversion H2; subst => //.
  inversion H6; subst; apply H0 => //.
  apply (rc_cr2 H (substtyp_reduction1 _ _ H4) H1).
Qed.

Lemma uapp_reducibility t ty ty' tys preds :
  Forall RC preds -> reducible (tyabs ty) preds t ->
  reducible (subst_typ 0 [:: ty'] ty) preds (t @' subst_typ 0 tys ty').
Proof.
  move => /= H H0.
  apply subst_reducibility => //=.
  rewrite /insert take0 sub0n !drop0 /=.
  by apply H0, reducibility_isrc.
Qed.

Lemma reduce_lemma ctx preds t ty :
  [seq Some c.2 | c <- ctx] \|- t \: ty ->
  Forall RC (unzip2 preds) ->
  Forall (fun c => reducible c.2 (unzip2 preds) c.1) ctx ->
  reducible ty (unzip2 preds)
    (subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t)).
Proof.
  elim: t ty ctx preds => /=.
  - move => v ty ctx preds H H0 H1.
    rewrite shifttyp_zero shift_zero subn0 size_map.
    elim: ctx v H H1 => //=; first by case.
    case => t ty' ctx IH [] //=.
    + by case/eqP => <- [].
    + by move => v H [H1 H2]; rewrite subSS; apply IH.
  - move => tl IHtl tr IHtr ty ctx preds /typing_appP [tyl H H0] H1 H2.
    by move: (IHtl (tyl :->: ty) ctx preds H H1 H2) => /=; apply; apply IHtr.
  - move => tyl t IHt ty ctx preds /typing_absP [tyr -> H] H0 H1.
    apply abs_reducibility => // t' H2.
    by rewrite subst_app //=; apply (IHt tyr ((t', tyl) :: ctx)).
  - move => t IHt tyr ty ctx preds /typing_uappP [tyl -> H] H0 H1.
    by apply uapp_reducibility => //; apply IHt.
  - move => t IHt ty ctx preds /typing_uabsP [ty' ->];
      rewrite -map_comp /funcomp /= => H H0 H1.
    apply uabs_reducibility => // v P H2.
    rewrite -(subst_substtyp_distr 0 [:: v]) // typemap_compose /=.
    have /(typemap_eq 0 t) -> : forall i ty,
      subst_typ (i + 0) [:: v] (subst_typ (i + 1) (unzip1 preds) ty) =
      subst_typ i (v :: unzip1 preds) ty by
        move => i ty''; rewrite addn0 addn1 subst_app_ty.
    move: (IHt ty' [seq (c.1, shift_typ 1 0 c.2) | c <- ctx] ((v, P) :: preds)).
    rewrite /unzip1 -!map_comp /comp /=; apply => //=.
    apply Forall_map; move: H1; rewrite /comp /=; apply Forall_impl =>
      {t ty IHt H H0 H2} [[t ty]] /=
      /(proj2 (shift_reducibility ty [:: P] t (leq0n _))).
    by rewrite /insert take0 drop0 sub0n /=; apply.
Qed.

Theorem typed_term_is_snorm ctx t ty : ctx \|- t \: ty -> SN t.
Proof.
  move => H.
  move: (@reduce_lemma
    (map (oapp (pair (var 0)) (var 0, tyvar 0)) ctx) [::] t ty) => /=.
  rewrite -map_comp /comp /=.
  have {H} H:
    [seq Some (oapp (pair (var 0)) (var 0, tyvar 0) c).2 | c <- ctx] \|- t \: ty
    by move: H; apply subject_reduction_proof.ctxleq_preserves_typing;
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

Notation bottom := (tyabs (tyvar 0)).
Notation "# ctx" := (rcons ctx (Some bottom)) (at level 65, no associativity).

Section CRs.
Variable (ctx : context typ) (ty : typ) (P : term -> Prop).
Definition CR1 := forall t, #ctx \|- t \: ty -> P t -> SN t.
Definition CR2 := forall t t', #ctx \|- t \: ty -> t ->r1 t' -> P t -> P t'.
Definition CR3 := forall t,
  #ctx \|- t \: ty -> neutral t -> (forall t', t ->r1 t' -> P t') -> P t.
Record RC : Prop := reducibility_candidate
  { rc_cr1 : CR1 ; rc_cr2 : CR2 ; rc_cr3 : CR3 }.
End CRs.

Lemma CR2' ctx ty P t t' :
  RC ctx ty P -> #ctx \|- t \: ty -> t ->r t' -> P t -> P t'.
Proof.
  move => H H0 H1; move: t t' H1 H0.
  refine (clos_refl_trans_1n_ind _ _ _ _ _) => //= x y z H0 H1 H2 H3 H4.
  by apply H2; [apply (subject_reduction H0) | apply (rc_cr2 H H3)].
Qed.

Lemma CR4 ctx ty P t : RC ctx ty P ->
  #ctx \|- t \: ty -> neutral t -> (forall t', ~ t ->r1 t') -> P t.
Proof. by move/rc_cr3 => H H0 H1 H2; apply H => // t' /H2. Qed.

Lemma CR4' ctx ty P (v : nat) : RC ctx ty P -> ctxindex (#ctx) v ty -> P v.
Proof. move/CR4 => H H0; apply H => // => t' H1; inversion H1. Qed.

Lemma snorm_isrc ctx ty : RC ctx ty SN.
Proof.
  constructor; move => /=; auto.
  - by move => t t' H H0 []; apply.
  - by move => t _ _ /(Acc_intro t).
Qed.

Lemma rcfun_isrc ctx tyl tyr P Q :
  RC ctx tyl P -> RC ctx tyr Q ->
  RC ctx (tyl :->: tyr)
    (fun u => forall v, #ctx \|- v \: tyl -> P v -> Q (u @ v)).
Proof.
  move => HP HQ; constructor; move => /=.
  - move => t H /(_ (size ctx @' tyl)).
    have H0 : #ctx \|- size ctx @' tyl \: tyl by
      rewrite /typing /= nth_rcons ltnn eqxx /= shift_zero_ty.
    have H1 t': ~ size ctx @' tyl ->r1 t' by
      move => H1; inversion H1; subst; inversion H5.
    move/(_ H0 (CR4 HP H0 erefl H1))/(rc_cr1 HQ) => {H1}.
    have -> : #ctx \|- t @ (size ctx @' tyl) \: tyr by
      apply/typing_appP; exists tyl.
    by move/(_ erefl); apply (acc_preservation (f := app^~_)); auto.
  - move => t t' H H0 H1 v H2 /(H1 _ H2); apply (rc_cr2 HQ).
    + by apply/typing_appP; exists tyl.
    + by constructor.
  - move => t H H0 H1 v H2 H3.
    move: v {H2 H3} (rc_cr1 HP H2 H3) (H2) (H3).
    refine (Acc_ind _ _) => v _ IH H2 H3.
    apply (rc_cr3 HQ) => //=; first by apply/typing_appP; exists tyl.
    move => t'' H4; move: H0; inversion H4; subst => //= _.
    + by apply (H1 _ H7).
    + apply IH => //.
      * by apply (subject_reduction H7).
      * by apply (rc_cr2 HP H2 H7).
Qed.

Fixpoint reducible ctx ty (preds : seq (typ * (term -> Prop))) t : Prop :=
  match ty with
    | tyvar v => nth SN (unzip2 preds) v t
    | tyfun tyl tyr => forall v,
      #ctx \|- v \: subst_typ 0 (unzip1 preds) tyl ->
        reducible ctx tyl preds v -> reducible ctx tyr preds (t @ v)
    | tyabs ty =>
      forall ty' P, RC ctx ty' P ->
        reducible ctx ty ((ty', P) :: preds) (t @' ty')
  end.

Lemma reducibility_isrc ctx ty preds :
  Forall (fun p => RC ctx p.1 p.2) preds ->
  RC ctx (subst_typ 0 (unzip1 preds) ty) (reducible ctx ty preds).
Proof.
  elim: ty preds => /= [n | tyl IHtyl tyr IHtyr | ty IHty] preds.
  - rewrite shift_zero_ty subn0.
    elim: preds n => [| P preds IH []] /=.
    + move => n _; rewrite !nth_nil /= !subn0; apply snorm_isrc.
    + by case.
    + by move => n [H] /(IH n) {IH}; rewrite !subSS.
  - by move => H; apply rcfun_isrc; [apply IHtyl | apply IHtyr].
  - move => H; constructor.
    + move => /= t H0 /(_ 0 _ (snorm_isrc _ _))
        /(rc_cr1 (IHty ((_, _) :: _) (conj (snorm_isrc _ _) H))) /=.
      suff: #ctx \|- t @' 0 \: subst_typ 0 (tyvar 0 :: unzip1 preds) ty by
        move => -> /(_ erefl);
        apply (acc_preservation (f := uapp^~_)) => x y H1; constructor.
      by apply/typing_uappP;
        exists (subst_typ 1 (unzip1 preds) ty) => //; rewrite subst_app_ty.
    + move => /= t t' H0 H1 H2 ty' P H3.
      move: (H2 _ _ H3); apply (rc_cr2 (IHty ((_, _) :: _) (conj H3 H))).
      * by apply/typing_uappP;
          exists (subst_typ 1 (unzip1 preds) ty) => //; rewrite subst_app_ty.
      * by constructor.
    + move => /= t H0 H1 H2 ty' P H3.
      apply (rc_cr3 (IHty ((_, _) :: _) (conj H3 H))) => //=.
      + by apply/typing_uappP;
          exists (subst_typ 1 (unzip1 preds) ty) => //; rewrite subst_app_ty.
      * by move => t' H4; move: H0; inversion H4; subst => //= _; apply H2.
Qed.

Lemma shift_reducibility c ty preds preds' ctx t :
  c <= size preds ->
  (reducible ctx (shift_typ (size preds') c ty)
     (insert preds' preds (tyvar 0, SN) c) t <->
   reducible ctx ty preds t).
Proof.
  elim: ty c preds t => [v | tyl IHtyl tyr IHtyr | ty IHty] c preds t H.
  - rewrite /= /unzip2 map_insert nth_insert size_map; elimif_omega.
  - rewrite /= /unzip1 map_insert -(size_map (@fst _ _)) /=
            !subst_shift_cancel_ty4 ?size_map //.
    by split => H0 v H1 /(IHtyl c _ _ H) /(H0 _ H1) /(IHtyr c _ _ H).
  - by split => /= H0 ty' P H1;
      apply (IHty c.+1 ((ty', P) :: preds)) => //; apply H0.
Qed.

Lemma subst_reducibility ty preds n tys ctx t :
  n <= size preds ->
  (reducible ctx (subst_typ n tys ty) preds t <->
   reducible ctx ty
     (insert [seq (subst_typ 0 (drop n (unzip1 preds)) ty,
                   reducible ctx ty (drop n preds)) | ty <- tys]
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
        (take n preds) ctx t (leq0n (size (drop n preds)))).
      by rewrite /insert take0 drop0 /= cat_take_drop size_takel.
  - by move => H /=;
      split => H0 t' H1 /IHtyl => /(_ H) /H0 /IHtyr => /(_ H); apply; move: H1;
      rewrite /unzip1 map_insert -map_comp /= subst_subst_compose_ty ?size_map.
  - move => H /=; split => H0 ty' P /H0.
    + by move/IHty => /(_ H); rewrite /insert /= subSS.
    + by move => H1; apply IHty.
Qed.

Lemma abs_reducibility tyl tyr preds ctx t :
  #ctx \|- abs (subst_typ 0 (unzip1 preds) tyl) t
        \: subst_typ 0 (unzip1 preds) (tyl :->: tyr) ->
  Forall (fun p => RC ctx p.1 p.2) preds ->
  (forall t',
   #ctx \|- t' \: subst_typ 0 (unzip1 preds) tyl ->
   reducible ctx tyl preds t' ->
   reducible ctx tyr preds (subst_term 0 0 [:: t'] t)) ->
  reducible ctx (tyl :->: tyr) preds (abs (subst_typ 0 (unzip1 preds) tyl) t).
Proof.
  rewrite /= typing_absE => H H0.
  move: (reducible ctx tyl preds) (reducible ctx tyr preds)
    (reducibility_isrc tyl H0) (reducibility_isrc tyr H0) =>
    {H0} P Q HP HQ H0 t' H1 H2.
  have H3: SN t by
    move: (rc_cr1 HQ (subject_subst0' H H1) (H0 t' H1 H2));
      apply acc_preservation => x y; apply subst_reduction1.
  move: t t' H3 {H0 H1 H2} (rc_cr1 HP H1 H2) H (H1) (H2) (H0 _ H1 H2).
  refine (Acc_ind2 _) => t t' IHt IHt' H H0 H1 H2; apply (rc_cr3 HQ) => //=.
  - by apply/typing_appP;
      exists (subst_typ 0 (unzip1 preds) tyl) => //; rewrite typing_absE.
  - move => t'' H3; inversion H3; subst => //.
    + inversion H7; subst; apply IHt => //.
      * by move: H; apply subject_reduction.
      * by apply (@rc_cr2 _ _ _ HQ (subst_term 0 0 [:: t'] t)) => //;
          [apply (subject_subst0' H) | apply subst_reduction1].
    + apply IHt' => //.
      * by apply (subject_reduction H7).
      * by apply (rc_cr2 HP H0 H7).
      * move: H2; apply (CR2' HQ); first by apply (subject_subst0' H).
        by apply (@subst_reduction t 0 0 [:: (t', t2')]) => /=;
          intuition apply rtc_step.
Qed.

Lemma uabs_reducibility ty preds ctx t :
  #ctx \|- uabs t \: subst_typ 0 (unzip1 preds) (tyabs ty) ->
  Forall (fun p => RC ctx p.1 p.2) preds ->
  (forall v P, RC ctx v P ->
   reducible ctx ty ((v, P) :: preds) (typemap (subst_typ^~ [:: v]) 0 t)) ->
  reducible ctx (tyabs ty) preds (uabs t).
Proof.
  rewrite /= typing_uabsE => H H0 H1 ty' P H2.
  move: (substtyp_preserves_typing 0 [:: ty'] H) (H1 ty' P H2).
  have ->: ctxmap (subst_typ 0 [:: ty']) (ctxmap (shift_typ 1 0) (#ctx)) = #ctx
    by rewrite !map_rcons /=; congr rcons;
      elim: ctx {H H0 H1 H2} => //= ty'' ctx {2}<-; case: ty'' => //= ty'';
      rewrite subst_shift_cancel_ty2 //= subnn shift_zero_ty.
  move: (reducible _ _) (@reducibility_isrc ctx ty ((ty', P) :: preds))
    => P' /= /(_ (conj H2 H0)) {H0 H1 H2}.
  rewrite -typing_uabsE -/(subst_typ 0 _ (tyabs _)) in H.
  rewrite subst_app_ty /= => H0 H1 H2.
  have H3: SN t by
    move: (rc_cr1 H0 H1 H2);
      apply acc_preservation => x y; apply substtyp_reduction1.
  move: t H3 H H1 H2; refine (Acc_ind _ _) => t _ IH H H1 H2.
  apply (rc_cr3 H0) => //=.
  - by apply/typing_uappP;
      exists (subst_typ 1 (unzip1 preds) ty) => //; rewrite subst_app_ty.
  - move => t' H4; inversion H4; subst => //.
    inversion H7; subst; apply IH => //.
    + by apply (subject_reduction H7).
    + by move: H1; apply subject_reduction, substtyp_reduction1.
    + by apply (rc_cr2 H0 H1 (substtyp_reduction1 _ _ H5) H2).
Qed.

Lemma uapp_reducibility ty ty' preds ctx t :
  Forall (fun p => RC ctx p.1 p.2) preds ->
  reducible ctx (tyabs ty) preds t ->
  reducible ctx (subst_typ 0 [:: ty'] ty) preds
    (t @' subst_typ 0 (unzip1 preds) ty').
Proof.
  move => /= H H0.
  apply subst_reducibility => //=.
  rewrite /insert take0 sub0n !drop0 /=.
  by apply H0, reducibility_isrc.
Qed.

Lemma reduce_lemma ctx ctx' preds t ty :
  [seq Some c.2 | c <- ctx] \|- t \: ty ->
  Forall (fun p => RC ctx' p.1 p.2) preds ->
  Forall (fun c => #ctx' \|- c.1 \: subst_typ 0 (unzip1 preds) c.2 /\
                   reducible ctx' c.2 preds c.1) ctx ->
  reducible ctx' ty preds
    (subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t)).
Proof.
  have Hty: forall t ty  ctx ctx' preds,
    [seq Some c.2 | c <- ctx] \|- t \: ty ->
    Forall (fun p => RC ctx' p.1 p.2) preds ->
    Forall (fun c => #ctx' \|- c.1 \: subst_typ 0 (unzip1 preds) c.2 /\
                     reducible ctx' c.2 preds c.1) ctx ->
    #ctx' \|-
      subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t) \:
      subst_typ 0 (unzip1 preds) ty.
    clear => t ty ctx ctx' preds H H0 H1.
    move: (fun t ty => @subject_subst0 t ty (#ctx')
      [seq (c.1, subst_typ 0 (unzip1 preds) c.2) | c <- ctx]).
    rewrite /unzip1 -!map_comp !/comp -/unzip1; apply => /=.
    - by elim: ctx H1 {H} => //= [[]] /= t' ty' ctx IH [] [-> _] /=.
    - by move: (substtyp_preserves_typing 0 (unzip1 preds) H);
        rewrite -map_comp; apply ctxleq_preserves_typing, ctxleq_appr.
  elim: t ty ctx ctx' preds => /=.
  - move => v ty ctx ctx' preds H H0 H1.
    rewrite shifttyp_zero shift_zero subn0 size_map.
    elim: ctx v H H1 => //=; first by case.
    case => t ty' ctx IH [] //=.
    + by case/eqP => <- [] [].
    + by move => v H [H1 H2]; rewrite subSS; apply IH.
  - move => tl IHtl tr IHtr ty ctx ctx' preds /typing_appP [tyl H H0] H1 H2.
    by move: (IHtl (tyl :->: ty) ctx ctx' preds H H1 H2) => /=;
      apply; [apply Hty | apply IHtr].
  - move => tyl t IHt ty ctx ctx' preds /typing_absP [tyr -> H] H0 H1.
    apply abs_reducibility => //;
      first by apply (Hty (abs tyl t)) => //; rewrite typing_absE.
    by move => t' H2 H3; rewrite subst_app //=;
      apply (IHt tyr ((t', tyl) :: ctx)).
  - move => t IHt tyr ty ctx ctx' preds /typing_uappP [tyl -> H] H0 H1.
    by apply uapp_reducibility => //; apply IHt.
  - move => t IHt ty ctx ctx' preds /typing_uabsP [ty' -> H] H0 H1.
    apply uabs_reducibility => //;
      first by apply (Hty (uabs t)) => //; rewrite typing_uabsE.
    move => v P H2.
    rewrite -(subst_substtyp_distr 0 [:: v]) // typemap_compose /=.
    have /(typemap_eq 0 t) -> : forall i ty,
      subst_typ (i + 0) [:: v] (subst_typ (i + 1) (unzip1 preds) ty) =
      subst_typ i (unzip1 ((v, P) :: preds)) ty by
        move => i ty''; rewrite addn0 addn1 subst_app_ty.
    move: (IHt ty'
      [seq (c.1, shift_typ 1 0 c.2) | c <- ctx] ctx' ((v, P) :: preds)).
    rewrite /unzip1 -!map_comp /comp /=; apply => //=.
    + by move: H; rewrite -map_comp /comp /=.
    + apply Forall_map; move: H1; apply Forall_impl => [[t' ty'']] /= [].
      rewrite subst_shift_cancel_ty3 //= drop0 !add0n subSS sub0n shift_zero_ty.
      case (shift_reducibility ty'' [:: (v, P)] ctx' t' (leq0n (size preds))).
      rewrite /insert take0 drop0 sub0n; auto.
Qed.

Lemma identical_substitution ctx' ctx t ty n :
  ctx' ++ ctx \|- t \: ty ->
  subst_term (size ctx') n [seq var i | i <- iota 0 (size ctx)] t = t.
Proof.
  elim: t ctx' ctx ty n => //=.
  - move => v ctx' ctx ty n; case: ifP => //; elimleq.
    rewrite /typing /= size_map size_iota -nth_map' /=
            nth_cat ltnNge leq_addr //= addKn addnC => H; congr addn.
    have H0: v < size ctx by elim: v ctx H => [| v IH] [].
    by move: (ltnW H0); rewrite -subn_eq0 => /eqP ->; rewrite nth_iota.
  - by move => tl IHtl tr IHtr ctx' ctx tyr n /typing_appP [tyl H H0];
      rewrite (IHtl _ _ (tyl :->: tyr)) // (IHtr _ _ tyl).
  - move => tyl t IHt ctx' ctx ty n /typing_absP [tyr _ H].
    rewrite (IHt (Some tyl :: ctx') _ tyr) //.
  - move => t IHt tyr ctx' ctx ty n /typing_uappP [tyl _ H].
    by rewrite (IHt ctx' ctx (tyabs tyl)).
  - move => t IHt ctx' ctx ty n /typing_uabsP [ty' _];
      rewrite map_cat => /IHt => /(_ n.+1).
    by rewrite !size_map => ->.
Qed.

Theorem typed_term_is_snorm ctx t ty : ctx \|- t \: ty -> SN t.
Proof.
  move => H.
  have {H}: map some (map (odflt (tyvar 0)) ctx) \|- t \: ty by
    move: H; apply ctxleq_preserves_typing;
      elim: ctx {t ty} => // [[]] // ty ctx H; rewrite ctxleqE eqxx.
  move: {ctx} (map _ ctx) => ctx H; move: (H).
  have ->: map some ctx =
           [seq Some c.2 | c <- zip (map var (iota 0 (size ctx))) ctx] by
    elim: {H} ctx 0 => //= {t ty} ty ctx IH n; rewrite -IH.
  move/reduce_lemma => /(_ (map some ctx) [::] I).
  rewrite /= unzip1_zip ?size_map ?size_iota ?leqnn; last by [].
  have H0: Forall
      (fun c => #[seq Some i | i <- ctx] \|- c.1 \: subst_typ 0 [::] c.2 /\
                reducible (map some ctx) c.2 [::] c.1)
      (zip (map var (iota 0 (size ctx))) ctx).
    apply Forall_nth; case => {H t ty} t ty n; rewrite
      size_zip size_map size_iota minnn nth_map' (nth_map' (@fst _ _)) /=
      -/unzip1 -/unzip2 unzip1_zip ?unzip2_zip ?size_map ?size_iota // => H;
      rewrite (nth_map 0 t var) ?size_iota // nth_iota // add0n.
    suff: #[seq Some i | i <- ctx] \|- n \: subst_typ 0 [::] (nth ty ctx n) by
      intuition apply (CR4' (@reducibility_isrc _ (nth ty ctx n) [::] I)).
    by rewrite /typing /= subst_nil_ty nth_rcons size_map H (nth_map ty).
  move/(_ H0) => {H0} /(rc_cr1 (reducibility_isrc _ _)) /= /(_ I).
  have ->: typemap (subst_typ^~ [::]) 0 t = t by
    elim: {H} t 0 => //=; move: subst_nil_ty; congruence'.
  move: (@identical_substitution [::] (map some ctx) t ty 0 H).
  rewrite subst_nil_ty /= size_map => ->.
  move/(_ (ctxleq_preserves_typing _ H)).
  by rewrite -cats1 => /(_ (ctxleq_appr _ _)).
Qed.

End strong_normalization_proof_typed.

Module strong_normalization_proof_kripke.

Import subject_reduction_proof.

Section CRs.
Variable (ty : typ) (P : context typ -> term -> Prop).
Definition CR_typed := forall ctx t, P ctx t -> ctx \|- t \: ty.
Definition CR0 := forall ctx ctx' t, ctx <=c ctx' -> P ctx t -> P ctx' t.
Definition CR1 := forall ctx t, P ctx t -> SN t.
Definition CR2 := forall ctx t t', t ->r1 t' -> P ctx t -> P ctx t'.
Definition CR3 := forall ctx t,
  ctx \|- t \: ty -> neutral t -> (forall t', t ->r1 t' -> P ctx t') -> P ctx t.
Record RC : Prop :=
  reducibility_candidate {
    rc_typed : CR_typed ;
    rc_cr0 : CR0 ;
    rc_cr1 : CR1 ;
    rc_cr2 : CR2 ;
    rc_cr3 : CR3
  }.
End CRs.

Lemma CR2' ty P ctx t t' : RC ty P -> t ->r t' -> P ctx t -> P ctx t'.
Proof.
  move => H; move: t t'.
  refine (clos_refl_trans_1n_ind _ _ _ _ _) => //= x y z H0 H1 H2 H3.
  by apply H2, (rc_cr2 H H0).
Qed.

Lemma CR4 ty P ctx t : RC ty P ->
  ctx \|- t \: ty -> neutral t -> (forall t', ~ t ->r1 t') -> P ctx t.
Proof. by move/rc_cr3 => H H0 H1 H2; apply H => // t' /H2. Qed.

Lemma CR4' ty P ctx (v : nat) : RC ty P -> ctxindex ctx v ty -> P ctx v.
Proof. move/CR4 => H H0; apply H => // t' H1; inversion H1. Qed.

Notation SN' ty := (fun ctx t => ctx \|- t \: ty /\ SN t).

Lemma snorm_isrc ty : RC ty (SN' ty).
Proof.
  (constructor; move => /=) =>
    [ctx t [] // | ctx ctx' t H [H0 H1] | ctx t [] // |
     ctx t t' H [H0 [H1]] | ctx t ]; intuition.
  - by apply (ctxleq_preserves_typing H).
  - by apply (subject_reduction H).
  - by constructor => t' /H1 [].
Qed.

Definition rcfun tyl tyr (P Q : context typ -> term -> Prop) ctx u : Prop :=
  ctx \|- u \: tyl :->: tyr /\
  forall ctx' v, ctx <=c ctx' -> P ctx' v -> Q ctx' (u @ v).

Lemma rcfun_isrc tyl tyr P Q :
  RC tyl P -> RC tyr Q -> RC (tyl :->: tyr) (rcfun tyl tyr P Q).
Proof.
  move => HP HQ; rewrite /rcfun; constructor; move => /=; first tauto.
  - move => ctx ctx' t H [H0 H1]; split; last move => ctx'' t' H2 H3.
    + by apply (ctxleq_preserves_typing H).
    + by apply (H1 ctx'' t') => //; apply ctxleq_trans with ctx'.
  - move => ctx t [H]
      /(_ _ _ (ctxleq_appr _ _) (CR4' HP (ctxindex_last ctx tyl))) /(rc_cr1 HQ).
    by apply (acc_preservation (f := app^~_)); auto.
  - move => ctx t t' H [H0 H1]; split; last move => ctx' t''.
    + by apply (subject_reduction H).
    + by move => /H1 {H1} H1 /H1 {H1}; apply (rc_cr2 HQ); constructor.
  - move => ctx t H H0 H1; split => // ctx' t' H2 H3.
    move: t' {H3} (rc_cr1 HP H3) (H3).
    refine (Acc_ind _ _) => t' _ IH H3.
    apply (rc_cr3 HQ) => //=; first (apply/typing_appP; exists tyl).
    + by apply (ctxleq_preserves_typing H2).
    + by apply (rc_typed HP).
    + move => t'' H4; move: H0; inversion H4; subst => //= _.
      * by apply (proj2 (H1 _ H7) ctx').
      * by apply IH => //; apply (rc_cr2 HP H7).
Qed.

Fixpoint reducible ty (preds : seq (typ * (context typ -> term -> Prop))) :
    context typ -> term -> Prop :=
  match ty with
    | tyvar v => nth (SN' (v - size preds)) (unzip2 preds) v
    | tyfun tyl tyr =>
      let s := subst_typ 0 (unzip1 preds) in
      rcfun (s tyl) (s tyr) (reducible tyl preds) (reducible tyr preds)
    | tyabs ty => fun ctx t =>
      ctx \|- t \: tyabs (subst_typ 1 (unzip1 preds) ty) /\
      forall ty' P, RC ty' P -> reducible ty ((ty', P) :: preds) ctx (t @' ty')
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
    + by move => /= ctx t [].
    + move => /= ctx ctx' t H0 [H1 H2]; split;
        first by move: H1; apply ctxleq_preserves_typing.
      move => ty' P H3.
      move: (rc_cr0 (IHty ((_, _) :: _) (conj H3 H))) => /(_ ctx ctx' _ H0).
      by apply; apply H2.
    + move => /= ctx t [_] /(_ 0 _ (snorm_isrc _))
        /(rc_cr1 (IHty ((_, _) :: _) (conj (snorm_isrc _) H))).
      by apply (acc_preservation (f := uapp^~_)) => x y H0; constructor.
    + move => /= ctx t t' H0 [H1 H2]; split;
        first by move: H1; apply subject_reduction.
      move => ty' P H3; move: (H2 _ _ H3).
      by apply (rc_cr2 (IHty ((_, _) :: _) (conj H3 H))); constructor.
    + move => /= ctx t H0 H1 H2; split => // ty' P H3.
      apply (rc_cr3 (IHty ((_, _) :: _) (conj H3 H))) => //=.
      + by apply/typing_uappP;
          exists (subst_typ 1 (unzip1 preds) ty) => //; rewrite subst_app_ty.
      * by move => t' H4; move: H0; inversion H4; subst => //= _; apply H2.
Qed.

Lemma shift_reducibility c ty preds preds' ctx t :
  c <= size preds ->
  (reducible (shift_typ (size preds') c ty)
     (insert preds' preds (tyvar 0, SN' 0) c) ctx t <->
   reducible ty preds ctx t).
Proof.
  elim: ty c preds ctx t => [v | tyl IHtyl tyr IHtyr | ty IHty] c preds ctx t H.
  - rewrite /= /unzip2 map_insert nth_insert size_map size_insert; elimif_omega.
    rewrite (_ : v - size preds = 0) //; ssromega.
  - rewrite /= /rcfun /unzip1 map_insert -(size_map (@fst _ _)) /=
            !subst_shift_cancel_ty4 ?size_map //.
    by split; case => H0 H1; split => // ctx' t' H2
      /(IHtyl c _ _ _ H) /(H1 _ _ H2) /(IHtyr c _ _ _ H).
  - rewrite /= /unzip1 map_insert -(size_map (@fst _ _)) -add1n
            subst_shift_cancel_ty4 ?size_map //.
    by split; case => H0 H1; split => // ty' P H2;
      apply (IHty c.+1 ((ty', P) :: preds)) => //; apply H1.
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
      by rewrite /insert take0 drop0 /= cat_take_drop size_takel.
    + by move => H; rewrite (_ : v - size preds = 0) //; ssromega.
  - move => H /=; rewrite /rcfun /= /unzip1 map_insert -!map_comp /comp /=
      -!subst_subst_compose_ty ?size_map // -/unzip1 add0n.
    by split; case => H1 H2; split =>
      // ctx' t' H3 /IHtyl => /(_ H) /(H2 _ _ H3) /IHtyr => /(_ H).
  - move => H /=; rewrite /unzip1 map_insert -!map_comp /comp /=
      -subst_subst_compose_ty ?size_map // add1n -/unzip1.
    split; case => H0 H1; split => // ty' P /H1 {H0 H1}.
    + by move/IHty => /= /(_ H); rewrite /insert /= subSS.
    + by move => H0; apply IHty.
Qed.

Lemma abs_reducibility tyl tyr preds ctx t :
  ctx \|- abs (subst_typ 0 (unzip1 preds) tyl) t
       \: subst_typ 0 (unzip1 preds) (tyl :->: tyr) ->
  Forall (fun p => RC p.1 p.2) preds ->
  (forall ctx' t', ctx <=c ctx' ->
   reducible tyl preds ctx' t' ->
   reducible tyr preds ctx' (subst_term 0 0 [:: t'] t)) ->
  reducible (tyl :->: tyr) preds ctx (abs (subst_typ 0 (unzip1 preds) tyl) t).
Proof.
  move => /= H H0.
  move: (reducible tyl preds) (reducible tyr preds)
    (reducibility_isrc tyl H0) (reducibility_isrc tyr H0) =>
    {H0} P Q HP HQ H0; split => // ctx' t' H1 H2.
  have H3: SN t by
    move: (rc_cr1 HQ (H0 _ _ H1 H2));
      apply acc_preservation => x y; apply subst_reduction1.
  move: t t' H3 {H0 H2} (rc_cr1 HP H2) H H1 (H2) (H0 _ _ H1 H2).
  refine (Acc_ind2 _) => t t' IHt IHt' H H0 H1 H2; apply (rc_cr3 HQ) => //=;
    first (apply/typing_appP; exists (subst_typ 0 (unzip1 preds) tyl)).
  - by move: H; apply ctxleq_preserves_typing.
  - by apply (rc_typed HP).
  - move => t'' H3; inversion H3; subst => //.
    + inversion H7; subst; apply IHt; auto.
      * by move: H; apply subject_reduction.
      * by apply (rc_cr2 HQ (subst_reduction1 0 0 [:: t'] H8)).
    + apply IHt' => //; first by apply (rc_cr2 HP H7).
      move: H2; apply (CR2' HQ).
      by apply (@subst_reduction t 0 0 [:: (t', t2')]) => /=;
        intuition apply rtc_step.
Qed.

Lemma uabs_reducibility ty preds ctx t :
  ctx \|- uabs t \: subst_typ 0 (unzip1 preds) (tyabs ty) ->
  Forall (fun p => RC p.1 p.2) preds ->
  (forall v P, RC v P ->
   reducible ty ((v, P) :: preds) ctx (typemap (subst_typ^~ [:: v]) 0 t)) ->
  reducible (tyabs ty) preds ctx (uabs t).
Proof.
  move => /= H H0 H1; split => // ty' P H2.
  move: (reducible _ _) (@reducibility_isrc ty ((ty', P) :: preds))
    (H1 ty' P H2) => P' /= /(_ (conj H2 H0)) {H0 H1 H2} H0 H1.
  have H2: SN t by
    move: (rc_cr1 H0 H1);
      apply acc_preservation => x y; apply substtyp_reduction1.
  move: t H2 H H1; refine (Acc_ind _ _) => t _ H1 H H2.
  apply (rc_cr3 H0) => //=.
  - by apply/typing_uappP;
      exists (subst_typ 1 (unzip1 preds) ty) => //; rewrite subst_app_ty.
  - move => t' H3; inversion H3; subst => //.
    inversion H7; subst; apply H1 => //.
    + by apply (subject_reduction H7).
    + apply (rc_cr2 H0 (substtyp_reduction1 _ _ H5) H2).
Qed.

Lemma uapp_reducibility ty ty' preds ctx t :
  Forall (fun p => RC p.1 p.2) preds ->
  reducible (tyabs ty) preds ctx t ->
  reducible (subst_typ 0 [:: ty'] ty) preds ctx
    (t @' subst_typ 0 (unzip1 preds) ty').
Proof.
  move => /= H H0.
  apply subst_reducibility => //=.
  rewrite /insert take0 sub0n !drop0 /=.
  by apply H0, reducibility_isrc.
Qed.

Lemma reduce_lemma ctx ctx' preds t ty :
  [seq Some c.2 | c <- ctx] \|- t \: ty ->
  Forall (fun p => RC p.1 p.2) preds ->
  Forall (fun c => reducible c.2 preds ctx' c.1) ctx ->
  reducible ty preds ctx'
    (subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t)).
Proof.
  have Hty: forall t ty  ctx ctx' preds,
    [seq Some c.2 | c <- ctx] \|- t \: ty ->
    Forall (fun p => RC p.1 p.2) preds ->
    Forall (fun c => reducible c.2 preds ctx' c.1) ctx ->
    ctx' \|-
      subst_term 0 0 (unzip1 ctx) (typemap (subst_typ^~ (unzip1 preds)) 0 t) \:
      subst_typ 0 (unzip1 preds) ty.
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
  - move => tl IHtl tr IHtr ty ctx ctx' preds /typing_appP [tyl H H0] H1 H2.
    by move: (IHtl (tyl :->: ty) ctx ctx' preds H H1 H2) => /= [_];
      apply => //; apply IHtr.
  - move => tyl t IHt ty ctx ctx' preds /typing_absP [tyr -> H] H0 H1.
    apply abs_reducibility => //;
      first by apply (Hty (abs tyl t)) => //; rewrite typing_absE.
    move => ctx'' t' H2 H3; rewrite subst_app //=.
    apply (IHt tyr ((t', tyl) :: ctx)) => //=; split => //; move: H1.
    by apply Forall_impl => {t' ty H H3} [[t' ty]] /=;
      apply (rc_cr0 (reducibility_isrc ty H0) H2).
  - move => t IHt tyr ty ctx ctx' preds /typing_uappP [tyl -> H] H0 H1.
    by apply uapp_reducibility => //; apply IHt.
  - move => t IHt ty ctx ctx' preds /typing_uabsP [ty' -> H] H0 H1.
    apply uabs_reducibility => //;
      first by apply (Hty (uabs t)) => //; rewrite typing_uabsE.
    move => v P H2.
    rewrite -(subst_substtyp_distr 0 [:: v]) // typemap_compose /=.
    have /(typemap_eq 0 t) -> : forall i ty,
      subst_typ (i + 0) [:: v] (subst_typ (i + 1) (unzip1 preds) ty) =
      subst_typ i (unzip1 ((v, P) :: preds)) ty by
        move => i ty''; rewrite addn0 addn1 subst_app_ty.
    move: (IHt ty'
      [seq (c.1, shift_typ 1 0 c.2) | c <- ctx] ctx' ((v, P) :: preds)).
    rewrite /unzip1 -!map_comp /comp /=; apply => //=.
    + by move: H; rewrite -map_comp /comp /=.
    + apply Forall_map; move: H1; apply Forall_impl => [[t' ty'']] /=.
      case (shift_reducibility ty'' [:: (v, P)] ctx' t' (leq0n (size preds))).
      rewrite /insert take0 drop0 sub0n => _ /=; apply.
Qed.

Theorem typed_term_is_snorm ctx t ty : ctx \|- t \: ty -> SN t.
Proof.
  move => H.
  have {H}: map some (map (odflt (tyvar 0)) ctx) \|- t \: ty by
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

End strong_normalization_proof_kripke.
