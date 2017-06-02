From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LCAC Require Import Relations_ext seq_ext_base ssrnat_ext seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Orders *)

Inductive ord := data | ofun of ord & ord.

Notation "ty ->o ty'" := (ofun ty ty') (at level 50, no associativity).

Fixpoint eqord o1 o2 :=
  match o1, o2 with
    | data, data => true
    | o1l ->o o1r, o2l ->o o2r => eqord o1l o2l && eqord o1r o2r
    | _, _ => false
  end.

Lemma eqordP : Equality.axiom eqord.
Proof.
move => o1 o2; apply: (iffP idP) => [| <-]; last by elim: o1 => //= o ->.
by elim: o1 o2 => [| o1l IHl o1r IHr] [] //= o2l o2r /andP [] /IHl -> /IHr ->.
Defined.

Canonical ord_eqMixin := EqMixin eqordP.
Canonical ord_eqType := Eval hnf in EqType ord ord_eqMixin.

(* Types *)

Inductive typ
  := tyvar of nat
   | tyfun of typ & typ
   | tyall of ord & typ
   | tyapp of typ & typ
   | tyabs of ord & typ.

Coercion tyvar : nat >-> typ.

Notation "ty ->t ty'" := (tyfun ty ty') (at level 50, no associativity).
Notation "ty @' ty'" := (tyapp ty ty') (at level 60, no associativity).

Fixpoint eqtyp t1 t2 :=
  match t1, t2 with
    | tyvar n, tyvar m => n == m
    | t1l ->t t1r, t2l ->t t2r => eqtyp t1l t2l && eqtyp t1r t2r
    | tyall o1 t1, tyall o2 t2 => (o1 == o2) && eqtyp t1 t2
    | t1l @' t1r, t2l @' t2r => eqtyp t1l t2l && eqtyp t1r t2r
    | tyabs o1 t1, tyabs o2 t2 => (o1 == o2) && eqtyp t1 t2
    | _, _ => false
  end.

Lemma eqtypP : Equality.axiom eqtyp.
Proof.
move => t1 t2; apply: (iffP idP) => [| <-].
- by elim: t1 t2 =>
    [n | t1l IHl t1r IHr | o1 t1 IH | t1l IHl t1r IHr | o1 t1 IH]
    [//= m /eqP -> | //= t2l t2r /andP [] /IHl -> /IHr -> |
     //= o2 t2 /andP [] /eqP -> /IH -> | //= t2l t2r /andP [] /IHl -> /IHr -> |
     //= o2 t2 /andP [] /eqP -> /IH ->].
- by elim: t1 => //= [t -> | o t -> | t -> | o t ->] //; rewrite andbT.
Defined.

Canonical typ_eqMixin := EqMixin eqtypP.
Canonical typ_eqType := Eval hnf in EqType typ typ_eqMixin.

Fixpoint shift_ty d c t :=
  match t with
    | tyvar n => tyvar (if c <= n then n + d else n)
    | tl ->t tr => shift_ty d c tl ->t shift_ty d c tr
    | tyall o t => tyall o (shift_ty d c.+1 t)
    | tl @' tr => shift_ty d c tl @' shift_ty d c tr
    | tyabs o t => tyabs o (shift_ty d c.+1 t)
  end.

Notation subst_tyv ts m n :=
  (shift_ty n 0 (nth (tyvar (m - n - size ts)) ts (m - n))) (only parsing).

Fixpoint subst_ty n ts t :=
  match t with
    | tyvar m => if n <= m then subst_tyv ts m n else m
    | tl ->t tr => subst_ty n ts tl ->t subst_ty n ts tr
    | tyall o t => tyall o (subst_ty n.+1 ts t)
    | tl @' tr => subst_ty n ts tl @' subst_ty n ts tr
    | tyabs o t => tyabs o (subst_ty n.+1 ts t)
  end.

Reserved Notation "t ~>ty1 t'" (at level 70, no associativity).

Inductive reduction1_ty : relation typ :=
  | tyred1fst o t1 t2    : tyabs o t1 @' t2 ~>ty1 subst_ty 0 [:: t2] t1
  | tyred1funl t1 t1' t2 : t1 ~>ty1 t1' -> t1 ->t t2 ~>ty1 t1' ->t t2
  | tyred1funr t1 t2 t2' : t2 ~>ty1 t2' -> t1 ->t t2 ~>ty1 t1 ->t t2'
  | tyred1all o t t'     : t ~>ty1 t' -> tyall o t ~>ty1 tyall o t'
  | tyred1appl t1 t1' t2 : t1 ~>ty1 t1' -> t1 @' t2 ~>ty1 t1' @' t2
  | tyred1appr t1 t2 t2' : t2 ~>ty1 t2' -> t1 @' t2 ~>ty1 t1 @' t2'
  | tyred1abs o t t'     : t ~>ty1 t' -> tyabs o t ~>ty1 tyabs o t'
where "t ~>ty1 t'" := (reduction1_ty t t').

Notation reduction_ty := [* reduction1_ty].
Infix "~>ty" := reduction_ty (at level 70, no associativity).

Hint Constructors reduction1_ty.

Fixpoint ordering_rec (ctx : context ord) (t : typ) : option ord :=
  match t with
    | tyvar n => nth None ctx n
    | tyfun tl tr =>
      if (ordering_rec ctx tl == Some data) &&
         (ordering_rec ctx tr == Some data)
      then Some data else None
    | tyall o t =>
      if ordering_rec (Some o :: ctx) t == Some data then Some data else None
    | tyabs o t => omap (ofun o) (ordering_rec (Some o :: ctx) t)
    | tyapp tl tr =>
      if ordering_rec ctx tl is Some (ol ->o or)
      then (if ordering_rec ctx tr == Some ol then Some or else None)
      else None
  end.

Definition ordering := nosimpl ordering_rec.

Notation "ctx \|-o ty \: o" := (Some o == ordering ctx ty)
  (at level 69, no associativity).
Notation "ctx \|-o ty \: o" := (Some (o : ord) == ordering ctx ty)
  (at level 69, no associativity, only parsing).

Lemma ordering_varE ctx (n : nat) (o : ord) :
  ctx \|-o n \: o = ctxindex ctx n o.
Proof. by rewrite /ordering. Qed.

Lemma ordering_funE ctx tyl tyr o :
  ctx \|-o tyl ->t tyr \: o =
  [&& ctx \|-o tyl \: data, ctx \|-o tyr \: data & o == data].
Proof.
by rewrite /ordering /= !(eq_sym _ (Some data));
  do 2 case: (Some _ =P ordering_rec _ _).
Qed.

Lemma ordering_funE' ctx tyl tyr :
  ctx \|-o tyl ->t tyr \: data =
  (ctx \|-o tyl \: data) && (ctx \|-o tyr \: data).
Proof. by rewrite ordering_funE eqxx andbT. Qed.

Lemma ordering_allE ctx o t o' :
  ctx \|-o tyall o t \: o' = (Some o :: ctx \|-o t \: data) && (o' == data).
Proof.
by rewrite /ordering /= !(eq_sym _ (Some data));
  case: (Some _ =P ordering_rec _ _).
Qed.

Lemma ordering_allE' ctx o t :
  ctx \|-o tyall o t \: data = Some o :: ctx \|-o t \: data.
Proof. by rewrite ordering_allE eqxx andbT. Qed.

Lemma ordering_appP ctx tyl tyr o :
  reflect (exists2 ol, ctx \|-o tyl \: ol ->o o & ctx \|-o tyr \: ol)
          (ctx \|-o tyl @' tyr \: o).
Proof.
apply: (iffP idP); rewrite /ordering /=.
- by move: (ordering_rec ctx tyl) => [] // [] // ol or;
    case: ifP => // /eqP -> /eqP [] ->; exists ol.
- by case => ol /eqP <- /eqP <-; rewrite eqxx.
Qed.

Lemma ordering_absP ctx ol ty o :
  reflect (exists2 or, o = ol ->o or & Some ol :: ctx \|-o ty \: or)
          (ctx \|-o tyabs ol ty \: o).
Proof.
apply: (iffP idP); rewrite /ordering /=.
- by case: ordering_rec => //= or /eqP [] ->; exists or.
- by case => or ->; case: ordering_rec => // or' /eqP [] <-.
Qed.

Lemma ordering_absE ctx ol or ty :
  ctx \|-o tyabs ol ty \: ol ->o or = Some ol :: ctx \|-o ty \: or.
Proof.
by rewrite /ordering /=;
  case: (ordering_rec _ _) => //= o; apply/eqP/eqP; do!case => ->.
Qed.

Notation SN_ty := (Acc (fun x y => reduction1_ty y x)).

Definition neutral (ty : typ) : bool :=
  match ty with tyabs _ _ => false | _ => true end.

(*
Lemma inj_shift_ty d c ty ty' :
  (shift_ty d c ty == shift_ty d c ty') = (ty == ty').
Proof.
elim: ty ty' d c =>
  [n | tyl IHl tyr IHr | o ty IH | tyl IHl tyr IHr | o ty IH]
  [m | tyl' tyr' | o' ty' | tyl' tyr' | o' ty'] d c //=;
  try by rewrite !eqE /= -!eqE ?IH ?IHl ?IHr.
by apply/eqP; elimif; case: ifP => H0; apply/eqP; move: H0;
   rewrite!eqE /= ?(eqn_add2l, eqn_add2r) //;
   (move => -> // || move/eqP => H; apply/eqP; ssromega).
Qed.
*)

Lemma shift_zero_ty n ty : shift_ty 0 n ty = ty.
Proof. by elim: ty n; congruence' => n c; rewrite addn0 if_same. Qed.

Lemma shift_add_ty d d' c c' ty :
  c <= c' <= c + d -> shift_ty d' c' (shift_ty d c ty) = shift_ty (d' + d) c ty.
Proof. case/andP; do 2 elimleq; elim: ty c; congruence' => *; elimif_omega. Qed.

Lemma shift_shift_distr_ty d c d' c' ty :
  c' <= c ->
  shift_ty d' c' (shift_ty d c ty) = shift_ty d (d' + c) (shift_ty d' c' ty).
Proof. elimleq; elim: ty c'; congruence' => *; elimif_omega. Qed.

Lemma shift_subst_distr_ty n d c tys ty :
  c <= n ->
  shift_ty d c (subst_ty n tys ty) = subst_ty (d + n) tys (shift_ty d c ty).
Proof.
by elimleq; elim: ty c => /=; congruence' => v c;
  elimif_omega; rewrite shift_add_ty //; elimif_omega.
Qed.

Lemma subst_shift_distr_ty n d c tys ty :
  n <= c ->
  shift_ty d c (subst_ty n tys ty) =
  subst_ty n (map (shift_ty d (c - n)) tys) (shift_ty d (size tys + c) ty).
Proof.
elimleq; elim: ty n; congruence' => v n; elimif_omega.
- rewrite !nth_default ?size_map /=; elimif_omega.
- rewrite -shift_shift_distr_ty // nth_map' /=;
    congr shift_ty; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_shift_cancel_ty n d c tys ty :
  c <= n -> size tys + n <= d + c ->
  subst_ty n tys (shift_ty d c ty) = shift_ty (d - size tys) c ty.
Proof.
by do 2 elimleq; elim: ty c; congruence' => v c;
  elimif_omega; rewrite nth_default /=; elimif_omega.
Qed.

Lemma subst_subst_distr_ty n m xs ys ty :
  m <= n ->
  subst_ty n xs (subst_ty m ys ty) =
  subst_ty m (map (subst_ty (n - m) xs) ys) (subst_ty (size ys + n) xs ty).
Proof.
elimleq; elim: ty m; congruence' => v m /=; elimif_omega.
- rewrite (@subst_shift_cancel_ty m) // size_map 1?nth_default /=; elimif_omega.
- rewrite size_map -shift_subst_distr_ty // nth_map' /=;
    congr shift_ty; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_app_ty n xs ys ty :
  subst_ty n xs (subst_ty (size xs + n) ys ty) = subst_ty n (xs ++ ys) ty.
Proof.
elim: ty n; congruence' => v n; rewrite nth_cat size_cat;
  elimif_omega; rewrite subst_shift_cancel_ty; elimif_omega.
Qed.

Lemma subst_nil_ty n ty : subst_ty n [::] ty = ty.
Proof. elim: ty n; congruence' => v n; rewrite nth_nil /=; elimif_omega. Qed.

Lemma subst_reduction1_ty n tys ty ty' :
  ty ~>ty1 ty' -> subst_ty n tys ty ~>ty1 subst_ty n tys ty'.
Proof.
move => H; move: ty ty' H n.
refine (reduction1_ty_ind _ _ _ _ _ _ _) => /=; auto => t t' ty n.
by rewrite subst_subst_distr_ty //= add1n subn0.
Qed.

(*******************************************************************************
Strong normalization proof for types with the order-free version of reducibility
*******************************************************************************)
Module typelevel_strong_normalization_proof_orderfree.

Fixpoint reducible (o : ord) (ty : typ) : Prop :=
  match o with
    | data => SN_ty ty
    | ol ->o or => forall ty', reducible ol ty' -> reducible or (ty @' ty')
  end.

Lemma CR2 o ty ty' : ty ~>ty1 ty' -> reducible o ty -> reducible o ty'.
Proof.
elim: o ty ty' => /= [| ol IHl or IHr] ty ty' H.
- by case; apply.
- by move => H0 ty'' H1; apply IHr with (ty @' ty''); auto.
Qed.

Hint Resolve CR2.

Lemma CR1_and_CR3 o :
  (forall ty, reducible o ty -> SN_ty ty) /\
  (forall ty, neutral ty ->
             (forall ty', ty ~>ty1 ty' -> reducible o ty') -> reducible o ty).
Proof.
elim: o; first by [].
move => /= ol [IHl1 IHl2] or [IHr1 IHr2]; split => [ty H | tyl H H0 tyr H1].
- suff: SN_ty ([fun ty => ty @' 0] ty) by apply acc_preservation; constructor.
  apply IHr1, IHr2 => // t' H0.
  apply (CR2 H0), H, IHl2 => // t'' H1; inversion H1.
- move: (IHl1 tyr H1) => H2.
  move: tyr H2 H1; refine (Acc_ind' _) => tyr IH H1.
  apply IHr2 => // ty' H2.
  move: H; inversion H2; subst => // _; eauto.
Qed.

Definition CR1 o ty := proj1 (CR1_and_CR3 ty) o.
Definition CR3 o ty := proj2 (CR1_and_CR3 ty) o.

Lemma abs_reducibility ty ol or :
  (forall ty', reducible ol ty' -> reducible or (subst_ty 0 [:: ty'] ty)) ->
  reducible (ol ->o or) (tyabs ol ty).
Proof.
move => /= H ty' H0.
have H1: SN_ty ty by
  move: (CR1 (H ty' H0));
  apply acc_preservation => x y; apply subst_reduction1_ty.
move: ty ty' H1 {H0} (CR1 H0) H (H0);
  refine (Acc_ind2 _) => ty ty' IHty IHty' H H0.
apply CR3 => // ty'' H1; inversion H1; subst; eauto; inversion H5.
by apply IHty; auto => t'' H7;
  apply (CR2 (subst_reduction1_ty 0 [:: t''] H6)), H.
Qed.

Lemma reduce_lemma ctx (ctx' : seq (typ * ord)) ty o :
  [seq Some p.2 | p <- ctx'] ++ ctx \|-o ty \: o ->
  Forall (fun p => reducible p.2 p.1) ctx' ->
  reducible o (subst_ty 0 (unzip1 ctx') ty).
Proof.
elim: ty o ctx ctx'.
- move => /= n o ctx ctx'.
  rewrite subn0 size_map shift_zero_ty.
  elim: ctx' n => [| c' ctx' IH []] /=.
  + move => n _ _; rewrite nth_nil subn0.
    apply CR3 => //; auto => t' H0; inversion H0.
  + case/eqP => ->; tauto.
  + by move => n H [_ H0]; apply IH.
- move => tyl IHl tyr IHr o ctx ctx' /=.
  rewrite ordering_funE => /and3P [H H0] /eqP -> {o} H1.
  move: {tyl tyr} (subst_ty _ _ tyl) (subst_ty _ _ tyr)
        {IHl IHr H H0 H1} (IHl _ _ _ H H1) (IHr _ _ _ H0 H1) => /=.
  by refine (Acc_ind2 _) => tyl tyr IHl IHr; constructor => ty H;
    inversion H; subst; auto.
- move => o ty IH o' ctx ctx'.
  rewrite ordering_allE => /andP [] H /eqP -> {o'} H0 /=.
  have/(IH data ctx ((tyvar 0, o) :: ctx') H) /=:
    Forall (fun p => reducible p.2 p.1) ((tyvar 0, o) :: ctx')
    by split => //=; apply CR3 => // ty' H1; inversion H1.
  rewrite -/([:: _] ++ _) -subst_app_ty /= addn0.
  move: (subst_ty 1 _ _) {IH H H0} => ty'.
  move: {1 3}(subst_ty _ _ _) (erefl (subst_ty 0 [:: tyvar 0] ty')) => ty'' H H0.
  move: ty'' H0 ty' H.
  refine (Acc_ind' _) => ty' H ty'' H0; subst ty'.
  constructor => ty''' H0; inversion H0; subst.
  by apply (H (subst_ty 0 [:: tyvar 0] t')) => //; apply subst_reduction1_ty.
- move => tyl IHl tyr IHr or ctx ctx' /ordering_appP [ol H H0] H1.
  by move: (IHl (ol ->o or) ctx ctx') => /=; apply => //; apply IHr with ctx.
- move => ol ty IH o ctx ctx' /ordering_absP [or -> H] H0.
  simpl subst_ty; apply abs_reducibility => ty' H1.
  by rewrite subst_app_ty /=; apply (IH or ctx ((ty', ol) :: ctx')).
Qed.

Theorem typed_term_is_sn ctx ty o : ctx \|-o ty \: o -> SN_ty ty.
Proof.
by move/(@reduce_lemma ctx [::]) => /= /(_ I); rewrite subst_nil_ty; apply CR1.
Qed.

End typelevel_strong_normalization_proof_orderfree.
