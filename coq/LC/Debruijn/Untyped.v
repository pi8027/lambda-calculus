From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LCAC Require Import Relations_ext seq_ext_base ssrnat_ext seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Set := var of nat | app of term & term | abs of term.

Coercion var : nat >-> term.

Fixpoint eqterm t1 t2 :=
  match t1, t2 with
    | var n, var m => n == m
    | app t1l t1r, app t2l t2r => eqterm t1l t2l && eqterm t1r t2r
    | abs t1, abs t2 => eqterm t1 t2
    | _, _ => false
  end.

Lemma eqtermP : Equality.axiom eqterm.
Proof.
move => t1 t2; apply: (iffP idP) => [| <-]; last by elim: t1 => //= t1l ->.
by elim: t1 t2 => [n | t1l IH t1r IH' | t1 IH]
  [// m /eqP -> | //= t2l t2r /andP [] /IH -> /IH' -> | // t2 /IH ->].
Defined.

Canonical term_eqMixin := EqMixin eqtermP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Fixpoint shift d c t : term :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d c.+1 t1)
  end.

Notation substitutev ts m n :=
  (shift n 0 (nth (var (m - n - size ts)) ts (m - n))) (only parsing).

Fixpoint substitute n ts t : term :=
  match t with
    | var m => if n <= m then substitutev ts m n else m
    | app t1 t2 => app (substitute n ts t1) (substitute n ts t2)
    | abs t' => abs (substitute n.+1 ts t')
  end.

Reserved Notation "t ->b1 t'" (at level 70, no associativity).

Inductive betared1 : relation term :=
  | betared1beta t1 t2     : app (abs t1) t2 ->b1 substitute 0 [:: t2] t1
  | betared1appl t1 t1' t2 : t1 ->b1 t1' -> app t1 t2 ->b1 app t1' t2
  | betared1appr t1 t2 t2' : t2 ->b1 t2' -> app t1 t2 ->b1 app t1 t2'
  | betared1abs t t'       : t ->b1 t' -> abs t ->b1 abs t'
  where "t ->b1 t'" := (betared1 t t').

Notation betared := [* betared1].
Infix "->b" := betared (at level 70, no associativity).

Hint Constructors betared1.

Lemma shiftzero n t : shift 0 n t = t.
Proof. by elim: t n; congruence' => v n; rewrite addn0 if_same. Qed.

Lemma shift_add d d' c c' t :
  c <= c' <= c + d -> shift d' c' (shift d c t) = shift (d' + d) c t.
Proof. case/andP; do 2 elimleq; elim: t c; congruence' => *; elimif_omega. Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof. elimleq; elim: t c'; congruence' => *; elimif_omega. Qed.

Lemma shift_subst_distr n d c ts t :
  c <= n -> shift d c (substitute n ts t) = substitute (d + n) ts (shift d c t).
Proof.
by elimleq; elim: t c; congruence' => v c; elimif;
  rewrite shift_add //= add0n leq_addr.
Qed.

Lemma subst_shift_distr n d c ts t :
  n <= c ->
  shift d c (substitute n ts t) =
  substitute n (map (shift d (c - n)) ts) (shift d (size ts + c) t).
Proof.
elimleq; elim: t n; congruence' => v n; elimif.
- rewrite !nth_default ?size_map /=; elimif_omega.
- rewrite -shift_shift_distr // nth_map' /=;
    congr shift; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

(*
Lemma subst_shift_distr' n d c ts t :
  shift d (n + c) (substitute n ts t) =
  substitute n [seq shift d c i | i <- ts] (shift d (size ts + (n + c)) t).
Proof. by rewrite subst_shift_distr ?addKn // leq_addr. Qed.
*)

Lemma subst_shift_cancel n d c ts t :
  c <= n -> size ts + n <= d + c ->
  substitute n ts (shift d c t) = shift (d - size ts) c t.
Proof.
do 2 elimleq; elim: t c; congruence' => v c;
  elimif; rewrite nth_default /=; elimif_omega.
Qed.

Lemma subst_subst_distr n m xs ys t :
  m <= n ->
  substitute n xs (substitute m ys t) =
  substitute m (map (substitute (n - m) xs) ys) (substitute (size ys + n) xs t).
Proof.
elimleq; elim: t m; congruence' => v m; elimif.
- rewrite nth_default ?(@subst_shift_cancel m) // ?size_map /=; elimif_omega.
- rewrite -shift_subst_distr // nth_map' /=;
    congr shift; apply nth_equal; rewrite size_map; elimif_omega.
Qed.

Lemma subst_app n xs ys t :
  substitute n xs (substitute (size xs + n) ys t) = substitute n (xs ++ ys) t.
Proof.
elim: t n; congruence' => v n; rewrite nth_cat size_cat;
  elimif_omega; rewrite subst_shift_cancel; elimif_omega.
Qed.

Lemma subst_nil n t : substitute n [::] t = t.
Proof. elim: t n; congruence' => m n; rewrite nth_nil /=; elimif_omega. Qed.

Lemma subst_betared1 n ts t t' :
  t ->b1 t' -> substitute n ts t ->b1 substitute n ts t'.
Proof.
move => H; elim/betared1_ind: t t' / H n => /=; auto => t t' n.
by rewrite subst_subst_distr //= add1n subn0.
Qed.

(* small example for PPL2015 paper *)
Lemma shift_betared t t' d c : t ->b1 t' -> shift d c t ->b1 shift d c t'.
Proof.
move => H; elim/betared1_ind: t t' / H d c => /=; auto => t1 t2 d c.
rewrite subst_shift_distr //= add1n subn0; auto.
Qed.

Module confluence_proof.

Reserved Notation "t ->bp t'" (at level 70, no associativity).

Inductive parred : relation term :=
  | parredvar n : var n ->bp var n
  | parredapp t1 t1' t2 t2' :
    t1 ->bp t1' -> t2 ->bp t2' -> app t1 t2 ->bp app t1' t2'
  | parredabs t t' : t ->bp t' -> abs t ->bp abs t'
  | parredbeta t1 t1' t2 t2' :
    t1 ->bp t1' -> t2 ->bp t2' -> app (abs t1) t2 ->bp substitute 0 [:: t2'] t1'
  where "t ->bp t'" := (parred t t').

Hint Constructors parred.

Function reduce_all_redex t : term :=
  match t with
    | var _ => t
    | app (abs t1) t2 =>
      substitute 0 [:: reduce_all_redex t2] (reduce_all_redex t1)
    | app t1 t2 => app (reduce_all_redex t1) (reduce_all_redex t2)
    | abs t' => abs (reduce_all_redex t')
  end.

Lemma parred_refl t : parred t t.
Proof. elim: t; auto. Qed.

Lemma betaredappl t1 t1' t2 : t1 ->b t1' -> app t1 t2 ->b app t1' t2.
Proof. apply (rtc_map' (fun x y => @betared1appl x y t2)). Qed.

Lemma betaredappr t1 t2 t2' : t2 ->b t2' -> app t1 t2 ->b app t1 t2'.
Proof. apply (rtc_map' (@betared1appr t1)). Qed.

Lemma betaredabs t t' : t ->b t' -> abs t ->b abs t'.
Proof. apply (rtc_map' betared1abs). Qed.

Hint Resolve parred_refl betaredappl betaredappr betaredabs.

Lemma betared1_in_parred : inclusion betared1 parred.
Proof. apply betared1_ind; auto. Qed.

Lemma parred_in_betared : inclusion parred betared.
Proof.
apply parred_ind; auto => t1 t1' t2 t2' H H0 H1 H2.
- apply rtc_trans with (app t1' t2); auto.
- apply rtc_trans with (app (abs t1') t2); auto.
  apply rtc_trans with (app (abs t1') t2'); auto.
  by apply rtc_step.
Qed.

Lemma shift_parred t t' d c : t ->bp t' -> shift d c t ->bp shift d c t'.
Proof.
move => H; elim/parred_ind: t t' / H d c => //=;
  auto => t1 t1' t2 t2' H H0 H1 H2 d c.
rewrite subst_shift_distr //= add1n subn0; auto.
Qed.

Lemma subst_parred n ps t t' :
  Forall (prod_curry parred) ps -> t ->bp t' ->
  substitute n [seq fst p | p <- ps] t ->bp
  substitute n [seq snd p | p <- ps] t'.
Proof.
move => H H0; elim/parred_ind: t t' / H0 n => /=; auto.
- move => v n; elimif; rewrite !size_map; apply shift_parred.
  elim: ps v H => //= [[t t']] ps IH [| v] [] //= H H0.
  by rewrite subSS; apply IH.
- move => t1 t1' t2 t2' H0 H1 H2 H3 n.
  by rewrite subst_subst_distr //= add1n subn0; auto.
Qed.

Lemma parred_all_lemma t t' : t ->bp t' -> t' ->bp reduce_all_redex t.
Proof with auto.
elim/reduce_all_redex_ind: {t}_ t'.
- by move => t n H t' H0; inversion H0; subst.
- move => _ t1 t2 _ H H0 t' H1; inversion H1; subst.
  + inversion H4; subst...
  + apply (@subst_parred 0 [:: (t2', reduce_all_redex t2)]) => /=...
- move => _ t1 t2 _ H H0 H1 t' H2; inversion H2; subst => //...
- move => _ t1 _ H t2 H0; inversion H0; subst...
Qed.

Lemma parred_confluent : confluent parred.
Proof.
by move => t1 t2 t3 H H0; exists (reduce_all_redex t1); apply parred_all_lemma.
Qed.

Theorem betared_confluent : confluent betared.
Proof.
apply (rtc_confluent' betared1_in_parred parred_in_betared parred_confluent).
Qed.

End confluence_proof.
