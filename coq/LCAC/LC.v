Require Import
  Arith.Arith Relations.Relations
  ssreflect Relations_ext.

(* Definition 1.1: Lambda-terms *)

Inductive lcterm : Set :=
  | lcbvar of nat
  | lcubvar of nat
  | lclam of lcterm
  | lcapp of lcterm & lcterm.

Lemma eq_lcterm_dec : forall (t1 t2 : lcterm), {t1 = t2}+{t1 <> t2}.
Proof.
  do !decide equality.
Qed.

Infix "@" := lcapp (at level 20, left associativity).

(* Example 1.2 *)

Check (lclam (lcapp (lcbvar 0) (lcubvar 0))).
Check (lclam (lcapp (lcbvar 0) (lcubvar 0))).
Check (lcapp (lcubvar 0) (lclam (lclam (lcbvar 0)))).
Check (lcapp (lclam (lcbvar 0)) (lclam (lcapp (lcbvar 0) (lcubvar 0)))).
Check (lclam (lcapp (lcubvar 0) (lcbvar 0))).

(* Notation 1.3 *)

Fixpoint lclams (n : nat) (t : lcterm) :=
  match n with
    | 0 => t
    | S n => lclams n (lclam t)
  end.

(* Definition 1.6: Length of lambda-term *)

Fixpoint lc_length (t : lcterm) : nat :=
  match t with
    | lclam t' => S (lc_length t')
    | lcapp t1 t2 => lc_length t1 + lc_length t2
    | _ => 1
  end.

(* Definition 1.7: Binary relation "occurs in" on lambda-terms *)

Inductive lc_occurs : relation lcterm :=
  | lc_occurs_refl  : forall (t : lcterm), lc_occurs t t
  | lc_occurs_left  : forall (t1 t2 t3 : lcterm),
    lc_occurs t1 t2 -> lc_occurs t1 (t2 @ t3)
  | lc_occurs_right : forall (t1 t2 t3 : lcterm),
    lc_occurs t1 t3 -> lc_occurs t1 (t2 @ t3)
  | lc_occurs_lam   : forall (t1 t2 : lcterm),
    lc_occurs t1 t2 -> lc_occurs t1 (lclam t2).

(* Definition 1.12: Substitution *)
