Require Import
  Coq.Arith.Arith Coq.Relations.Relations Coq.Relations.Relation_Operators
  Ssreflect.ssreflect Ssreflect.seq LCAC.Relations_ext.

(* Definition 2.1: Combinatory logic terms, or CL-terms *)

Inductive clterm : Set :=
  | clvar of nat
  | clapp of clterm & clterm
  | clatoms | clatomk | clatomi.

Lemma eq_clterm_dec : forall (t1 t2 : clterm), {t1 = t2}+{t1 <> t2}.
Proof.
  do ?decide equality.
Qed.

Local Infix "@" := clapp (at level 20, left associativity).

Check ((clatoms @ (clatomk @ clatoms)) @ clatomk).
Check ((clatoms @ (clatomk @ clvar 0)) @ ((clatoms @ clatomk) @ clatomk)).

(* Definition 2.3: Length of CL-term *)

Fixpoint cl_length (t : clterm) : nat :=
  match t with
    | clapp t1 t2 => cl_length t1 + cl_length t2
    | _ => 1
  end.

(* Definition 2.4: Binary relation "occurs in" on CL-terms *)

Inductive cl_occurs : relation clterm :=
  | cl_occurs_refl  : forall (t : clterm), cl_occurs t t
  | cl_occurs_left  : forall (t1 t2 t3 : clterm),
    cl_occurs t1 t2 -> cl_occurs t1 (t2 @ t3)
  | cl_occurs_right : forall (t1 t2 t3 : clterm),
    cl_occurs t1 t3 -> cl_occurs t1 (t2 @ t3).

(* Definition 2.6, Exercise 2.8: Substitution *)

Fixpoint subst_lookup (l : seq (nat * clterm)) (v : nat) : option clterm :=
  match l with
    | nil => None
    | (v', t) :: l' => if eq_nat_dec v v' then Some t else subst_lookup l' v
  end%GEN_IF.

Fixpoint substitute (l : list (nat * clterm)) (t : clterm) : clterm :=
  match t with
    | clvar v =>
      match subst_lookup l v with
        | None => clvar v
        | Some t' => t'
      end
    | clapp tl tr => clapp (substitute l tl) (substitute l tr)
    | bc => bc
  end.

(* Example 2.7 *)

Eval compute in substitute
  [:: (1, clatoms @ clatomk) ] (clvar 0 @ clvar 1 @ clvar 1).
Eval compute in substitute [:: (1, clatoms @ clatomk) ; (0, clatomk @ clatomi) ]
  (clvar 0 @ clvar 1 @ clvar 1).

(* Definition 2.9: Weak reduction *)

Inductive cl_weakred : relation clterm :=
  | weakred_left  : forall (t1 t2 t3 : clterm),
    cl_weakred t1 t2 -> cl_weakred (t1 @ t3) (t2 @ t3)
  | weakred_right : forall (t1 t2 t3 : clterm),
    cl_weakred t1 t2 -> cl_weakred (t3 @ t1) (t3 @ t2)
  | weakred_s     : forall (t1 t2 t3 : clterm),
    cl_weakred (clatoms @ t1 @ t2 @ t3) (t1 @ t3 @ (t2 @ t3))
  | weakred_k     : forall (t1 t2 : clterm), cl_weakred (clatomk @ t1 @ t2) t1
  | weakred_i     : forall (t : clterm), cl_weakred (clatomi @ t) t.

Notation cl_weakred_rtc := (clos_refl_trans_1n clterm cl_weakred).

Infix "->1w" := cl_weakred (at level 50, no associativity).
Infix "->w" := cl_weakred_rtc (at level 50, no associativity).

Lemma weakred_rtc_left :
  forall t1 t2 t3, t1 ->w t2 -> t1 @ t3 ->w t2 @ t3.
Proof.
  move=> t1 t2 t3 ; elim ; econstructor.
  apply weakred_left, H.
  auto.
Qed.

Lemma weakred_rtc_right :
  forall t1 t2 t3, t1 ->w t2 -> t3 @ t1 ->w t3 @ t2.
Proof.
  move=> t1 t2 t3 ; elim ; econstructor.
  apply weakred_right, H.
  auto.
Qed.

Lemma weakred_rtc_app : forall t1 t1' t2 t2',
  t1 ->w t1' -> t2 ->w t2' -> (t1 @ t2) ->w (t1' @ t2').
Proof.
  move=> t1 t1' t2 t2' H H0 ; apply rt1n_trans' with (t1 @ t2').
  by apply weakred_rtc_right.
  by apply weakred_rtc_left.
Qed.

(* Definition 2.10: Weak normal form *)

Definition cl_weaknf (t : clterm) : Prop := ~(exists t' : clterm, t ->1w t').
Definition cl_weaknf_of (t1 t2 : clterm) : Prop := t2 ->w t1 /\ cl_weaknf t1.

(* Example 2.11 *)

Definition cl_comb_b : clterm := clatoms @ (clatomk @ clatoms) @ clatomk.

Example example_2_11 : forall t1 t2 t3,
  cl_comb_b @ t1 @ t2 @ t3 ->w t1 @ (t2 @ t3).
Proof.
  move=> t1 t2 t3.
  rewrite /cl_comb_b.
  eapply rt1n_trans ; first apply weakred_left, weakred_left, weakred_s.
  eapply rt1n_trans ;
    first apply weakred_left, weakred_left, weakred_left, weakred_k.
  eapply rt1n_trans ; first apply weakred_s.
  apply rt1n_step ; apply weakred_left, weakred_k.
Qed.

(* Example 2.12 *)

Definition cl_comb_c : clterm :=
  clatoms @ (cl_comb_b @ cl_comb_b @ clatoms) @ (clatomk @ clatomk).

Example example_2_12 :
  forall t1 t2 t3, cl_comb_c @ t1 @ t2 @ t3 ->w t1 @ t3 @ t2.
Proof.
  move=> t1 t2 t3.
  rewrite /cl_comb_c.
  eapply rt1n_trans ; first apply weakred_left, weakred_left, weakred_s.
  eapply rt1n_trans' ; first (do 3 apply weakred_rtc_left ; apply example_2_11).
  eapply rt1n_trans' ; first apply weakred_rtc_left, example_2_11.
  eapply rt1n_trans ; first apply weakred_s.
  apply weakred_rtc_right.
  eapply rt1n_trans ; first apply weakred_left, weakred_left, weakred_k.
  apply rt1n_step ; apply weakred_k.
Qed.

(* Exercise 2.13 *)



(* Lemma 2.14: Substitution lemma for ->w *)

Lemma substlemma_a' : forall t1 t2 v,
  t1 ->1w t2 -> cl_occurs (clvar v) t2 -> cl_occurs (clvar v) t1.
Proof.
  move=> t1 t2 v H H0.
  induction H.
  inversion H0.
  apply cl_occurs_left, IHcl_weakred, H3.
  apply cl_occurs_right, H3.
  inversion H0.
  apply cl_occurs_left, H3.
  apply cl_occurs_right, IHcl_weakred, H3.
  inversion H0 ; inversion H2.
  apply cl_occurs_left, cl_occurs_left, cl_occurs_right, H6.
  apply cl_occurs_right, H6.
  apply cl_occurs_left, cl_occurs_right, H6.
  apply cl_occurs_right, H6.
  apply cl_occurs_left, cl_occurs_right, H0.
  apply cl_occurs_right, H0.
Qed.

Lemma substlemma_a : forall t1 t2 v,
  t1 ->w t2 -> cl_occurs (clvar v) t2 -> cl_occurs (clvar v) t1.
Proof.
  move=> t1 t2 v ; elim.
  auto.
  intros ; eapply substlemma_a' ; eauto.
Qed.

Lemma substlemma_b : forall t1 t2 t3 v,
  t1 ->w t2 -> substitute [:: (v, t1)] t3 ->w substitute [:: (v, t2)] t3.
Proof.
  move=> t1 t2 t3 v H ; elim t3 ; simpl ; try constructor.
  by move=> n ; elim (eq_nat_dec n v) ; try constructor.
  by move=> t3l H0 t3r ; apply weakred_rtc_app.
Qed.

Lemma substlemma_c : forall t1 t2 l,
  t1 ->1w t2 -> substitute l t1 ->1w substitute l t2.
Proof.
  by move=> t1 t2 l ; elim ; simpl ; constructor.
Qed.

(* Theorem 2.15: Church-Rosser theorem for ->w *)

Inductive cl_parred : relation clterm :=
  | parred_app   : forall (t1 t1' t2 t2' : clterm),
    cl_parred t1 t1' -> cl_parred t2 t2' -> cl_parred (t1 @ t2) (t1' @ t2')
  | parred_s     : forall (t1 t1' t2 t2' t3 t3' t3'' : clterm),
    cl_parred t1 t1' -> cl_parred t2 t2' ->
    cl_parred t3 t3' -> cl_parred t3 t3'' ->
    cl_parred (clatoms @ t1 @ t2 @ t3) (t1' @ t3' @ (t2' @ t3''))
  | parred_k     : forall (t1 t1' t2 : clterm),
    cl_parred t1 t1' -> cl_parred (clatomk @ t1 @ t2) t1'
  | parred_i     : forall (t1 t1' : clterm),
    cl_parred t1 t1' -> cl_parred (clatomi @ t1) t1'
  | parred_var   : forall (n : nat), cl_parred (clvar n) (clvar n)
  | parred_atoms : cl_parred clatoms clatoms
  | parred_atomk : cl_parred clatomk clatomk
  | parred_atomi : cl_parred clatomi clatomi.

Infix "->p" := cl_parred (at level 50, no associativity).

Lemma cl_parred_refl : forall t, t ->p t.
Proof.
  by elim ; constructor.
Qed.

Lemma cl_weakred_in_parred : inclusion cl_weakred cl_parred.
Proof.
  move=> t1 t2 ; elim.
  constructor ; [ auto | apply cl_parred_refl ].
  constructor ; [ apply cl_parred_refl | auto ].
  move=> ? ? ? ; apply parred_s ; apply cl_parred_refl.
  constructor ; apply cl_parred_refl.
  constructor ; apply cl_parred_refl.
Qed.

Lemma cl_parred_in_weakred_rtc : inclusion cl_parred cl_weakred_rtc.
Proof.
  intros ; induction H ; try by constructor.
  apply weakred_rtc_app ; auto.
  eapply rt1n_trans ; [ apply weakred_s | do ?apply weakred_rtc_app ; auto ].
  eapply rt1n_trans ; [ apply weakred_k | do ?apply weakred_rtc_app ; auto ].
  eapply rt1n_trans ; [ apply weakred_i | do ?apply weakred_rtc_app ; auto ].
Qed.

Fixpoint cl_parred_all (t : clterm) : clterm :=
  match t with
    | clatoms @ t1 @ t2 @ t3 =>
      (cl_parred_all t1 @ cl_parred_all t3) @
      (cl_parred_all t2 @ cl_parred_all t3)
    | clatomk @ t1 @ t2 => cl_parred_all t1
    | clatomi @ t1 => cl_parred_all t1
    | t1 @ t2 => cl_parred_all t1 @ cl_parred_all t2
    | _ => t
  end.

Lemma cl_parred_all_lemma : forall t1 t2, t1 ->p t2 -> t2 ->p cl_parred_all t1.
Proof.
  intros ; induction H ; try by do ?constructor.
  destruct t1 ; try by constructor.
  - destruct t1_1 ; try by constructor.
    - destruct t1_1_1 ; try by constructor.
      inversion H ; inversion H3 ; inversion H8 ;
        rewrite -H4 -H9 -H12 in IHcl_parred1.
      by inversion IHcl_parred1 ; inversion H15 ; apply parred_s.
    - inversion H ; inversion H3 ; rewrite -H4 -H7 in IHcl_parred1.
      by inversion IHcl_parred1 ; apply parred_k.
  - inversion H ; rewrite -H2 in IHcl_parred1.
    by inversion IHcl_parred1 ; apply parred_i.
Qed.

Theorem cl_parred_confluent : confluent cl_parred.
Proof.
  by move=> t1 ; exists (cl_parred_all t1) ; split ; apply cl_parred_all_lemma.
Qed.

Theorem cl_weakred_confluent : confluent cl_weakred_rtc.
Proof.
  apply (rt1n_confluent' _ _ _
    cl_weakred_in_parred cl_parred_in_weakred_rtc cl_parred_confluent).
Qed.

(* Corollary 2.15.1: Uniqueness of nf *)

Corollary cl_weaknf_uniqueness : forall t1 t2 t3,
  cl_weaknf_of t2 t1 -> cl_weaknf_of t3 t1 -> t2 = t3.
Proof.
  move=> t1 t2 t3 ; elim => H H0 ; elim => H1 H2.
  elim (cl_weakred_confluent t1 t2 t3 H H1) => [t4 [H3 H4]].
  inversion H3.
  inversion H4.
  auto.
  apply False_ind, H2 ; eauto.
  apply False_ind, H0 ; eauto.
Qed.

(* Exercise 2.16 *)

Lemma exercise_2_16 : forall t, clatoms @ clatomk @ clatomk @ t ->w t.
Proof.
  move=> t.
  eapply rt1n_trans.
  apply weakred_s.
  apply rt1n_step, weakred_k.
Qed.

(* Exercise 2.17 *)
