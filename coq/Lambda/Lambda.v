
Require Import Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Omega.

Inductive term : Type :=
  | var : nat -> term
  | app : term -> term -> term
  | abs : term -> term.

Inductive shifted1 : nat -> nat -> term -> Type :=
  | svar1 : forall d c n, n < c -> shifted1 d c (var n)
  | svar2 : forall d c n, c + d <= n -> d <= n -> shifted1 d c (var n)
  | sapp : forall d c t1 t2, shifted1 d c t1 -> shifted1 d c t2 -> shifted1 d c (app t1 t2)
  | sabs : forall d c t, shifted1 d (S c) t -> shifted1 d c (abs t).

Fixpoint shift (d c : nat) (t : term) : term :=
  match t with
    | var n =>
      match le_dec c n with
        | left p => var (d + n)
        | right p => var n
      end
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (S c) t1)
  end.

Functional Scheme shift_ind := Induction for shift Sort Prop.

Definition shifted2 (d c : nat) (t : term) : Type :=
  { t' : term | shift d c t' = t }.

Lemma shifted1_shift : forall d c t, shifted1 d c (shift d c t).
  intros.
  revert d c.
  induction t ; intros ; simpl.
  case (le_dec c n) ; intros.
  apply svar2 ; omega.
  apply svar1 ; omega.
  apply sapp ; auto.
  apply sabs ; auto.
Qed.

Theorem shifted1_is_shifted2 : forall d c t, shifted1 d c t -> shifted2 d c t.
  intros.
  induction H.
  exists (var n) ; simpl.
  case (le_dec c n) ; intros.
  apply False_ind ; omega.
  auto.
  exists (var (n - d)) ; simpl.
  case (le_dec c (n - d)) ; intros.
  f_equal ; omega.
  apply False_ind ; omega.
  elim IHshifted1_1 ; elim IHshifted1_2 ; intros.
  exists (app x0 x) ; simpl.
  f_equal ; auto.
  elim IHshifted1 ; intros.
  exists (abs x) ; simpl.
  f_equal ; auto.
Qed.

Theorem shifted2_is_shifted1 : forall d c t, shifted2 d c t -> shifted1 d c t.
  intros.
  destruct X.
  rewrite <- e.
  exact (shifted1_shift d c x).
Qed.

Definition unshift (d c : nat) (t : term) (p : shifted2 d c t) : term := proj1_sig p.



