Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat
  Ssreflect.seq
  LCAC.ssrnat_ext LCAC.seq_ext LCAC.Relations_ext.

Set Implicit Arguments.

Section context.

Variable (A : Type).

Definition context := (seq (option A)).

(* ctxleq *)

Fixpoint ctxleq (xs ys : context) : Prop :=
  match xs, ys with
    | [::], _ => True
    | x :: xs, [::] => x = None /\ ctxleq xs [::]
    | x :: xs, y :: ys => (x = y \/ x = None) /\ ctxleq xs ys
  end.

Theorem ctxleq_refl : forall xs, ctxleq xs xs.
Proof.
  elim => //=; tauto.
Qed.

Theorem ctxleq_trans :
  forall xs ys zs, ctxleq xs ys -> ctxleq ys zs -> ctxleq xs zs.
Proof.
  elim => // x xs IH; case => /= [| y ys].
  - case => // z zs; case => H H0 _; subst; split; auto.
    apply IH with [::] => //.
  - case => //.
    - case; case => H H0; case => H1 H2; subst; split; auto;
        apply IH with ys => //.
    - move => z zs.
      case; case => H H0; case; case => H1 H2; subst; split; auto;
        apply IH with ys => //.
Qed.

Theorem ctxleq_nil : forall xs, ctxleq [::] xs.
Proof.
  by case.
Qed.

Theorem ctxleq_appl :
  forall xs ys zs, ctxleq ys zs -> ctxleq (xs ++ ys) (xs ++ zs).
Proof.
  elim => //=; auto.
Qed.

Theorem ctxleq_appr : forall xs ys, ctxleq xs (xs ++ ys).
Proof.
  move => xs ys; elim: xs.
  - apply ctxleq_nil.
  - rewrite /=; tauto.
Qed.

(* ctxnth *)

Fixpoint ctxnth (xs : context) n :=
  if xs is x :: xs
    then (if n is n.+1 then ctxnth xs n else x)
    else None.

Theorem ctxnth_oversize : forall xs n, size xs <= n -> ctxnth xs n = None.
Proof.
  elim => // x xs IH; case => //.
Qed.

Theorem ctxnth_drop : forall xs n m, ctxnth xs (n + m) = ctxnth (drop n xs) m.
Proof.
  by elim => // x xs Ih; case.
Qed.

Theorem ctxnth_drop' : forall xs n, ctxnth xs n = ctxnth (drop n xs) 0.
Proof.
  by move => xs n; rewrite -{1}(addn0 n) ctxnth_drop.
Qed.

Theorem ctxnth_take0 : forall xs n m, m <= n -> ctxnth (take m xs) n = None.
Proof.
  by elim => // x xs IH n; case => // m; case: n => //= n H; rewrite IH.
Qed.

Theorem ctxnth_take1 :
  forall xs n m, n < m -> ctxnth (take m xs) n = ctxnth xs n.
Proof.
  by elim => // x xs IH n; case => // m; case: n => //= n H; rewrite IH.
Qed.

Theorem ctxnth_appl :
  forall xs ys n, n < size xs -> ctxnth (xs ++ ys) n = ctxnth xs n.
Proof.
  by move => xs ys; elim: xs => // x xs IH; case.
Qed.

Theorem ctxnth_appr :
  forall xs ys n, ctxnth (xs ++ ys) (size xs + n) = ctxnth ys n.
Proof.
  by elim.
Qed.

(* ctxinsert *)

Fixpoint ctxinsert (xs ys : context) n : context :=
  if n is n.+1
    then
      (if ys is y :: ys then y else None) ::
      ctxinsert xs (List.tl ys) n
    else xs ++ ys.

Theorem size_ctxinsert :
  forall xs ys n, size (ctxinsert xs ys n) = size xs + maxn n (size ys).
Proof.
  move => xs; elim => [| y ys IH].
  - move => n.
    rewrite /= maxn0.
    elim: n xs => /=.
    - by move => xs; rewrite cats0 addn0.
    - by move => n IH xs; rewrite IH addnS.
  - case.
    - by rewrite /= size_cat max0n.
    - by move => n; rewrite /= maxnSS addnS IH.
Qed.

Theorem ctxnth_ctxinsert :
  forall xs ys n m,
  ctxnth (ctxinsert xs ys n) m =
  if m < n then ctxnth ys m else
  if m < n + size xs then ctxnth xs (m - n) else ctxnth ys (m - size xs).
Proof.
  move => xs ys n; elim: n ys.
  - move => /= ys m.
    rewrite add0n subn0.
    elim: xs m.
    - case => //=.
    - move => x xs IH; case => //.
  - move => n IH; case => //.
    - case => //= m.
      rewrite subSS addSn !ltnS (IH [::] m) //.
    - move => y ys; case => //= m.
      rewrite subSS addSn !ltnS (IH ys m).
      do 2 case: ifP => //; move => H _.
      by replace (m.+1 - size xs) with (m - size xs).+1 by ssromega.
Qed.

(* ctxindex *)

Notation ctxindex xs n x := (Some x = ctxnth xs n).

Theorem ctxleq_preserves_ctxindex :
  forall xs ys n a,
  ctxleq xs ys -> ctxindex xs n a -> ctxindex ys n a.
Proof.
  elim => // x xs IH; case => [| y ys]; case => /= [| n] a.
  - by case => H; subst.
  - case => H; subst => H H0; apply False_ind.
    elim: xs n H H0 {IH} => // x xs IH; case => /= [| n].
    - by case => H; subst.
    - case => H; subst; apply IH.
  - by case; case => H H0; subst.
  - case => _; apply IH.
Qed.

End context.

Notation ctxindex xs n x := (Some x = ctxnth xs n).
