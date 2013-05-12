Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq LCAC.ssrnat_ext.

Set Implicit Arguments.

Fixpoint Forall A (P : A -> Prop) xs :=
  if xs is x :: xs then P x /\ Forall P xs else True.

Section Seq.

Variable (A B : Type).

(* drop and take *)

Theorem drop_addn :
  forall n m (xs : seq A), drop n (drop m xs) = drop (n + m) xs.
Proof.
  move => n; elim => [| m IH] [] // x xs.
  - by rewrite addn0.
  - by rewrite addnS /= IH.
Qed.

Theorem take_minn :
  forall n m (xs : seq A), take n (take m xs) = take (minn n m) xs.
Proof.
  by elim => [| n IH] [| m] [] // x xs; rewrite minnSS /= IH.
Qed.

Theorem drop_take_distr :
  forall n m (xs : seq A), drop n (take m xs) = take (m - n) (drop n xs).
Proof.
  elim.
  - by move => m xs; rewrite !drop0 subn0.
  - move => n IH [].
    - by move => xs; rewrite sub0n !take0.
    - by move => m [] //= _ xs; rewrite subSS IH.
Qed.

Theorem take_drop_distr :
  forall n m (xs : seq A), take n (drop m xs) = drop m (take (n + m) xs).
Proof.
  by move => n m xs; rewrite drop_take_distr addnK.
Qed.

Theorem drop_take_nil : forall n (xs : seq A), drop n (take n xs) = [::].
Proof.
  by move => n xs; rewrite drop_take_distr subnn take0.
Qed.

Theorem size_take : forall n (xs : seq A), size (take n xs) = minn n (size xs).
Proof.
  elim.
  - by move => xs; rewrite take0 min0n.
  - by move => n IH [] //= _ xs; rewrite IH minnSS.
Qed.

(* nth *)

Theorem nth_map' :
  forall (f : A -> B) x xs n, f (nth x xs n) = nth (f x) (map f xs) n.
Proof.
  move => f x; elim => /=.
  - by move => n; rewrite !nth_nil.
  - by move => x' xs IH [].
Qed.

Theorem nth_equal :
  forall (a b : A) xs n, (size xs <= n -> a = b) -> nth a xs n = nth b xs n.
Proof.
  move => a b; elim.
  by move => n /= ->.
  by move => x xs IH [].
Qed.

(* context *)

Definition context := (seq (option A)).

Notation ctxindex xs n x := (Some x = nth None xs n).
Notation ctxleq xs ys := (forall n a, ctxindex xs n a -> ctxindex ys n a).

Fixpoint ctxinsert xs ys n : context :=
  if n is n.+1
    then head None ys :: ctxinsert xs (behead ys) n
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
  nth None (ctxinsert xs ys n) m =
  if m < n then nth None ys m else
  if m < n + size xs then nth None xs (m - n) else nth None ys (m - size xs).
Proof.
  move => xs ys n; elim: n ys.
  - move => /= ys m.
    rewrite add0n subn0.
    by elim: xs m => [| x xs IH] [].
  - move => n IH [| y ys] [] //= m.
    - by rewrite subSS addSn !ltnS IH !nth_nil.
    - rewrite subSS addSn !ltnS IH.
      (do 2 case: ifP => //) => H _.
      rewrite subSn //; ssromega.
Qed.

Theorem ctxleq_refl : forall (xs : context), ctxleq xs xs.
Proof.
  done.
Qed.

Theorem ctxleq_trans :
  forall (xs ys zs : context), ctxleq xs ys -> ctxleq ys zs -> ctxleq xs zs.
Proof.
  auto.
Qed.

Theorem ctxleq_nil : forall (xs : context), ctxleq [::] xs.
Proof.
  by move => xs n a; rewrite nth_nil.
Qed.

Theorem ctxleq_appl :
  forall (xs ys zs : context), ctxleq ys zs -> ctxleq (xs ++ ys) (xs ++ zs).
Proof.
  by elim => // x xs IH ys zs H [] //=; apply IH.
Qed.

Theorem ctxleq_appr : forall (xs ys : context), ctxleq xs (xs ++ ys).
Proof.
  move => xs ys; elim: xs => // x xs.
  - by rewrite nth_nil.
  - by move => H [].
Qed.

Theorem ctxleq_app :
  forall (xs xs' ys ys' : context), size xs = size xs' ->
  ctxleq xs xs' -> ctxleq ys ys' -> ctxleq (xs ++ ys) (xs' ++ ys').
Proof.
  elim => [| x xs IH]; case => //= x' xs' ys ys' [H] H0 H1; case.
  - move => /= a H2; apply (H0 0 a H2).
  - move => /= n a; apply IH => // m; apply (H0 m.+1).
Qed.

(* Forall *)

Theorem Forall_impl :
  forall (P Q : A -> Prop) xs,
  (forall a, P a -> Q a) -> Forall P xs -> Forall Q xs.
Proof.
  move => P Q xs H; elim: xs; firstorder.
Qed.

End Seq.

Notation ctxindex xs n x := (Some x = nth None xs n).
Notation ctxleq xs ys := (forall n a, ctxindex xs n a -> ctxindex ys n a).
