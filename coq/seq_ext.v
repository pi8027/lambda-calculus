Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq.

Set Implicit Arguments.

Fixpoint Forall A (P : A -> Prop) xs :=
  if xs is x :: xs then P x /\ Forall P xs else True.

Section Seq.

Variable (A : Type).

Fixpoint nthopt (xs : seq A) n :=
  if xs is x :: xs
    then (if n is n.+1 then nthopt xs n else Some x)
    else None.

(* drop and take *)

Theorem drop_addn :
  forall n m (xs : seq A), drop n (drop m xs) = drop (n + m) xs.
Proof.
  move => n; elim => [| m IH]; case => // x xs.
  - by rewrite addn0.
  - by rewrite addnS /= IH.
Qed.

Theorem take_minn :
  forall n m (xs : seq A), take n (take m xs) = take (minn n m) xs.
Proof.
  elim => [| n IH]; case => [| m]; case => [| x xs] => //.
  by rewrite minnSS /=; f_equal.
Qed.

Theorem drop_take_distr :
  forall n m (xs : seq A), drop n (take m xs) = take (m - n) (drop n xs).
Proof.
  elim => [| n IH]; case => [| m]; case => [| x xs] => //=.
  - by rewrite sub0n take0.
  - by rewrite subSS.
Qed.

Theorem drop_take_nil : forall n (xs : seq A), drop n (take n xs) = [::].
Proof.
  by move => n xs; rewrite drop_take_distr -(addn0 n) subnDl take0.
Qed.

Theorem size_take : forall n (xs : seq A), size (take n xs) = minn n (size xs).
Proof.
  by elim => [| n IH]; case => //= x xs; rewrite IH minnSS.
Qed.

(* Forall *)

Theorem Forall_impl :
  forall (P Q : A -> Prop) xs,
  (forall a, P a -> Q a) -> Forall P xs -> Forall Q xs.
Proof.
  move => P Q xs H; elim: xs; firstorder.
Qed.

End Seq.
