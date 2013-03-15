Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq LCAC.ssrnat_ext.

Set Implicit Arguments.

Fixpoint Forall A (P : A -> Prop) xs :=
  if xs is x :: xs then P x /\ Forall P xs else True.

Section Seq.

Variable (A : Type).

Function insert (n : nat) (a : A) (xs : seq A) :=
  if n is n.+1
    then (if xs is x :: xs then x :: insert n a xs else [:: a])
    else a :: xs.

Fixpoint nthopt (xs : seq A) n :=
  if xs is x :: xs
    then (if n is n.+1 then nthopt xs n else Some x)
    else None.

(* drop and take *)

Theorem drop_addn :
  forall n m (xs : seq A), drop n (drop m xs) = drop (n + m) xs.
Proof.
  move => n; elim => [| m IH]; case => // x xs.
  - rewrite addn0 //.
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
  - rewrite sub0n take0 //.
  - rewrite subSS //.
Qed.

Theorem drop_take_nil : forall n (xs : seq A), drop n (take n xs) = [::].
Proof.
  move => n xs; rewrite drop_take_distr -(addn0 n) subnDl take0 //.
Qed.

(* nthopt *)

Theorem nthopt_drop : forall xs n m, nthopt xs (n + m) = nthopt (drop n xs) m.
Proof.
  elim => // x xs IH; case => //.
Qed.

Theorem nthopt_drop' : forall xs n, nthopt xs n = nthopt (drop n xs) 0.
Proof.
  by move => xs n; rewrite -{1}(addn0 n) nthopt_drop.
Qed.

Theorem nthopt_take0 :
  forall xs n m, m <= n -> nthopt (take m xs) n = None.
Proof.
  elim => // x xs IH; case => [| n]; case => //= m; rewrite ltnS; apply IH.
Qed.

Theorem nthopt_take1 :
  forall xs n m, n < m -> nthopt (take m xs) n = nthopt xs n.
Proof.
  by elim => // x xs IH; case => [| n]; case => //= m; rewrite ltnS; apply IH.
Qed.

Theorem nthopt_appl :
  forall xs ys n, n < size xs -> nthopt (xs ++ ys) n = nthopt xs n.
Proof.
  elim => // x xs IH ys; case => //= n; rewrite ltnS; apply IH.
Qed.

Theorem nthopt_appr :
  forall xs ys n, nthopt (xs ++ ys) (size xs + n) = nthopt ys n.
Proof.
  elim => //.
Qed.

(* insert *)

Theorem insert_eq :
  forall n (a : A) (xs : seq A), insert n a xs = take n xs ++ a :: drop n xs.
Proof.
  elim => [| n IHn] a.
  - by move => xs; rewrite take0 drop0.
  - by case => //= x xs; f_equal.
Qed.

Theorem insert_nthopt_l :
  forall m n a xs,
  m < n -> m < size xs -> nthopt (insert n a xs) m = nthopt xs m.
Proof.
  elim => //=.
  - by case => // n a; case.
  - move => m IH; case => // n a; case => //= x xs.
    rewrite !ltnS; apply IH.
Qed.

Theorem insert_nthopt_c :
  forall n a xs, n <= size xs -> nthopt (insert n a xs) n = Some a.
Proof.
  elim => // n IH a; case => //= x xs; rewrite ltnS; apply IH.
Qed.

Theorem insert_nthopt_r :
  forall m n a xs, n <= m -> nthopt (insert n a xs) m.+1 = nthopt xs m.
Proof.
  elim => [| m IH]; case => // n a; case => //= x xs; rewrite ltnS; apply IH.
Qed.

(* Forall *)

Theorem Forall_impl :
  forall (P Q : A -> Prop) xs,
  (forall a : A, P a -> Q a) -> Forall P xs -> Forall Q xs.
Proof.
  move => P Q xs H; elim: xs; firstorder.
Qed.

End Seq.

Notation seqindex xs n x := (Some x = nthopt xs n).
