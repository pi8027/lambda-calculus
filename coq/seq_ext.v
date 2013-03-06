Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq LCAC.ssrnat_ext.

Set Implicit Arguments.

Section Seq.

Variable A : Type.

Function insert (n : nat) (a : A) (xs : seq A) :=
  if n is S n
    then (if xs is x :: xs then x :: insert n a xs else [:: a])
    else a :: xs.

Theorem insert_eq :
  forall n (a : A) (xs : seq A), insert n a xs = take n xs ++ a :: drop n xs.
Proof.
  elim => [| n IHn] a.
  - by move => xs; rewrite take0 drop0.
  - by case => //= x xs; f_equal.
Qed.

Fixpoint seqindex (xs : seq A) n x :=
  if xs is x' :: xs
    then (if n is n.+1 then seqindex xs n x else x = x')
    else False.

Theorem lift_seqindex :
  forall xs ys n a, seqindex ys n a <-> seqindex (xs ++ ys) (size xs + n) a.
Proof.
  elim => //.
Qed.

Theorem appl_seqindex :
  forall xs ys n a, n < size xs ->
  (seqindex (xs ++ ys) n a <-> seqindex xs n a).
Proof.
  elim.
  - move => /= ys n a H.
    apply False_ind; ssromega.
  - move => x xs IH ys; case => //= n a H.
    apply IH.
    by rewrite -ltnS.
Qed.

Theorem appr_seqindex :
  forall xs ys n a, size xs <= n ->
  (seqindex (xs ++ ys) n a <-> seqindex ys (n - size xs) a).
Proof.
  move => xs ys n a H.
  by rewrite -{1}(subnKC H) {H} -lift_seqindex.
Qed.

Theorem insert_seqindex_l :
  forall m n a x xs,
  m < n <= size xs -> (seqindex xs m x <-> seqindex (insert n a xs) m x).
Proof.
  by elim => [| m IHm]; case => // n a x; case => //= _ xs H; apply IHm.
Qed.

Theorem insert_seqindex_c :
  forall n a b xs, n <= size xs -> (a = b <-> seqindex (insert n a xs) n b).
Proof.
  elim => // n IHn a b; case => //= _ xs; rewrite ltnS; apply IHn.
Qed.

Theorem insert_seqindex_r :
  forall m n a x xs,
  n < m -> (seqindex xs m x <-> seqindex (insert n a xs) m.+1 x).
Proof.
  by elim => // m IHm; case => // n a x; case => // x' xs H; apply IHm.
Qed.

Theorem dec_seqindex :
  forall xs n, { a | seqindex xs n a } + ({ a | seqindex xs n a } -> False).
Proof.
  elim => [ | x xs IH] /=.
  - by move => _; right; case.
  - by case => //=; left; exists x.
Defined.

Theorem unique_seqindex :
  forall xs n x y, seqindex xs n x -> seqindex xs n y -> x = y.
Proof.
  elim => // x xs IHxs; case => //= x' y H H0; congruence.
Qed.

End Seq.
