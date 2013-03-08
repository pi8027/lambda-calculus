Require Import
  Lists.List
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq LCAC.ssrnat_ext.

Set Implicit Arguments.

Section Seq.

Variable A B : Type.

Theorem Forall_app : forall (P : A -> Prop) xs ys,
  Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
Proof.
  move => P xs ys H0 H; move: xs H0.
  by refine (Forall_ind _ _ _) => //= x xs H0 H1 IHxs; constructor.
Qed.

Theorem Forall_map : forall (P : B -> Prop) (f : A -> B) xs,
  Forall P (map f xs) <-> Forall (fun x => P (f x)) xs.
Proof.
  move => P f; elim => //= x xs IH;
    split => H; inversion H; subst; constructor; tauto.
Qed.

Theorem drop_take_nil : forall n (xs : seq A), drop n (take n xs) = [::].
Proof.
  move => n xs; rewrite drop_oversize //=.
  move: xs n; elim => // x xs IH; case => //=.
Qed.

Theorem drop_addn :
  forall n m (xs : seq A), drop n (drop m xs) = drop (n + m) xs.
Proof.
  elim => [| n IH] m; case => [| x xs] //.
  - by rewrite drop0 add0n.
  - rewrite addSn //= -IH; clear; move: m x xs; elim => //=.
    - by move => _ xs; rewrite drop0.
    - move => m IH _; case => //.
Qed.

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

Fixpoint nthopt (xs : seq A) n :=
  if xs is x :: xs
    then (if n is n.+1 then nthopt xs n else Some x)
    else None.

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

Notation seqindex xs n x := (Some x = nthopt xs n).

Theorem seqindex_drop :
  forall (xs : seq A) n m a,
  seqindex xs (n + m) a <-> seqindex (drop n xs) m a.
Proof.
  elim => [| x xs IH]; case => //.
Qed.

Theorem lift_seqindex :
  forall xs ys n a, seqindex ys n a <-> seqindex (xs ++ ys) (size xs + n) a.
Proof.
  elim => //.
Qed.

Theorem appl_seqindex :
  forall xs ys n a, n < size xs ->
  (seqindex (xs ++ ys) n a <-> seqindex xs n a).
Proof.
  elim => // x xs IH ys; case => //= n a; rewrite ltnS; apply IH.
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
  elim => [| n IHn] a b; case => //=.
  - move => _; split; congruence.
  - move => _ _ _; split; congruence.
  - move => _ xs; rewrite ltnS; apply IHn.
Qed.

Theorem insert_seqindex_r :
  forall m n a x xs,
  n <= m -> (seqindex xs m x <-> seqindex (insert n a xs) m.+1 x).
Proof.
  by elim => [| m IHm]; case => // n a x; case => //= x' xs; apply IHm.
Qed.

Theorem dec_seqindex :
  forall xs n, { a | seqindex xs n a } + ({ a | seqindex xs n a } -> False).
Proof.
  elim => [ | x xs IH] //=.
  - by move => _; right; case.
  - by case => //; left; exists x.
Defined.

Theorem unique_seqindex :
  forall xs n x y, seqindex xs n x -> seqindex xs n y -> x = y.
Proof.
  elim => // x xs IH; case => //=; congruence.
Qed.

End Seq.

Notation seqindex xs n x := (Some x = nthopt xs n).
