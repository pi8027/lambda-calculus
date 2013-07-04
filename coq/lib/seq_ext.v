Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq LCAC.lib.ssrnat_ext.

Set Implicit Arguments.

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
  elim => [m xs | n IH [xs | m [] //= _ xs]].
  - by rewrite !drop0 subn0.
  - by rewrite sub0n !take0.
  - by rewrite subSS IH.
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
  elim => [xs | n IH [] //= _ xs].
  - by rewrite take0 min0n.
  - by rewrite minnSS IH.
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

End Seq.

(* context *)

Notation ctxindex xs n x := (Some x = nth None xs n).
Notation ctxleq xs ys := (forall n a, ctxindex xs n a -> ctxindex ys n a).
Infix "<=c" := ctxleq (at level 70, no associativity).

Definition context A := (seq (option A)).

Definition ctxinsert A xs ys n : context A :=
  take n ys ++ nseq (n - size ys) None ++ xs ++ drop n ys.

Section Context.

Variable (A B : Type).

Theorem ctxindex_map :
  forall (f : A -> B) xs n x,
  ctxindex xs n x -> ctxindex (map (omap f) xs) n (f x).
Proof.
  by move => f; elim => [| x xs IH] [] //= x' <-.
Qed.

Theorem size_ctxinsert :
  forall (xs ys : context A) n,
  size (ctxinsert xs ys n) = size xs + maxn n (size ys).
Proof.
  move => xs ys n.
  rewrite /ctxinsert !size_cat size_nseq size_take size_drop.
  ssromega.
Qed.

Theorem map_ctxinsert :
  forall (f : A -> B) xs ys n,
  map (omap f) (ctxinsert xs ys n) =
  ctxinsert (map (omap f) xs) (map (omap f) ys) n.
Proof.
  move => f xs ys n.
  by rewrite /ctxinsert !map_cat map_take map_nseq size_map map_drop.
Qed.

Theorem nth_ctxinsert :
  forall (xs ys : context A) n m,
  nth None (ctxinsert xs ys n) m =
  if m < n then nth None ys m else
  if m < n + size xs then nth None xs (m - n) else nth None ys (m - size xs).
Proof.
  move => xs ys n m.
  rewrite /ctxinsert !nth_cat size_take size_nseq -subnDA.
  replace (minn n (size ys) + (n - size ys)) with n by ssromega.
  do! case: ifP; try ssromega.
  - by move => H H0; rewrite nth_take.
  - move => H H0 H1; rewrite nth_nseq if_same nth_default //; ssromega.
  - do !move => _; f_equal; ssromega.
  - move => H _ _ _ _; rewrite nth_drop; f_equal; ssromega.
Qed.

Theorem ctxleq_refl : forall (xs : context A), ctxleq xs xs.
Proof.
  done.
Qed.

Theorem ctxleq_trans :
  forall (xs ys zs : context A), ctxleq xs ys -> ctxleq ys zs -> ctxleq xs zs.
Proof.
  auto.
Qed.

Theorem ctxleq_nil : forall (xs : context A), ctxleq [::] xs.
Proof.
  by move => xs n a; rewrite nth_nil.
Qed.

Theorem ctxleq_appl :
  forall (xs ys zs : context A), ctxleq ys zs -> ctxleq (xs ++ ys) (xs ++ zs).
Proof.
  by elim => // x xs IH ys zs H [] //=; apply IH.
Qed.

Theorem ctxleq_appr : forall (xs ys : context A), ctxleq xs (xs ++ ys).
Proof.
  by move => xs ys; elim: xs => [n a | x xs H []] //=; rewrite nth_nil.
Qed.

Theorem ctxleq_app :
  forall (xs xs' ys ys' : context A), size xs = size xs' ->
  ctxleq xs xs' -> ctxleq ys ys' -> ctxleq (xs ++ ys) (xs' ++ ys').
Proof.
  elim => [| x xs IH] [] //= x' xs' ys ys' [H] H0 H1 [| n] a /=.
  - apply (H0 0 a).
  - apply IH => // m; apply (H0 m.+1).
Qed.

End Context.

Theorem ctxleq_map :
  forall A B (f : A -> B) xs ys,
  ctxleq xs ys -> ctxleq (map (omap f) xs) (map (omap f) ys).
Proof.
  move => A B f xs ys H n y; move: {H} (H n).
  rewrite -!(nth_map' (omap f) None).
  by case: (nth None xs n) => // a H; rewrite -(H a).
Qed.

(* Forall *)

Fixpoint Forall A (P : A -> Prop) xs :=
  if xs is x :: xs then P x /\ Forall P xs else True.

Theorem Forall_impl :
  forall (A : Type) (P Q : A -> Prop) xs,
  (forall a, P a -> Q a) -> Forall P xs -> Forall Q xs.
Proof.
  move => A P Q xs H; elim: xs; firstorder.
Qed.

Theorem Forall_map :
  forall (A B : Type) (f : A -> B) (P : B -> Prop) xs,
  Forall P (map f xs) <-> Forall (P \o f) xs.
Proof.
  by move => A B f P; elim => //= x xs ->.
Qed.

Theorem Forall_nth :
  forall (A : Type) (P : A -> Prop) x xs m,
  m < size xs -> Forall P xs -> P (nth x xs m).
Proof.
  move => A P x0; elim => // x xs IH [].
  - by move => _ /= [].
  - by move => n; rewrite /= ltnS => H [_]; apply IH.
Qed.
