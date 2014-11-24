Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Seq.

Variable (A B : Type).

(* drop and take *)

Lemma drop_addn n m (xs : seq A) : drop n (drop m xs) = drop (n + m) xs.
Proof.
  elim: m xs => [| m IH] [] // x xs.
  - by rewrite addn0.
  - by rewrite addnS /= IH.
Qed.

Lemma take_minn n m (xs : seq A) : take n (take m xs) = take (minn n m) xs.
Proof. by elim: n m xs => [| n IH] [| m] [] // x xs; rewrite minnSS /= IH. Qed.

Lemma drop_take_distr n m (xs : seq A) :
  drop n (take m xs) = take (m - n) (drop n xs).
Proof.
  elim: n m xs => [m xs | n IH [xs | m [] //= _ xs]].
  - by rewrite !drop0 subn0.
  - by rewrite sub0n !take0.
  - by rewrite subSS IH.
Qed.

Lemma take_drop_distr n m (xs : seq A) :
  take n (drop m xs) = drop m (take (n + m) xs).
Proof. by rewrite drop_take_distr addnK. Qed.

Lemma drop_take_nil n (xs : seq A) : drop n (take n xs) = [::].
Proof. by rewrite drop_take_distr subnn take0. Qed.

Lemma size_take n (xs : seq A) : size (take n xs) = minn n (size xs).
Proof.
  elim: n xs => [xs | n IH [] //= _ xs].
  - by rewrite take0 min0n.
  - by rewrite minnSS IH.
Qed.

Lemma nth_take' x n m (xs : seq A) :
  nth x (take n xs) m = if n <= m then x else nth x xs m.
Proof.
  case: (leqP n m) => H.
  - by rewrite nth_default // size_take geq_min H.
  - by rewrite nth_take.
Qed.

(* nth *)

Lemma nth_map' (f : A -> B) x xs n : f (nth x xs n) = nth (f x) (map f xs) n.
Proof. by elim: xs n => [n | x' xs IH []] //=; rewrite !nth_nil. Qed.

Lemma nth_equal (a b : A) xs n :
  (size xs <= n -> a = b) -> nth a xs n = nth b xs n.
Proof. by elim: xs n => [n /= -> | x xs IH []]. Qed.

End Seq.
