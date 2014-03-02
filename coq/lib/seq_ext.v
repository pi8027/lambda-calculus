Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq LCAC.lib.ssrnat_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

(* nth *)

Lemma nth_map' (f : A -> B) x xs n : f (nth x xs n) = nth (f x) (map f xs) n.
Proof. by elim: xs n => [n | x' xs IH []] //=; rewrite !nth_nil. Qed.

Lemma nth_equal (a b : A) xs n :
  (size xs <= n -> a = b) -> nth a xs n = nth b xs n.
Proof. by elim: xs n => [n /= -> | x xs IH []]. Qed.

End Seq.

(* insert *)

Definition insert A xs ys d n : seq A :=
  take n ys ++ nseq (n - size ys) d ++ xs ++ drop n ys.

Section Insert.

Variable (A B : Type).

Lemma size_insert (xs ys : seq A) d n :
  size (insert xs ys d n) = size xs + maxn n (size ys).
Proof. rewrite /insert !size_cat size_nseq size_take size_drop; ssromega. Qed.

Lemma map_insert (f : A -> B) xs ys d n :
  map f (insert xs ys d n) = insert (map f xs) (map f ys) (f d) n.
Proof. by rewrite /insert !map_cat map_take map_nseq size_map map_drop. Qed.

Lemma nth_insert (xs ys : seq A) d d' n m :
  nth d (insert xs ys d' n) m =
  if m < n then nth d' ys m else
  if m < n + size xs then nth d' xs (m - n) else nth d ys (m - size xs).
Proof.
  rewrite /insert !nth_cat size_take size_nseq -subnDA nth_drop.
  have ->: minn n (size ys) + (n - size ys) = n by ssromega.
  elimif; try ssromega.
  - apply nth_equal; ssromega.
  - rewrite nth_nseq H0 nth_default //; ssromega.
  - rewrite nth_take //; apply nth_equal; ssromega.
Qed.

End Insert.

(* context *)

Definition context A := (seq (option A)).

Notation ctxindex xs n x := (Some x == nth None xs n).
Notation ctxmap f xs := (map (omap f) xs).
Notation ctxinsert xs ys n := (insert xs ys None n).

Section Context1.

Variable (A : eqType).

Fixpoint ctxleq_rec (xs ys : context A) : bool :=
  match xs, ys with
    | [::], _ => true
    | (None :: xs), [::] => ctxleq_rec xs [::]
    | (None :: xs), (_ :: ys) => ctxleq_rec xs ys
    | (Some _ :: _), [::] => false
    | (Some x :: xs), (Some y :: ys) => (x == y) && ctxleq_rec xs ys
    | (Some _ :: _), (None :: _) => false
  end.

Definition ctxleq := nosimpl ctxleq_rec.

Infix "<=c" := ctxleq (at level 70, no associativity).

Lemma ctxleqE xs ys :
  (xs <=c ys) =
  ((head None xs == head None ys) || (head None xs == None)) &&
    (behead xs <=c behead ys).
Proof.
  move: xs ys => [| [x |] xs] [| [y |] ys] //=.
  by case/boolP: (Some x == None) => // _; rewrite orbF.
Qed.

Lemma ctxleq0l xs : [::] <=c xs.
Proof. done. Qed.

Lemma ctxleql0 ys : (ys <=c [::]) = (ys == nseq (size ys) None).
Proof. by elim: ys => //=; case. Qed.

Lemma ctxleqnl xs ys : (None :: xs <=c ys) = (xs <=c behead ys).
Proof. by case: ys. Qed.

Lemma ctxleqln xs ys :
  (xs <=c None :: ys) = (head None xs == None) && (behead xs <=c ys).
Proof. by move: xs => [] //= []. Qed.

Lemma ctxleqsl x xs ys :
  (Some x :: xs <=c ys) = (Some x == head None ys) && (xs <=c behead ys).
Proof. by move: ys => [] //= []. Qed.

Lemma ctxleqls xs y ys :
  (xs <=c Some y :: ys) =
  ((head None xs == None) || (head None xs == Some y)) && (behead xs <=c ys).
Proof. by move: xs => [] //= []. Qed.

Lemma ctxleqss x xs y ys :
  (Some x :: xs <=c Some y :: ys) = (x == y) && (xs <=c ys).
Proof. by rewrite ctxleqsl. Qed.

Lemma ctxleqcc x xs y ys :
  (x :: xs <=c y :: ys) = ((x == y) || (x == None)) && (xs <=c ys).
Proof. by rewrite ctxleqE. Qed.

Lemma ctxleqcl x xs ys :
  (x :: xs <=c ys) = ((x == head None ys) || (x == None)) && (xs <=c behead ys).
Proof. by rewrite ctxleqE. Qed.

Lemma ctxleqlc xs y ys :
  (xs <=c y :: ys) =
  ((head None xs == y) || (head None xs == None)) && (behead xs <=c ys).
Proof. by rewrite ctxleqE. Qed.

Lemma ctxleqP (xs ys : context A) :
  reflect (forall n a, ctxindex xs n a -> ctxindex ys n a) (ctxleq xs ys).
Proof.
  apply: (iffP idP); elim: xs ys => [| x xs IH].
  - by move => ys _ n a; rewrite nth_nil.
  - by case => [| y ys]; rewrite ctxleqcl /=; case/andP; case/orP;
      move/eqP => ?; subst => H [] //= n a; move/(IH _ H) => //;
      rewrite nth_nil.
  - by move => ys; rewrite ctxleq0l.
  - by case => [| y ys]; rewrite ctxleqcl /= => H; apply/andP;
      (apply conj;
       [ case: x H; rewrite ?eqxx ?orbT // => x H; rewrite (H 0 x) |
         apply IH => n a; move/(H n.+1 a) ]).
Qed.

Lemma ctxleqxx (xs : context A) : xs <=c xs.
Proof. by apply/ctxleqP. Qed.

Lemma ctxleq_trans (xs ys zs : context A) :
  xs <=c ys -> ys <=c zs -> xs <=c zs.
Proof. do 2 move/ctxleqP => ?; apply/ctxleqP; auto. Qed.

Lemma ctxleq_app (xs xs' ys ys' : context A) :
  size xs = size xs' ->
  (xs ++ ys) <=c (xs' ++ ys') = (xs <=c xs') && (ys <=c ys').
Proof.
  elim: xs xs' => [| x xs IH] [] //= x' xs' [].
  by rewrite !ctxleqcc; move/IH => ->; rewrite andbA.
Qed.

Lemma ctxleq_appl (xs ys zs : context A) :
  (xs ++ ys <=c xs ++ zs) = (ys <=c zs).
Proof. by rewrite ctxleq_app // ctxleqxx. Qed.

Lemma ctxleq_appr (xs ys : context A) : xs <=c (xs ++ ys).
Proof. by rewrite -{1}(cats0 xs) ctxleq_appl ctxleq0l. Qed.

End Context1.

Hint Resolve ctxleq0l ctxleql0 ctxleqnl ctxleqln ctxleqsl ctxleqls ctxleqss
             ctxleqcc ctxleqcl ctxleqlc.

Infix "<=c" := ctxleq (at level 70, no associativity).

Section Context3.

Variable (A B : eqType).

Lemma ctxindex_map (f : A -> B) xs n x :
  ctxindex xs n x -> ctxindex (ctxmap f xs) n (f x).
Proof. by elim: xs n x => [| x xs IH] [] //= x' /eqP <-. Qed.

Lemma ctxleq_map (f : A -> B) xs ys :
  xs <=c ys -> ctxmap f xs <=c ctxmap f ys.
Proof.
  move/ctxleqP => H; apply/ctxleqP => n a.
  move: (H n).
  rewrite -!(nth_map' (omap f) None).
  case: (nth None xs n) => //= a' H0.
  by move/eqP: (H0 a' (eqxx _)) => <- /=.
Qed.

End Context3.

Hint Resolve ctxindex_map ctxleqxx ctxleq_trans ctxleq_app
             ctxleq_appl ctxleq_appr ctxleq_map.

(* Forall *)

Fixpoint Forall A (P : A -> Prop) xs :=
  if xs is x :: xs then P x /\ Forall P xs else True.

Lemma Forall_impl :
  forall (A : Type) (P Q : A -> Prop) xs,
  (forall a, P a -> Q a) -> Forall P xs -> Forall Q xs.
Proof. move => A P Q xs H; elim: xs; firstorder. Qed.

Lemma Forall_map (A B : Type) (f : A -> B) P xs :
  Forall P (map f xs) <-> Forall (P \o f) xs.
Proof. by elim: xs => //= x xs ->. Qed.

Lemma Forall_nth (A : Type) (P : A -> Prop) xs :
  Forall P xs <-> (forall x m, m < size xs -> P (nth x xs m)).
Proof.
  elim: xs => //= x' xs [] IH IH'; split.
  - by case => H H0 x [] //= n; rewrite ltnS; apply IH.
  - move => H; split.
    + by apply (H x' 0).
    + by apply IH' => x m; apply (H x m.+1).
Qed.

Lemma allP' (A : eqType) (P : pred A) xs :
  reflect (Forall P xs) (all P xs).
Proof.
  apply (iffP idP); elim: xs => //= x xs IH.
  - by case/andP => -> /IH.
  - by case => ->.
Qed.
