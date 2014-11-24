Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq LCAC.lib.seq_ext_base LCAC.lib.ssrnat_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  rewrite /insert !nth_cat size_take size_nseq -subnDA nth_drop nth_take'.
  have ->: minn n (size ys) + (n - size ys) = n by ssromega.
  elimif_omega; rewrite nth_nseq H0 nth_default //; ssromega.
Qed.

Lemma take_insert n (xs ys : seq A) d :
  take n (insert xs ys d n) = take n ys ++ nseq (n - size ys) d.
Proof.
  by rewrite /insert take_cat size_take ltnNge geq_minl /= minnE subKn
             ?leq_subr // take_cat size_nseq ltnn subnn take0 cats0.
Qed.

Lemma drop_insert n (xs ys : seq A) d :
  drop (n + size xs) (insert xs ys d n) = drop n ys.
Proof.
  rewrite /insert !catA drop_cat !size_cat size_take size_nseq drop_addn.
  elimif_omega.
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

Lemma ctxleqP (xs ys : context A) :
  reflect (forall n a, ctxindex xs n a -> ctxindex ys n a) (ctxleq xs ys).
Proof.
  apply: (iffP idP); elim: xs ys => [| x xs IH].
  - by move => ys _ n a; rewrite nth_nil.
  - by case => [| y ys]; rewrite ctxleqE /= =>
      /andP [] /orP [] /eqP -> H [] //= n a /(IH _ H) //; rewrite nth_nil.
  - by move => ys; rewrite ctxleqE eqxx orbT.
  - by case => [| y ys]; rewrite ctxleqE /= => H; apply/andP;
      (split;
       [ case: x H; rewrite ?eqxx ?orbT // => x H; rewrite (H 0 x) |
         apply IH => n a /(H n.+1 a) ]).
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
  by rewrite ctxleqE /=; move/IH => ->; apply esym; rewrite ctxleqE /= andbA.
Qed.

Lemma ctxleq_appl (xs ys zs : context A) :
  (xs ++ ys <=c xs ++ zs) = (ys <=c zs).
Proof. by rewrite ctxleq_app // ctxleqxx. Qed.

Lemma ctxleq_appr (xs ys : context A) : xs <=c (xs ++ ys).
Proof. by rewrite -{1}(cats0 xs) ctxleq_appl. Qed.

Lemma ctxindex_last ctx (x : A) : ctxindex (ctx ++ [:: Some x]) (size ctx) x.
Proof. by rewrite nth_cat ltnn subnn. Qed.

End Context1.

Infix "<=c" := ctxleq (at level 70, no associativity).

Section Context2.

Variable (A B : eqType).

Lemma ctxindex_map (f : A -> B) xs n x :
  ctxindex xs n x -> ctxindex (ctxmap f xs) n (f x).
Proof. by elim: xs n x => [| x xs IH] [] //= x' /eqP <-. Qed.

Lemma ctxleq_map (f : A -> B) xs ys :
  xs <=c ys -> ctxmap f xs <=c ctxmap f ys.
Proof.
  move/ctxleqP => H; apply/ctxleqP => n a.
  move: (H n); rewrite -!(nth_map' (omap f) None).
  by case: (nth None xs n) => //= a' /(_ a' (eqxx _)) /eqP => <-.
Qed.

End Context2.

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
