Require Import
  Omega Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Tactic Notation "find_minneq_hyp" constr(n) constr(m) :=
  match goal with
    | H : is_true (n <= m) |- _ => move/minn_idPl: (H)
    | H : is_true (m <= n) |- _ => move/minn_idPr: (H)
    | |- _ =>
      let H := fresh "H" in
      case/orP: (leq_total n m) => H;
      [move/minn_idPl: (H) | move/minn_idPr: (H)]
  end.

Tactic Notation "find_maxneq_hyp" constr(n) constr(m) :=
  match goal with
    | H : is_true (n <= m) |- _ => move/maxn_idPr: (H)
    | H : is_true (m <= n) |- _ => move/maxn_idPl: (H)
    | |- _ =>
      let H := fresh "H" in
      case/orP: (leq_total n m) => H;
      [move/maxn_idPr: (H) | move/maxn_idPl: (H)]
  end.

Ltac replace_minn_maxn :=
  let H' := fresh "H" in
  match goal with
    | H : context [minn ?n ?m] |- _ =>
      find_minneq_hyp n m => H'; rewrite H' {H'} in H
    | H : context [maxn ?n ?m] |- _ =>
      find_maxneq_hyp n m => H'; rewrite H' {H'} in H
    | |- context [minn ?n ?m] => find_minneq_hyp n m => ->
    | |- context [maxn ?n ?m] => find_maxneq_hyp n m => ->
  end.

Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [andb _ _] |- _ => let H0 := fresh "H" in case/andP: H => H H0
    | H : context [orb _ _] |- _ => case/orP in H
    | H : context [?L <= ?R] |- _ => move/leP in H
    | H : context [?L == ?R] |- _ => move/eqP in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  match goal with
    | |- is_true (andb _ _) => apply/andP; split
    | |- is_true (orb _ _) => apply/orP
    | |- is_true (_ <= _) => apply/leP
    | |- is_true (eqn _ _) => apply/eqnP
  end.

Ltac ssromega :=
  repeat (let x := fresh "x" in move => x);
  do ?replace_minn_maxn;
  do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec in *;
  do ?arith_hypo_ssrnat2coqnat;
  do ?arith_goal_ssrnat2coqnat;
  omega.

Ltac elimleq :=
  let H := fresh "H" in
  match goal with
    | [ |- is_true (?m <= ?n) -> _ ] =>
      move => H; rewrite -(subnKC H) ?(addnK, addKn, addnA);
      move: {n H} (n - m) => n
  end.

(* test codes for ssromega *)

Goal forall m n, minn (maxn m n) m = m. ssromega; fail. Abort.
Goal forall m n, minn n (maxn m n) = n. ssromega; fail. Abort.
Goal forall m n, maxn (minn m n) m = m. ssromega; fail. Abort.
Goal forall m n, maxn n (minn m n) = n. ssromega; fail. Abort.
Goal forall m n, maxn m n = m + (n - m). ssromega; fail. Abort.
Goal forall m n, minn m n = m - (m - n). ssromega; fail. Abort.
Goal forall m n, minn m n = m <-> m <= n. split; ssromega; fail. Abort.
Goal forall m n, maxn m n = n <-> m <= n. split; ssromega; fail. Abort.
Goal forall m n, maxn m n - minn m n = (m - n) + (n - m). ssromega; fail. Abort.
Goal forall m n, minn m n - maxn m n = 0. ssromega; fail. Abort.
Goal forall m n, minn m n + maxn m n = m + n. ssromega; fail. Abort.
Goal forall m n, minn m n + (m - n) = m. ssromega; fail. Abort.
Goal forall m n, maxn m n - (n - m) = m. ssromega; fail. Abort.

(* Extended comparison predicates. *)

CoInductive leq_xor_gtn' m n :
    bool -> bool -> bool -> bool ->
    nat -> nat -> nat -> nat -> nat -> nat -> Set :=
  | LeqNotGtn' of m <= n :
    leq_xor_gtn' m n (m < n) false true (n <= m) n n m m 0 (n - m)
  | GtnNotLeq' of n < m :
    leq_xor_gtn' m n false true false true m m n n (m - n) 0.

Lemma leqP' m n : leq_xor_gtn' m n
  (m < n) (n < m) (m <= n) (n <= m)
  (maxn m n) (maxn n m) (minn m n) (minn n m)
  (m - n) (n - m).
Proof.
  case: (leqP m n) => H; rewrite (maxnC n) (minnC n).
  - rewrite (maxn_idPr H) (minn_idPl H).
    by move: (H); rewrite -subn_eq0 => /eqP ->; constructor.
  - rewrite (ltnW H) ltnNge leq_eqVlt H orbT
            (maxn_idPl (ltnW H)) (minn_idPr (ltnW H)).
    by move: (ltnW H); rewrite -subn_eq0 => /eqP ->; constructor.
Qed.

CoInductive compare_nat' m n :
    bool -> bool -> bool -> bool -> bool ->
    nat -> nat -> nat -> nat -> nat -> nat -> Set :=
  | CompareNatLt' of m < n :
    compare_nat' m n true false false true false n n m m 0 (n - m)
  | CompareNatGt' of m > n :
    compare_nat' m n false true false false true m m n n (m - n) 0
  | CompareNatEq' of m = n :
    compare_nat' m n false false true true true m m m m 0 0.

Lemma ltngtP' m n : compare_nat' m n
  (m < n) (n < m) (m == n) (m <= n) (n <= m)
  (maxn m n) (maxn n m) (minn m n) (minn n m)
  (m - n) (n - m).
Proof.
  (case: (ltngtP m n) => H;
    last by rewrite -H leqnn maxnn minnn subnn; constructor);
    rewrite (maxnC n) (minnC n) ?(ltnW H) leqNgt H /=.
  - rewrite (maxn_idPr (ltnW H)) (minn_idPl (ltnW H)).
    by move: (ltnW H); rewrite -subn_eq0 => /eqP ->; constructor.
  - rewrite (maxn_idPl (ltnW H)) (minn_idPr (ltnW H)).
    by move: (ltnW H); rewrite -subn_eq0 => /eqP ->; constructor.
Qed.
