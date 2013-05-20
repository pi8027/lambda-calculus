Require Import
  Omega Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat.

Tactic Notation "find_minneq_hyp" constr(n) constr(m) :=
  match goal with
    | H : is_true (n <= m) |- _ => move/minn_idPl: (H)
    | H : is_true (m <= n) |- _ => move/minn_idPr: (H)
    | |- _ =>
      let H0 := fresh "H" in
      case/orP: (leq_total n m) => H0;
      [move/minn_idPl: (H0) | move/minn_idPr: (H0)]
  end.

Tactic Notation "find_maxneq_hyp" constr(n) constr(m) :=
  match goal with
    | H : is_true (n <= m) |- _ => move/maxn_idPr: (H)
    | H : is_true (m <= n) |- _ => move/maxn_idPl: (H)
    | |- _ =>
      let H0 := fresh "H" in
      case/orP: (leq_total n m) => H0;
      [move/maxn_idPr: (H0) | move/maxn_idPl: (H0)]
  end.

Ltac replace_minn_maxn :=
  match goal with
    | H : context [minn ?n ?m] |- _ => move: H; find_minneq_hyp n m => -> H
    | H : context [maxn ?n ?m] |- _ => move: H; find_maxneq_hyp n m => -> H
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
  do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec in *;
  repeat (let x := fresh "x" in move => x);
  do ?replace_minn_maxn;
  do ?arith_hypo_ssrnat2coqnat;
  do ?arith_goal_ssrnat2coqnat;
  omega.

(* test codes for ssromega *)

Goal forall m n, maxn m n - minn m n = (m - n) + (n - m). ssromega; fail. Abort.
Goal forall m n, minn m n + maxn m n = m + n. ssromega; fail. Abort.
Goal forall m n, minn (maxn m n) m = m. ssromega; fail. Abort.
Goal forall m n, minn n (maxn m n) = n. ssromega; fail. Abort.
Goal forall m n, maxn (minn m n) m = m. ssromega; fail. Abort.
Goal forall m n, maxn n (minn m n) = n. ssromega; fail. Abort.
Goal forall m n, minn m n = m <-> m <= n. split; ssromega; fail. Abort.
Goal forall m n, maxn m n = n <-> m <= n. split; ssromega; fail. Abort.
