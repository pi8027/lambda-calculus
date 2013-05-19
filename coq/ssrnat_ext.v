Require Import
  Omega Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat.

Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [andb _ _] |- _ => let H0 := fresh in case/andP: H => H H0
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
  do ?arith_hypo_ssrnat2coqnat ;
  do ?arith_goal_ssrnat2coqnat ;
  omega.
