Require Import
  Omega Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat.

Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [andb _ _] |- _ => let H0 := fresh in case/andP: H => H H0
    | H : context [orb _ _] |- _ => case/orP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L == ?R] |- _ => move/eqP: H => H
    | H : context [addn ?L ?R] |- _ => rewrite -plusE in H
    | H : context [subn ?L ?R] |- _ => rewrite -minusE in H
    | H : context [muln ?L ?R] |- _ => rewrite -multE in H
    | H : context [addn_rec ?L ?R] |- _ => rewrite /addn_rec in H
    | H : context [subn_rec ?L ?R] |- _ => rewrite /subn_rec in H
    | H : context [muln_rec ?L ?R] |- _ => rewrite /muln_rec in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  rewrite ?NatTrec.trecE -?plusE -?minusE -?multE;
  repeat match goal with
    | |- is_true (andb _ _) => apply/andP; split
    | |- is_true (orb _ _) => apply/orP
    | |- is_true (_ <= _) => apply/leP
    | |- is_true (eqn _ _) => apply/eqnP
  end.

Ltac ssromega :=
  repeat arith_hypo_ssrnat2coqnat ;
  arith_goal_ssrnat2coqnat ;
  (omega || apply False_ind; omega).
