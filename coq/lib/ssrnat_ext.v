Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ssromega *)

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
    | H : is_true false |- _ => by move: H
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

(* Other automation tactics. *)

Module simpl_natarith.

Lemma lem1_1 ml mr n r : ml = r + n -> ml + mr = r + mr + n.
Proof. by move => ->; rewrite addnAC. Qed.
Lemma lem1_2 ml mr n r : mr = r + n -> ml + mr = ml + r + n.
Proof. by move => ->; rewrite addnA. Qed.
Lemma lem1_3 m' n r : m' = r + n -> m'.+1 = r.+1 + n.
Proof. by move => ->; rewrite addSn. Qed.
Lemma lem2_1 ml mr n r : ml - n = r -> ml - mr - n = r - mr.
Proof. by move => <-; rewrite subnAC. Qed.
Lemma lem2_2 m' n r : m' - n = r -> m'.-1 - n = r.-1.
Proof. by move => <-; rewrite -subnS -add1n subnDA subn1. Qed.
Lemma lem2_3 m n r : m = r + n -> m - n = r.
Proof. by move => ->; rewrite addnK. Qed.
Lemma lem4_1 m n m' n' : m - n = m' - n' -> (m <= n) = (m' <= n').
Proof. by rewrite -!subn_eq0 => ->. Qed.

End simpl_natarith.

Import simpl_natarith.

Ltac simpl_natarith1 m n :=
  match m with
    | n => constr: (esym (add0n n))
    | ?ml + ?mr => let H := simpl_natarith1 ml n in constr: (lem1_1 mr H)
    | ?ml + ?mr => let H := simpl_natarith1 mr n in constr: (lem1_2 ml H)
    | ?m'.+1 => let H := simpl_natarith1 m' n in constr: (lem1_3 H)
    | ?m'.+1 => match n with 1 => constr: (esym (addn1 m')) end
  end.

Ltac simpl_natarith2 m n :=
  match m with
    | ?ml - ?mr => let H := simpl_natarith2 ml n in constr: (lem2_1 mr H)
    | ?m'.-1 => let H := simpl_natarith2 m' n in constr: (lem2_2 H)
    | _ => let H := simpl_natarith1 m n in constr: (lem2_3 H)
  end.

Ltac simpl_natarith3 m n :=
  lazymatch n with
    | ?nl + ?nr =>
      simpl_natarith3 m nl;
      match goal with |- _ = ?m1 -> _ =>
        let H := fresh "H" in
        simpl_natarith3 m1 nr => H;
        move/(fun H' => eq_trans (subnDA _ _ _)
                       (eq_trans (f_equal (subn^~ _) H')
                       (eq_trans H (esym (subnDA _ _ _))))); clear H
      end
    | _ =>
      match n with
        | ?n'.+1 =>
          lazymatch n' with
            | 0 => fail
            | _ => simpl_natarith3 m (n' + 1);
                   move/(eq_trans (f_equal (subn m) (esym (addn1 _))))
          end
        | _ =>
          let H := simpl_natarith2 m n in move: (eq_trans H (esym (subn0 _)))
        | _ => move: (erefl (m - n))
      end
  end.

Ltac simpl_natarith :=
  let H' := fresh "H" in
  let tac := (rewrite {}H'
    ?(addSn, addnS, add0n, addn0, sub0n, subn0, subSS, leq0n)) in
  repeat match goal with
    | H : context [?m - ?n] |- _ =>
      simpl_natarith3 m n => H'; move: H; tac => H
    | |- context [?m - ?n] =>
      simpl_natarith3 m n => H'; tac
    | H : context [?m <= ?n] |- _ =>
      simpl_natarith3 m n; move/lem4_1 => H'; move: H; tac => H
    | |- context [?m <= ?n] =>
      simpl_natarith3 m n; move/lem4_1 => H'; tac
  end;
  repeat match goal with
    | H : is_true true |- _ => move => {H}
  end.

Tactic Notation "elimleq" :=
  match goal with
    | |- is_true (_ <= _ _) -> _ => fail
    | |- is_true (?m <= ?n) -> _ =>
      (let H := fresh "H" in move/subnKC => H; rewrite <- H in *; clear H);
      (let rec tac :=
        lazymatch reverse goal with
          | H : context [n] |- _ => move: H; tac => H
          | _ => move: {n} (n - m) => n
        end in tac);
      simpl_natarith
  end.

Tactic Notation "elimleq" constr(H) := move: H; elimleq.

Ltac elimif :=
  (match goal with
     | |- context [if ?m < ?n then _ else _] => case (leqP' n m)
     | |- context [if ?m <= ?n then _ else _] => case (leqP' m n)
     | |- context [if ?b then _ else _] => case (ifP b)
   end;
   move => //=; elimif; let hyp := fresh "H" in move => hyp) ||
  idtac.

Ltac elimif_omega :=
  elimif;
  try (repeat match goal with
    | |- _ + _ = _ => idtac
    | |- _ - _ = _ => idtac
    | |- _ => f_equal
  end; ssromega);
  repeat match goal with H : is_true (?m <= ?n) |- _ => elimleq H end.
