Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Omega Psatz LCAC.lib.seq_ext_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition natE :=
  (addSn, addnS, add0n, addn0, sub0n, subn0, subSS,
   min0n, minn0, max0n, maxn0, leq0n).

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

(* simpl_natarith *)

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
Lemma lem3_1 m m' m'' nl nl' nl'' nr nr' :
  m - nl = m' - nl' -> m' - nl' - nr = m'' - nl'' - nr' ->
  m - (nl + nr) = m'' - (nl'' + nr').
Proof. by rewrite !subnDA => -> ->. Qed.
Lemma lem3_2 m n r : m - (n + 1) = r -> m - n.+1 = r.
Proof. by rewrite addn1. Qed.
Lemma lem3_3 m n r : m - n = r -> m - n = r - 0.
Proof. by rewrite subn0. Qed.
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
        move => H; simpl_natarith3 m1 nr; move/(lem3_1 H) => {H}
      end
    | _ =>
      match n with
        | ?n'.+1 =>
          lazymatch n' with
            | 0 => fail
            | _ => simpl_natarith3 m (n' + 1); move/lem3_2
          end
        | _ => let H := simpl_natarith2 m n in move: (lem3_3 H)
        | _ => move: (erefl (m - n))
      end
  end.

Ltac simpl_natarith :=
  let tac x :=
    lazymatch goal with
      | |- ?x = ?x -> _ => move => _; rewrite !natE
      | _ => move => ->; rewrite ?natE
    end in
  repeat
    (match goal with
       H : context [?m - ?n] |- _ => move: H; simpl_natarith3 m n; tac 0 => H
     end ||
     match goal with
       |- context [?m - ?n] => simpl_natarith3 m n; tac 0
     end ||
     match goal with
       H : context [?m <= ?n] |- _ =>
       move: H; simpl_natarith3 m n; move/lem4_1; tac 0 => H
     end ||
     match goal with
       |- context [?m <= ?n] => simpl_natarith3 m n; move/lem4_1; tac 0
     end);
  try done;
  repeat match goal with
    | H : is_true true |- _ => clear H
                               (* "move => {H}" may unfold the "is_true" *)
  end.

(* elimleq *)

Tactic Notation "elimleq" :=
  match goal with |- is_true (?n <= ?m) -> _ =>
    is_var m;
    (let H := fresh "H" in move/subnKC => H; rewrite <- H in *; clear H);
    let rec tac :=
      lazymatch reverse goal with
        | H : context [m] |- _ => move: H; tac => H
        | _ => move: {m} (m - n) => m; rewrite ?(addKn, addnK)
      end in tac; simpl_natarith
  end.

Tactic Notation "elimleq" constr(H) := move: H; elimleq.

(* ssromega *)

Tactic Notation "find_minneq_hyp" constr(m) constr(n) :=
  match goal with
    | H : is_true (m <= n) |- _ => rewrite (minn_idPl H)
    | H : is_true (n <= m) |- _ => rewrite (minn_idPr H)
    | H : is_true (m < n) |- _ => rewrite (minn_idPl (ltnW H))
    | H : is_true (n < m) |- _ => rewrite (minn_idPr (ltnW H))
    | |- _ => case (leqP' m n)
  end; rewrite ?natE.

Tactic Notation "find_maxneq_hyp" constr(m) constr(n) :=
  match goal with
    | H : is_true (m <= n) |- _ => rewrite (maxn_idPr H)
    | H : is_true (n <= m) |- _ => rewrite (maxn_idPl H)
    | H : is_true (m < n) |- _ => rewrite (maxn_idPr (ltnW H))
    | H : is_true (n < m) |- _ => rewrite (maxn_idPl (ltnW H))
    | |- _ => case (leqP' m n)
  end; rewrite ?natE.

Ltac replace_minn_maxn :=
  try (rewrite <- minnE in * || rewrite <- maxnE in * );
  match goal with
    | H : context [minn ?m ?n] |- _ => move: H; find_minneq_hyp n m => H
    | H : context [maxn ?m ?n] |- _ => move: H; find_maxneq_hyp n m => H
    | |- context [minn ?m ?n] => find_minneq_hyp m n
    | |- context [maxn ?m ?n] => find_maxneq_hyp m n
  end;
  try (let x := fresh "x" in move => x).

Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : is_true false    |- _ => by move: H
    | H : is_true (_ && _) |- _ => let H0 := fresh "H" in case/andP: H => H H0
    | H : is_true (_ || _) |- _ => case/orP in H
    | H : is_true (_ <  _) |- _ => move/ltP in H
    | H : is_true (_ <= _) |- _ => move/leP in H
    | H : is_true (_ == _) |- _ => move/eqP in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  match goal with
    | |- is_true (_ && _) => apply/andP; split
    | |- is_true (_ || _) => apply/orP
    | |- is_true (_ <  _) => apply/ltP
    | |- is_true (_ <= _) => apply/leP
    | |- is_true (_ == _) => apply/eqP
  end.

Ltac ssromega :=
  repeat (let x := fresh "x" in move => x);
  do ?replace_minn_maxn;
  try done;
  repeat match goal with H : is_true (?m <= ?n) |- _ => elimleq H end;
  do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec in *;
  do ?arith_hypo_ssrnat2coqnat;
  do ?arith_goal_ssrnat2coqnat;
  simpl Equality.sort in *;
  lia.

Ltac elimif' :=
  (match goal with
     | |- context [if ?m < ?n then _ else _] => case (leqP' n m)
     | |- context [if ?m <= ?n then _ else _] => case (leqP' m n)
     | |- context [if ?b then _ else _] => case (ifP b)
   end;
   move => //=; elimif'; let hyp := fresh "H" in move => hyp) ||
  idtac.

Ltac elimif :=
  elimif'; simpl_natarith;
  repeat match goal with H : is_true (?m <= ?n) |- _ => elimleq H end.

Ltac elimif_omega :=
  elimif;
  try (repeat match goal with
    | |- @eq nat _ _ => idtac
    | |- nth _ _ _ = nth _ _ _ => apply nth_equal
    | |- _ => f_equal
  end; ssromega).

(* congruence' *)

Ltac congruence' := simpl; try (move: addSn addnS; congruence).

(* test code for ssromega *)

Module ssromega_test.
Goal forall m n, minn (maxn m n) m = m. ssromega. Qed.
Goal forall m n, minn n (maxn m n) = n. ssromega. Qed.
Goal forall m n, maxn (minn m n) m = m. ssromega. Qed.
Goal forall m n, maxn n (minn m n) = n. ssromega. Qed.
Goal forall m n, maxn m n = m + (n - m). ssromega. Qed.
Goal forall m n, minn m n = m - (m - n). ssromega. Qed.
Goal forall m n, minn m n = m <-> m <= n. split; ssromega. Qed.
Goal forall m n, maxn m n = n <-> m <= n. split; ssromega. Qed.
Goal forall m n, maxn m n - minn m n = (m - n) + (n - m). ssromega. Qed.
Goal forall m n, minn m n - maxn m n = 0. ssromega. Qed.
Goal forall m n, minn m n + maxn m n = m + n. ssromega. Qed.
Goal forall m n, minn m n + (m - n) = m. ssromega. Qed.
Goal forall m n, maxn m n - (n - m) = m. ssromega. Qed.
End ssromega_test.
