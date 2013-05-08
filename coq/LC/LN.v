Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Coq.Program.Program
  Omega
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.Relations_ext.

Set Implicit Arguments.

Notation nopts n T := (iter n option T).

Inductive term (V : Type) : Type :=
  | var of V
  | app of term V & term V
  | abs of term (option V).

Notation term' n V := (term (nopts n V)).

Fixpoint tmap (V1 V2 : Type) (f : V1 -> V2) (t : term V1) : term V2 :=
  match t with
    | var a => var (f a)
    | app tl tr => app (tmap f tl) (tmap f tr)
    | abs t => abs (tmap (Option.map f) t)
  end.

Fixpoint somenth (T : Type) (n : nat) (a : T) : nopts n T :=
  match n with
    | 0 => a
    | n.+1 => Some (somenth n a)
  end.

Fixpoint substitute_var
  (V : Type) (n : nat) (t : term V) : nopts n (option V) -> term' n V :=
  match n with
    | 0 => fun v => match v with
        | None => t
        | Some v => var v
      end
    | n.+1 => fun v => match v with
        | None => var None
        | Some v => tmap some (substitute_var n t v)
      end
  end.

Fixpoint substitute
  (V : Type) (n : nat) (t1 : term V) (t2 : term' n (option V)) : term' n V :=
  match t2 with
    | var v => substitute_var n t1 v
    | app t2l t2r => app (substitute n t1 t2l) (substitute n t1 t2r)
    | abs t2' => abs (substitute n.+1 t1 t2')
  end.

Fixpoint substitute_seq_var2
  (V : Type) (ts : seq (term V)) : nopts (size ts) V -> term V :=
  match ts with
    | [::] => fun v => var v
    | t :: ts => fun v => match v with
        | None => t
        | Some v => substitute_seq_var2 ts v
      end
  end.

Fixpoint substitute_seq_var1
  (V : Type) (n : nat) (ts : seq (term V)) :
  nopts (n + size ts) V -> term' (n + 0) V :=
  match n with
    | 0 => fun v => substitute_seq_var2 ts v
    | n.+1 => fun v => match v with
        | None => var None
        | Some v => tmap some (substitute_seq_var1 n ts v)
      end
  end.

Fixpoint substitute_seq
  (V : Type) (n : nat) (ts : seq (term V)) (t : term' (n + size ts) V) :
  term' (n + 0) V :=
  match t with
    | var v => substitute_seq_var1 n ts v
    | app tl tr => app (substitute_seq n ts tl) (substitute_seq n ts tr)
    | abs t => abs (substitute_seq n.+1 ts t)
  end.

Lemma substitute_seq_nil :
  forall V n (t : term' (n + 0) V), substitute_seq n [::] t = t.
Proof.
  fix IH 3 => V n; case => //=.
  - elim: n => // {IH} n IH //=; case => // v.
    by rewrite (IH v).
  - move => tl tr; f_equal; apply IH.
  - move => t; f_equal; apply IH.
Qed.

Reserved Notation "t ->1b t'" (at level 70, no associativity).
Reserved Notation "t ->bp t'" (at level 70, no associativity).

Inductive betared1 : forall V, relation (term V) :=
  | betared1beta :
    forall V (t1 : term (option V)) (t2 : term V),
    app (abs t1) t2 ->1b substitute 0 t2 t1
  | betared1appl :
    forall V (t1 t1' t2 : term V), t1 ->1b t1' -> app t1 t2 ->1b app t1' t2
  | betared1appr :
    forall V (t1 t2 t2' : term V), t2 ->1b t2' -> app t1 t2 ->1b app t1 t2'
  | betared1abs  :
    forall V (t t' : term (option V)), t ->1b t' -> abs t ->1b abs t'
  where "t ->1b t'" := (betared1 t t').

Inductive parred : forall V, relation (term V) :=
  | parredvar  :
    forall V (x : V), var x ->bp var x
  | parredapp  :
    forall V (t1 t1' t2 t2' : term V),
    t1 ->bp t1' -> t2 ->bp t2' -> app t1 t2 ->bp app t1' t2'
  | parredabs  :
    forall V (t t' : term (option V)), t ->bp t' -> abs t ->bp abs t'
  | parredbeta :
    forall V (t1 t1' : term (option V)) (t2 t2' : term V),
    t1 ->bp t1' -> t2 ->bp t2' -> app (abs t1) t2 ->bp substitute 0 t2' t1'
  where "t ->bp t'" := (parred t t').
