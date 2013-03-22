Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Omega
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  LCAC.Relations_ext.

Set Implicit Arguments.

Inductive term (V : Type) : Type :=
  var of V | app of term V & term V | abs of term (option V).

Notation term' n V := (term (iter n option V)).

Fixpoint tmap (V1 V2 : Type) (f : V1 -> V2) (t : term V1) : term V2 :=
  match t with
    | var a => var (f a)
    | app tl tr => app (tmap f tl) (tmap f tr)
    | abs t => abs (tmap (Option.map f) t)
  end.

Fixpoint substitute
  (V : Type) (n : nat) (t1 : term' n V) (t2 : term' n.+1 V) : term' n V :=
  match t2 with
    | var None => t1
    | var (Some v) => var v
    | app t2l t2r => app (substitute t1 t2l) (substitute t1 t2r)
    | abs t2' => abs (@substitute _ n.+1 (@tmap _ _ (@Some _) t1) t2')
  end.

Reserved Notation "t ->1b t'" (at level 70, no associativity).
Reserved Notation "t ->bp t'" (at level 70, no associativity).

Inductive betared1 : forall V, relation (term V) :=
  | betared1beta :
    forall V (t1 : term (option V)) (t2 : term V),
    app (abs t1) t2 ->1b @substitute V 0 t2 t1
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
    t1 ->bp t1' -> t2 ->bp t2' -> app (abs t1) t2 ->bp @substitute V 0 t2' t1'
  where "t ->bp t'" := (parred t t').
