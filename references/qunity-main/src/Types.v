From Coq Require Import Bool Arith Lia FinFun Equality FunctionalExtensionality.
From Qunity Require Import Lists Tactics.
Import ListNotations.

Declare Scope qunity_scope.
Open Scope nat_scope.
Open Scope qunity_scope.

(* empty, singleton, sum, product *)
Inductive type :=
  | void
  | qunit
  | superpos (t0 t1 : type)
  | joint (t0 t1 : type).

Bind Scope qunity_scope with type.

Infix "+" := superpos : qunity_scope.
Infix "*" := joint : qunity_scope.

#[export]
Instance eqb_type : has_eqb type :=
  fix eqb_type t t' :=
  match t, t' with
  | void, void | qunit, qunit =>
      true
  | t0 + t1, t0' + t1' | t0 * t1, t0' * t1' =>
      eqb_type t0 t0' && eqb_type t1 t1'
  | _, _ =>
      false
  end.

Example bit : type := qunit + qunit.

Inductive prog_type :=
  | coherent (t t' : type)
  | channel (t t' : type).

Infix "~>" :=
  coherent (no associativity, at level 55) :
  qunity_scope.
Notation "t ==> t'" :=
  (channel t t') (no associativity, at level 55, t' at level 55) :
  qunity_scope.

(* number of values in the type *)
Fixpoint cardinal t : nat :=
  match t with
  | void => 0
  | qunit => 1
  | t0 + t1 => cardinal t0 + cardinal t1
  | t0 * t1 => cardinal t0 * cardinal t1
  end.

(* number of qubits used to store a value *)
Fixpoint size t : nat :=
  match t with
  | void | qunit => 0
  | t0 + t1 => S (max (size t0) (size t1))
  | t0 * t1 => size t0 + size t1
  end.

Lemma eqb_type_refl :
  forall t, eqb_type t t = true.
Proof.
  intros t. induction t; simpl; auto with bool.
Qed.

#[export]
Instance eqb_type_valid :
  valid_eqb eqb_type.
Proof.
  split; auto using eqb_type_refl.
  intros t.
  induction t; intros [] H; cbn in *;
  autorewrite with bool in *; unpack; auto_false;
  apply IHt1 in H; apply IHt2 in H0; congruence.
Qed.

#[export]
Hint Rewrite eqb_type_refl : bool.

#[export]
Hint Resolve eqb_type_valid : eqb_db.
