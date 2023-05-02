From PLF Require Export LibTactics.
From Coq Require Import Bool ZArith String RelationClasses.

Set Implicit Arguments.

#[export]
Instance or_sym : Symmetric or.
Proof.
  intros P Q [H | H]; auto.
Qed.

Class has_eqb (A : Set) : Set :=
  eqb : A -> A -> bool.

Declare Scope qunity_scope.
Infix "=?" := eqb : qunity_scope.
Open Scope qunity_scope.

Class valid_eqb A `(has_eqb A) : Prop :=
  { eqb_refl : forall e : A, e =? e = true;
    eqb_sound : forall e e', e =? e' = true -> e = e' }.

#[export]
Instance eqb_string : has_eqb string :=
  String.eqb.

#[export]
Instance eqb_string_valid :
  valid_eqb eqb_string.
Proof.
  split.
  - apply String.eqb_refl.
  - apply String.eqb_eq.
Qed.

Lemma eqb_eq :
  forall (A : Set) eqb,
  valid_eqb eqb <-> forall e e' : A, e =? e' = true <-> e = e'.
Proof.
  intros A eqb. split.
  - intros [Hr Hs] e e'. split; intros H; subst; auto.
  - intros H. split; intros; apply H; auto.
Qed.

Lemma rewrite_eqb :
  forall (A : Set) eqb,
  valid_eqb eqb ->
  forall e e' : A, e =? e' = true <-> e = e'.
Proof. apply eqb_eq. Qed.

Lemma valid_eqb_sym :
  forall (A : Set) eqb,
  valid_eqb eqb ->
  forall e e' : A, (e =? e') = (e' =? e).
Proof.
  intros A eqb H e e'. destruct (e =? e') eqn:E.
  - apply eqb_sound in E. subst. symmetry. apply eqb_refl.
  - destruct (e' =? e) eqn:E'; auto.
    apply eqb_sound in E'. subst. rewrite eqb_refl in E. discriminate.
Qed.

#[export]
Hint Rewrite
  andb_true_r orb_false_r String.eqb_eq eqb_refl
  andb_true_iff orb_true_iff andb_false_iff orb_false_iff and_assoc :
  bool.

Create HintDb eqb_db.

#[export]
Hint Resolve Build_valid_eqb eqb_string_valid : eqb_db.
