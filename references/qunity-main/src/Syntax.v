From Coq Require Import Basics Bool String ZArith FunctionalExtensionality.
From Qunity Require Import Reals Types Lists Tactics.
Import EqNotations ListNotations.

Set Implicit Arguments.

Declare Scope qunity_scope.
Open Scope bool_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope real_scope.
Open Scope qunity_scope.

(* the main definition of Qunity syntax *)
Inductive expr : Set :=
  | null
  | var (x : string)
  | qpair (e0 e1 : expr)
  | ctrl (e : expr) (t : type) (l : list (expr * expr)) (t' : type)
  | try (e e' : expr)
  | apply (f : prog) (e : expr)
with prog : Set :=
  | u3 (theta phi lambda : real)
  | left (t0 t1 : type)
  | right (t0 t1 : type)
  | lambda (e : expr) (t : type) (e' : expr)
  | rphase (t : type) (e : expr) (gamma gamma' : real).

(* Additional notations and coercions for making code cleaner *)
Module Import QunityNotations.
  Coercion const : Z >-> real.
  Coercion var : string >-> expr.
  Coercion apply : prog >-> Funclass.
  Notation "e |> f" := (apply f e) (at level 50) : qunity_scope.
  Notation "#( x , y , .. , z )" := (qpair .. (qpair x y) .. z) : qunity_scope.
  Infix "=>>" :=
    (@pair expr expr) (at level 80, no associativity) : qunity_scope.
End QunityNotations.

Module Import Variables.
  Definition x : string := "x".
  Definition x' : string := "x'".
  Definition x0 : string := "x0".
  Definition x1 : string := "x1".
End Variables.

Definition bit := qunit + qunit.
Definition zero := left qunit qunit null.
Definition one := right qunit qunit null.
Definition qid t := lambda x t x.
Definition qnot := u3 pi 0 pi.
Definition had := u3 (pi / 2) 0 pi.
Definition plus := had zero.
Definition maybe t := qunit + t.
Definition nothing t := left qunit t null.
Definition just t := right qunit t.
Definition equals t e := lambda x t (try (lambda e t one x) zero).
Definition qfst t0 t1 := lambda #(x0, x1) (t0 * t1) x0.
Definition qsnd t0 t1 := lambda #(x0, x1) (t0 * t1) x1.
Definition gphase t gamma := rphase t x gamma gamma.

Definition qand := equals (bit * bit) #(one, one).

#[export]
Instance eqb_pair (A0 A1 : Set) (eqb0 : has_eqb A0) (eqb1 : has_eqb A1) :
  has_eqb (A0 * A1) :=
  fun '(e0, e1) '(e0', e1') => eqb0 e0 e0' && eqb1 e1 e1'.

Module Eqb.

  Fixpoint eqb_expr (e e' : expr) {struct e} : bool :=
    match e, e' with
    | null, null =>
        true
    | var x, var x' =>
        String.eqb x x'
    | #(e0, e1), #(e0', e1') =>
        eqb_expr e0 e0' && eqb_expr e1 e1'
    | ctrl e t0 l t1, ctrl e' t0' l' t1' =>
        eqb_expr e e' &&
        eqb_type t0 t0' &&
        eqb_list (H:=eqb_pair eqb_expr eqb_expr) l l' &&
        eqb_type t1 t1'
    | try e1 e2, try e1' e2' =>
        eqb_expr e1 e1' && eqb_expr e2 e2'
    | e |> f, e' |> f' =>
        eqb_prog f f' && eqb_expr e e'
    | _, _ => false
    end
  with eqb_prog (f f' : prog) {struct f} : bool :=
    match f, f' with
    | u3 theta phi lamda, u3 theta' phi' lamda' =>
        eqb_real theta theta' && eqb_real phi phi' && eqb_real lamda lamda'
    | left t0 t1, left t0' t1' =>
        eqb_type t0 t0' && eqb_type t1 t1'
    | right t0 t1, right t0' t1' =>
        eqb_type t0 t0' && eqb_type t1 t1'
    | lambda e1 t e2, lambda e1' t' e2' =>
        eqb_expr e1 e1' && eqb_type t t' && eqb_expr e2 e2'
    | rphase t e r0 r1, rphase t' e' r0' r1' =>
        eqb_type t t' && eqb_expr e e' && eqb_real r0 r0' && eqb_real r1 r1'
    | _, _ => false
    end.

End Eqb.

#[export]
Instance eqb_expr : has_eqb expr := Eqb.eqb_expr.

#[export]
Instance eqb_prog : has_eqb prog := Eqb.eqb_prog.

(* A custom mutual induction scheme that gives more information *)
Fixpoint expr_prog_ind
  (Pe : expr -> Prop)
  (Pf : prog -> Prop)
  (H_null : Pe null)
  (H_var : forall x : string, Pe x)
  (H_pair : forall e0, Pe e0 -> forall e1, Pe e1 -> Pe #(e0, e1))
  (H_ctrl :
   forall e, Pe e ->
   forall t l,
   (forall ej ej', In (ej =>> ej') l -> Pe ej) ->
   (forall ej ej', In (ej =>> ej') l -> Pe ej') ->
   forall t',
   Pe (ctrl e t l t'))
  (H_try : forall e, Pe e -> forall e', Pe e' -> Pe (try e e'))
  (H_app : forall e, Pe e -> forall f, Pf f -> Pe (e |> f))
  (H_u3 : forall theta phi lambda, Pf (u3 theta phi lambda))
  (H_left : forall t0 t1, Pf (left t0 t1))
  (H_right : forall t0 t1, Pf (right t0 t1))
  (H_lambda :
   forall e1, Pe e1 ->
   forall t e2, Pe e2 ->
   Pf (lambda e1 t e2))
  (H_rphase :
   forall t e, Pe e ->
   forall gamma gamma', Pf (rphase t e gamma gamma'))
  (e : expr) :
  Pe e.
Proof.
  destruct e; auto.
  - apply H_pair; apply expr_prog_ind with (Pf:=Pf); assumption.
  - apply H_ctrl.
    + apply expr_prog_ind with (Pf:=Pf); assumption.
    + intros ej ej' Hj. induction l as [| [e0 e0'] l IH]; destruct Hj; auto.
      injection H as H _. rewrite <- H.
      apply expr_prog_ind with (Pf:=Pf); assumption.
    + intros ej ej' Hj. induction l as [| [e0 e0'] l IH]; destruct Hj; auto.
      injection H as _ H. rewrite <- H.
      apply expr_prog_ind with (Pf:=Pf); assumption.
  - apply H_try; apply expr_prog_ind with (Pf:=Pf); assumption.
  - apply H_app.
    + apply expr_prog_ind with (Pf:=Pf); assumption.
    + destruct f; auto.
      * apply H_lambda; apply expr_prog_ind with (Pf:=Pf); assumption.
      * apply H_rphase; apply expr_prog_ind with (Pf:=Pf); assumption.
Qed.

(* A custom induction scheme focused only on expr *)
Lemma expr_ind' :
  forall (P : expr -> Prop),
  P null ->
  (forall x : string, P x) ->
  (forall e0, P e0 -> forall e1, P e1 -> P #(e0, e1)) ->
  (forall e, P e ->
   forall t l,
   (forall ej ej', In (ej =>> ej') l -> P ej) ->
   (forall ej ej', In (ej =>> ej') l -> P ej') ->
   forall t',
   P (ctrl e t l t')) ->
  (forall e, P e -> forall e', P e' -> P (try e e')) ->
  (forall theta phi lambda e, P e -> P (u3 theta phi lambda e)) ->
  (forall t0 t1 e, P e -> P (left t0 t1 e)) ->
  (forall t0 t1 e, P e -> P (right t0 t1 e)) ->
  (forall e1, P e1 ->
   forall t e2, P e2 ->
   forall e3, P e3 ->
   P (lambda e1 t e2 e3)) ->
  (forall e', P e' ->
   forall t e gamma gamma', P e ->
   P (rphase t e gamma gamma' e')) ->
  forall e, P e.
Proof.
  intros.
  induction e using expr_prog_ind
    with (Pf := fun f => forall e, P e -> P (f e));
  auto.
Qed.

#[export]
Instance eqb_pair_valid :
  forall A0 A1 (eqb0 : has_eqb A0) (eqb1 : has_eqb A1),
  valid_eqb eqb0 ->
  valid_eqb eqb1 ->
  valid_eqb (eqb_pair eqb0 eqb1).
Proof.
  intros A0 A1 eqb0 eqb1 H0 H1. split.
  - intros [e0 e1]. cbn.
    destruct H0 as [H0 _], H1 as [H1 _].
    rewrite H0, H1. reflexivity.
  - intros [e0 e1] [e0' e1'] H. cbn in H. autorewrite with bool in H. unpack.
    f_equal; apply eqb_sound; assumption.
Qed.

#[export]
Instance eqb_expr_valid :
  valid_eqb eqb_expr.
Proof.
  split.
  - intros e.
    induction e using expr_ind'; cbn; autorewrite with bool;
    auto using eqb_type_refl, eqb_real_refl, String.eqb_refl.
    splits; auto.
    induction l as [| [e0 e0'] l IHl]; cbn; auto.
    erewrite H, H0, IHl; simpl; auto.
    + intros ej ej' Hj. eapply H. right. apply Hj.
    + intros ej ej' Hj. eapply H0. right. apply Hj.
  - intros e.
    induction e using expr_ind'; intros [] H'; try destruct f;
    try discriminate; cbn in *; repeat f_equal; auto;
    repeat rewrite andb_true_iff in H'; unpack; subst; auto;
    try apply eqb_sound; auto.
    clear e t t' e0 t'0 IHe H1 H4 H2.
    generalize dependent l0.
    induction l as [| [e0 e0'] l0 IH]; intros [| [e1 e1'] l1];
    cbn in *; auto_false.
    autorewrite with bool. intros. unpack.
    repeat f_equal; eauto 6.
Qed.

#[export]
Instance eqb_prog_valid :
  valid_eqb eqb_prog.
Proof.
  split.
  - intros []; unfold eqb; simpl; autorewrite with bool; auto using eqb_refl.
  - intros [] []; unfold eqb; try discriminate; simpl; intros H;
    autorewrite with bool in H; unpack; f_equal; apply eqb_sound; assumption.
Qed.

#[export]
Hint Resolve eqb_pair_valid eqb_expr_valid eqb_prog_valid : eqb_db.
