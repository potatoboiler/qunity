From Coq Require Export String List ListSet.
From Coq Require Import
  Bool String Permutation Basics Equality RelationClasses Morphisms Lia.
From Qunity Require Import Tactics Lists.
Import List.
Import ListNotations.
Import String (eqb).

Set Implicit Arguments.

Open Scope string_scope.
Open Scope list_scope.

Definition set := (list string).

Fixpoint mem (x : string) (X : set) : bool :=
  match X with
  | [] => false
  | x' :: X' => eqb x x' || mem x X'
  end.

Fixpoint diff (X X' : set) : set :=
  match X with
  | [] => []
  | x :: X2 =>
      if mem x X'
      then diff X2 X'
      else x :: diff X2 X'
  end.

Fixpoint disjointb (X X' : set) : bool :=
  match X with
  | [] => true
  | x :: X2 => negb (mem x X') && disjointb X2 X'
  end.

Fixpoint dollars n : string :=
  match n with
  | 0 => ""
  | S n' => "$" ++ dollars n'
  end.

Definition fresh X : string :=
  dollars (S (list_max (map String.length X))).

Definition inclusion (X X' : set) : Prop :=
  forall x, In x X -> In x X'.

Infix "<=" := inclusion : list_scope.

Definition equiv (X X' : set) : Prop :=
  forall x, In x X <-> In x X'.

Infix "~=" := equiv : list_scope.

Definition disjoint (X X' : set) :=
  forall x, In x X -> In x X' -> False.

#[export]
Instance eqb_string_valid :
  valid_eqb eqb.
Proof.
  split.
  - apply String.eqb_refl.
  - apply String.eqb_eq.
Qed.

#[export]
Hint Rewrite eqb_string_valid : bool.

Lemma mem_spec :
  forall x X, mem x X = true <-> In x X.
Proof.
  intros x X. induction X; simpl; auto_false.
  autorewrite with bool; auto using eqb_string_valid.
  split; intros; branches; subst; auto; right; apply IHX; assumption.
Qed.

Lemma mem_existsb :
  forall x X, mem x X = existsb (eqb x) X.
Proof.
  intros x X. induction X as [| x' X]; auto.
  simpl. destruct (x =? x'); auto.
Qed.

#[export]
Hint Rewrite mem_spec : bool.

Lemma inclusion_refl :
  forall X, X <= X.
Proof.
  intros X. unfold inclusion. tauto.
Qed.

Lemma inclusion_trans :
  forall X1 X2 X3,
  X1 <= X2 ->
  X2 <= X3 ->
  X1 <= X3.
Proof.
  unfold inclusion. intros X1 X2 X3 H1 H2 x H. auto.
Qed.

#[export]
Instance inclusion_preorder : PreOrder inclusion :=
{|
  PreOrder_Reflexive := inclusion_refl;
  PreOrder_Transitive := inclusion_trans
|}.

Lemma inclusion_nil :
  forall X, X <= [] -> X = [].
Proof.
  intros X H. destruct X; auto.
  exfalso. apply (H s). left. reflexivity.
Qed.

Lemma equiv_inclusion :
  forall X X', X ~= X' -> X <= X'.
Proof.
  unfold inclusion, equiv. intros X X' H x Hx. apply H, Hx.
Qed.

Lemma equiv_refl :
  forall X, X ~= X.
Proof.
  intros X. unfold equiv. tauto.
Qed.

Lemma equiv_sym :
  forall X X', X ~= X' -> X' ~= X.
Proof.
  unfold equiv. intros X X' H x. symmetry. apply H.
Qed.

Lemma equiv_trans :
  forall X1 X2 X3, X1 ~= X2 -> X2 ~= X3 -> X1 ~= X3.
Proof.
  unfold equiv. intros X1 X2 X3 H1 H3 x. rewrite H1. apply H3.
Qed.

#[export]
Instance equiv_Equivalence : Equivalence equiv :=
{|
  Equivalence_Reflexive := equiv_refl;
  Equivalence_Symmetric := equiv_sym;
  Equivalence_Transitive := equiv_trans
|}.

#[export]
Instance cons_proper :
  forall x, Proper (equiv ==> equiv) (cons x).
Proof.
  intros x X X' H. unfold equiv in *. intros x'. simpl.
  split; intros [He | Hi]; subst; auto; right; apply H; assumption.
Qed.

Lemma cons_in_equiv :
  forall x X, In x X -> x :: X ~= X.
Proof.
  intros x X H x'. simpl. split; auto.
  intros [He | Hi]; subst; auto.
Qed.

Lemma swap_equiv :
  forall x x' X, x :: x' :: X ~= x' :: x :: X.
Proof.
  intros x x' X s. simpl. tauto.
Qed.

#[export]
Instance in_proper_impl :
  forall x, Proper (equiv ==> impl) (In x).
Proof.
  intros x X X' H. unfold impl. apply (H x).
Qed.

#[export]
Instance in_proper_iff :
  forall x, Proper (equiv ==> iff) (In x).
Proof.
  intros x X X' H. apply H.
Qed.

#[export]
Instance app_proper :
  Proper (equiv ==> equiv ==> equiv) (app (A:=string)).
Proof.
  intros X0 X1 H X0' X1' H' x.
  repeat rewrite in_app_iff. rewrite H, H'. reflexivity.
Qed.

Lemma equiv_nil :
  forall X, X ~= [] -> X = [].
Proof.
  intros [] H; auto.
  exfalso. eapply H. simpl. eauto.
Qed.

#[export]
Instance disjoint_sym :
  Symmetric disjoint.
Proof.
  unfold disjoint. eauto.
Qed.

Lemma disjoint_nil0 :
  forall X, disjoint [] X.
Proof.
  intros X x. auto.
Qed.

Lemma disjoint_nil1 :
  forall X, disjoint X [].
Proof.
  intros X x. auto.
Qed.

Lemma disjoint_cons1 :
  forall X X' x,
  disjoint X (x :: X') <-> ~ In x X /\ disjoint X X'.
Proof.
  unfold disjoint. simpl. intros X X' x. split.
  - intros H. split.
    + intros Hc. eapply H; eauto.
    + intros x' H0 H1. eapply H; eauto.
  - intros [Hx Hd] x' H' [He | Hi]; subst; eauto.
Qed.

Lemma disjoint_cons0 :
  forall X X' x,
  disjoint (x :: X) X' <-> ~ In x X' /\ disjoint X X'.
Proof.
  intros X X' x. split; intros H.
  - symmetry in H. apply disjoint_cons1 in H. unpack.
    split; auto using disjoint_sym.
  - symmetry. apply disjoint_cons1. unpack. split; auto using disjoint_sym.
Qed.

Lemma disjoint_singleton1 :
  forall X x,
  disjoint X [x] <-> ~ In x X.
Proof.
  intros X x. rewrite disjoint_cons1.
  split; intros; unpack; auto using disjoint_nil1.
Qed.

Lemma disjoint_app1 :
  forall X X0 X1,
  disjoint X (X0 ++ X1) <-> disjoint X X0 /\ disjoint X X1.
Proof.
  intros X X0 X1. induction X0 as [| x0 X0]; simpl.
  - split.
    + intros H. split; auto using disjoint_sym, disjoint_nil1.
    + intros [_ H]. assumption.
  - repeat rewrite disjoint_cons1. rewrite IHX0. tauto.
Qed.

Lemma disjoint_app0 :
  forall X0 X1 X,
  disjoint (X0 ++ X1) X <-> disjoint X0 X /\ disjoint X1 X.
Proof.
  intros X0 X1 X. split.
  - intros H.
    split; apply disjoint_sym, disjoint_app1 in H; apply disjoint_sym, H.
  - intros [H0 H1]. apply disjoint_sym, disjoint_app1. auto using disjoint_sym.
Qed.

Lemma disjoint_concat1 :
  forall X l,
  disjoint X (concat l) <-> forall X', In X' l -> disjoint X X'.
Proof.
  intros X l. unfold disjoint. split.
  - intros H X' H' x Hi Hx. eapply H; try apply Hi.
    apply in_concat. exists X'. auto.
  - intros H x Hx H'. apply in_concat in H' as [X' [Hi H']]. eauto.
Qed.

#[export]
Instance disjoint_proper :
  Proper (inclusion ==> inclusion ==> flip impl) disjoint.
Proof.
  intros X1 X1' H1 X2 X2' H2 H x H1' H2'. eapply H.
  - apply H1, H1'.
  - apply H2, H2'.
Qed.

Lemma disjointb_true :
  forall X X', disjointb X X' = true <-> disjoint X X'.
Proof.
  intros X X'.
  induction X; simpl; split; auto using disjoint_nil0; autorewrite with bool.
  - intros H. autorewrite with bool in H. unpack. apply IHX in H0.
    unfold disjoint in *. intros x [Ha | Hx] H'; eauto.
    subst. apply mem_spec in H'. rewrite H' in H. discriminate.
  - intros H. split.
    + apply eq_true_not_negb. intros Hc. apply mem_spec in Hc.
      eapply H; try apply Hc.
      simpl. auto.
    + apply IHX. intros x H1 H2. eapply H; try apply H2.
      simpl. auto.
Qed.

Lemma inclusion_cons_iff :
  forall x X X',
  (x :: X) <= X' <-> In x X' /\ X <= X'.
Proof.
  intros x X X'. unfold inclusion. simpl. split; intros; auto.
  unpack. branches; subst; auto.
Qed.

Lemma dollars_length :
  forall n, String.length (dollars n) = n.
Proof.
  intros n. induction n; simpl; auto.
Qed.

Lemma fresh_spec :
  forall X, ~ In (fresh X) X.
Proof.
  intros X. remember (fresh X) as d. unfold fresh in Heqd.
  assert (list_max (map (String.length) X) < String.length d).
  - subst. rewrite dollars_length. lia.
  - clear Heqd. intros Hc. apply in_map with (f:=String.length) in Hc.
    rewrite list_max_lt in H.
    + induction H; simpls; auto.
      destruct Hc; auto.
      lia.
    + intros H'. rewrite H' in Hc. contradiction.
Qed. (* this could probably be cleaner *)

Lemma Permutation_equiv :
  forall X X', Permutation X X' -> X ~= X'.
Proof.
  intros X X' H x. split; apply Permutation_in; auto using Permutation_sym.
Qed.

#[export]
Instance disjoint_proper_equiv :
  Proper (equiv ==> equiv ==> impl) disjoint.
Proof.
  intros X0 X0' H0 X1 X1' H1 H.
  symmetry in H0, H1. apply equiv_inclusion in H0, H1.
  rewrite H0, H1. assumption.
Qed.

#[export]
Instance disjoint_proper_perm :
  Proper (Permutation (A:=string) ==> Permutation (A:=string) ==> impl)
    disjoint.
Proof.
  intros X0 X0' H0 X1 X1' H1 H. apply Permutation_equiv in H0, H1.
  rewrite <- H0, <- H1. assumption.
Qed.

Lemma nodupb_equiv :
  forall X, nodupb X ~= X.
Proof.
  intros X x. apply in_nodupb; auto with eqb_db.
Qed.

