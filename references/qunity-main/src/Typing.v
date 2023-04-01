From Coq Require Import Basics Permutation Vector Morphisms.
From Qunity Require Import Tactics Reals Sets Lists Types Syntax Contexts.
Import ListNotations QunityNotations.

Set Implicit Arguments.

Open Scope list_scope.
Open Scope qunity_scope.

(* Set of free variables *)
Fixpoint free_vars e : set :=
  match e with
  | null =>
      []
  | var x =>
      [x]
  | #(e0, e1)
  | try e0 e1 =>
      free_vars e0 ++ free_vars e1
  | ctrl e' t l t' =>
      free_vars e' ++
      flat_map (fun '(ej, ej') => diff (free_vars ej') (free_vars ej)) l
  | e' |> f =>
      free_vars e'
  end.

Inductive spanning : type -> list expr -> Prop :=
  | spanning_var t (x : string) :
      spanning t [x : expr]
  | spanning_void :
      spanning void []
  | spanning_null :
      spanning qunit [null]
  | spanning_sum t0 t1 l0 l1 :
      spanning t0 l0 ->
      spanning t1 l1 ->
      spanning (t0 + t1)
        (map (apply (left t0 t1)) l0 ++ map (apply (right t0 t1)) l1)
  | spanning_pair t0 t1 (l : list (expr * list expr)) :
      spanning t0 (map fst l) ->
      (forall e0 l1, In (e0, l1) l -> spanning t1 l1) ->
      (forall e0 l1, In (e0, l1) l -> disjoint (free_vars e0) (flat_map free_vars l1)) ->
      spanning (t0 * t1) (flat_map (fun '(e0, l1) => map (qpair e0) l1) l)
  | spanning_perm t l l' :
      Permutation l l' ->
      spanning t l ->
      spanning t l'.

Definition ortho t l : Prop :=
  exists l',
  sublist l l' /\ spanning t l'.

Inductive erases (x : string) : type -> list expr -> Prop :=
  | erases_var n t :
      erases x t (repeat (x : expr) n)
  | erases_gphase t l1 e gamma l2 :
      erases x t (l1 ++ e :: l2) ->
      erases x t (l1 ++ (gphase t gamma e) :: l2)
  | erases_ctrl t t' e l l1 l2 :
      erases x t (l1 ++ map snd l ++ l2) ->
      erases x t (l1 ++ ctrl e t' l t :: l2)
  | erases_pair0 t0 t1 l :
      erases x t0 (map fst l) ->
      erases x (t0 * t1) (map (uncurry qpair) l)
  | erases_pair1 t0 t1 l :
      erases x t1 (map snd l) ->
      erases x (t0 * t1) (map (uncurry qpair) l).

(* Main typing relation *)
Inductive has_pure_type : context -> context -> expr -> type -> Prop :=
  | has_type_null g :
      well_formed g ->
      has_pure_type g [] null qunit
  | has_type_cvar x t (g : context):
      g x = None ->
      well_formed g ->
      has_pure_type ((x, t) :: g) [] x t
  | has_type_qvar (g : context) x t :
      g x = None ->
      well_formed g ->
      has_pure_type g [(x, t)] x t
  | has_pure_type_pair (g d d0 d1 : context) e0 e1 t0 t1 :
      well_formed (g ++ d ++ d0 ++ d1) ->
      has_pure_type g (d ++ d0) e0 t0 ->
      has_pure_type g (d ++ d1) e1 t1 ->
      has_pure_type g (d ++ d0 ++ d1) #(e0, e1) (t0 * t1)
  | has_type_ctrl :
      forall (g g' d d' : context) (l : list (expr * expr * context)) e t t',
      well_formed (g ++ g' ++ d ++ d') ->
      has_mixed_type (g ++ d) e t ->
      ortho t (map (compose fst fst) l) ->
      (forall gj ej ej',
       In (ej =>> ej', gj) l ->
       has_pure_type [] gj ej t) ->
      (forall gj ej ej',
       In (ej =>> ej', gj) l ->
       has_pure_type (g ++ g' ++ gj) (d ++ d') ej' t') ->
      (forall x, In x (dom d) -> erases x t' (map (compose snd fst) l)) ->
      has_pure_type (g ++ g') (d ++ d') (ctrl e t (map fst l) t') t'
  | has_pure_type_app g d e f t t' :
      has_prog_type f (t ~> t') ->
      has_pure_type g d e t ->
      has_pure_type g d (f e) t'
  | has_pure_type_swap (g1 g2 g3 g4 d1 d2 d3 d4 : context) e t :
      has_pure_type (g1 ++ g2 ++ g3 ++ g4) (d1 ++ d2 ++ d3 ++ d4) e t ->
      has_pure_type (g1 ++ g3 ++ g2 ++ g4) (d1 ++ d3 ++ d2 ++ d4) e t
with has_mixed_type : context -> expr -> type -> Prop :=
  | has_type_mix d e t :
      has_pure_type [] d e t ->
      has_mixed_type d e t
  | has_mixed_type_pair (d d0 d1 : context) e0 e1 t0 t1 :
      well_formed (d ++ d0 ++ d1) ->
      has_mixed_type (d ++ d0) e0 t0 ->
      has_mixed_type (d ++ d1) e1 t1 ->
      has_mixed_type (d ++ d0 ++ d1) #(e0, e1) (t0 * t1)
  | has_type_try d d' e e' t :
      disjoint (dom d) (dom d') ->
      has_mixed_type d e t ->
      has_mixed_type d' e' t ->
      has_mixed_type (d ++ d') (try e e') t
  | has_mixed_type_app d e f t t' :
      has_prog_type f (t ==> t') ->
      has_mixed_type d e t ->
      has_mixed_type d (f e) t'
  | has_mixed_type_swap (d1 d2 d3 d4 : context) e t :
      has_mixed_type (d1 ++ d2 ++ d3 ++ d4) e t ->
      has_mixed_type (d1 ++ d3 ++ d2 ++ d4) e t
with has_prog_type : prog -> prog_type -> Prop :=
  | has_type_u3 theta phi lambda :
      has_prog_type (u3 theta phi lambda) (bit ~> bit)
  | has_type_left t0 t1 :
      has_prog_type (left t0 t1) (t0 ~> t0 + t1)
  | has_type_right t0 t1 :
      has_prog_type (right t0 t1) (t1 ~> t0 + t1)
  | has_coherent_type_abs d e e' t t' :
      has_pure_type [] d e t ->
      has_pure_type [] d e' t' ->
      has_prog_type (lambda e t e') (t ~> t')
  | has_type_rphase d t e gamma' gamma :
      has_pure_type [] d e t ->
      has_prog_type (rphase t e gamma' gamma) (t ~> t)
  | has_type_channel f t t' :
      has_prog_type f (t ~> t') ->
      has_prog_type f (t ==> t')
  | has_channel_type_abs (d d0 : context) e e' t t' :
      has_pure_type [] (d ++ d0) e t ->
      has_mixed_type d e' t' ->
      has_prog_type (lambda e t e') (t ==> t').

(* Mutual induction schemes with more information *)
Scheme pure_mixed_prog_ind := Induction for has_pure_type Sort Prop
  with mixed_pure_prog_ind := Induction for has_mixed_type Sort Prop
  with prog_pure_mixed_ind := Induction for has_prog_type Sort Prop.

Combined Scheme has_type_ind
  from pure_mixed_prog_ind, mixed_pure_prog_ind, prog_pure_mixed_ind.

Lemma pure_typed_well_formed :
  forall g d e t,
  has_pure_type g d e t ->
  well_formed (g ++ d).
Proof.
  intros g d e t H.
  induction H; try rewrite app_nil_r; auto.
  - apply well_formed_cons. auto.
  - rewrite <- Permutation_cons_append, well_formed_cons. auto.
  - rewrite <- app_assoc. assumption.
  - eapply well_formed_perm; try apply IHhas_pure_type.
    apply Permutation_app;
    apply Permutation_app_head; repeat rewrite app_assoc;
    apply Permutation_app_tail, Permutation_app_comm.
Qed.

Lemma pure_type_permute_g :
  forall g g' d e t,
  Permutation g g' ->
  has_pure_type g d e t ->
  has_pure_type g' d e t.
Proof.
  intros g g' d e t Hp H. rewrite Permutation_Permutation_transp in Hp.
  induction Hp; auto.
  replace (x :: y :: l2) with ([x] ++ [y] ++ l2) by reflexivity.
  replace d with ([] ++ [] ++ [] ++ d) by reflexivity.
  constructor. assumption.
Qed.

Lemma pure_type_permute_d :
  forall g d d' e t,
  Permutation d d' ->
  has_pure_type g d e t ->
  has_pure_type g d' e t.
Proof.
  intros g d d' e t Hp H. rewrite Permutation_Permutation_transp in Hp.
  induction Hp; auto.
  replace g with ([] ++ [] ++ [] ++ g) by reflexivity.
  replace (x :: y :: l2) with ([x] ++ [y] ++ l2) by reflexivity.
  constructor. assumption.
Qed.

(* Allows for rewriting via permutations *)
#[export]
Instance pure_type_proper :
  Proper
    (Permutation (A:=string*type) ==>
     Permutation (A:=string*type) ==>
     eq ==>
     eq ==>
     impl)
    has_pure_type.
Proof.
  intros g g' Hg d d' Hd e e' He t t' Ht H. subst.
  eauto using pure_type_permute_g, pure_type_permute_d.
Qed.

Lemma mixed_type_permute :
  forall d d' e t,
  Permutation d d' ->
  has_mixed_type d e t ->
  has_mixed_type d' e t.
Proof.
  intros d d' e t Hp H. rewrite Permutation_Permutation_transp in Hp.
  induction Hp; auto.
  replace (x :: y :: l2) with ([x] ++ [y] ++ l2) by reflexivity.
  apply has_mixed_type_swap. assumption.
Qed.

#[export]
Instance mixed_type_proper :
  Proper
    (Permutation (A:=string*type) ==> eq ==> eq ==> impl) has_mixed_type.
Proof.
  intros d d' Hd e e' He t t' Ht H. subst. eauto using mixed_type_permute.
Qed.

(* Sometimes more convenient than partitioning the context *)
Lemma has_type_find_cvar :
  forall (g : context) x t,
  well_formed g ->
  g x = Some t ->
  has_pure_type g [] x t.
Proof.
  intros g x t Hw H. apply context_find_inv_cons in H as [g' H]. rewrite H in *.
  apply well_formed_cons in Hw as [Hg Hw]. constructor; assumption.
Qed.

Lemma ortho_nil :
  forall t, ortho t [].
Proof.
  intros t. induction t; exists [var "x"]; split; eauto using sublist, spanning.
Qed.

Lemma erases_nil :
  forall x t, erases x t [].
Proof.
  intros x t. replace [] with (repeat (var x) 0) by reflexivity. constructor.
Qed.
