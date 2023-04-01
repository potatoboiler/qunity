From Coq Require Import Bool Arith String Basics Equality RelationClasses.
From Qunity Require Import Tactics.
From Coq Require Export List Permutation.
Import ListNotations.

Set Implicit Arguments.

Open Scope list_scope.

Fixpoint forall_ord_pairs A b (l : list A) :=
  match l with
  | [] => true
  | v :: l' => forallb (b v) l' && forall_ord_pairs b l'
  end.

Fixpoint all_or_nothing A (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | None :: l' => None
  | Some e :: l' => match all_or_nothing l' with
                    | None => None
                    | Some lr => Some (e :: lr)
                    end
  end.

Fixpoint map_maybe A B (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | e :: l => match f e, map_maybe f l with
              | Some e', Some l' => Some (e' :: l')
              | _, _ => None
              end
  end.

Fixpoint flat_map_maybe A B (f : A -> option (list B)) (l : list A) :
  option (list B) :=
  match l with
  | [] => Some []
  | e :: l => match f e, flat_map_maybe f l with
              | Some b, Some l' => Some (b ++ l')
              | _, _ => None
              end
  end.

Fixpoint inb A `{has_eqb A} e l : bool :=
  match l with
  | [] => false
  | e' :: l' => eqb e e' || inb e l'
  end.

Fixpoint dupb A `{has_eqb A} l : bool :=
  match l with
  | [] => false
  | e :: l' => inb e l' || dupb l'
  end.

Fixpoint nodupb A `{has_eqb A} l : list A :=
  match l with
  | [] => []
  | e :: l' => if inb e l' then nodupb l' else e :: nodupb l'
  end.

#[export]
Instance eqb_list A `{has_eqb A} : has_eqb (list A) :=
  fix eqb_list l l' :=
  match l, l' with
  | [], [] => true
  | e :: l, e' :: l' => eqb e e' && eqb_list l l'
  | _, _ => false
  end.

Inductive sublist A : list A -> list A -> Prop :=
  | sublist_nil l :
      sublist [] l
  | sublist_cons1 x l l' :
      sublist l l' ->
      sublist l (x :: l')
  | sublist_cons2 x l l' :
      sublist l l' ->
      sublist (x :: l) (x :: l').

Lemma nth_error_nil :
  forall A n, @nth_error A [] n = None.
Proof.
  intros A n. destruct n; auto.
Qed.

Lemma list_prod_nil :
  forall A A' l, @list_prod A A' l [] = [].
Proof.
  intros A A' l. induction l; auto.
Qed.

Lemma In_ind :
  forall (A : Set) (P : A -> list A -> Prop),
  (forall e l, P e (e :: l)) ->
  (forall e e' l, In e l -> P e l -> P e (e' :: l)) ->
  forall e l, In e l -> P e l.
Proof.
  intros A P Hh Ht e l H. induction l; inversion H; subst; auto.
Qed.

Lemma forall_ord_pairs_true :
  forall (A : Set) (l : list A) f,
  forall_ord_pairs f l = true <-> ForallOrdPairs (fun e e' => f e e' = true) l.
Proof.
  intros A l f. split.
  - induction l as [| e l]; simpl;
    autorewrite with bool; auto using ForallOrdPairs.
    + intros [He Hl]. constructor.
      * rewrite forallb_forall in He. apply Forall_forall, He.
      * apply IHl, Hl.
  - intros H. induction H; simpl; autorewrite with bool; auto.
    split; auto.
    apply forallb_forall, Forall_forall, H.
Qed.

Lemma map_maybe_Some :
  forall A B (f : A -> option B) l l',
  map_maybe f l = Some l' ->
  Forall (fun '(e, e') => f e = Some e') (combine l l').
Proof.
  intros A B f l. induction l as [| e l IH]; simpl; auto.
  intros [| e' li] Hm; constructor; try apply IH;
  destruct (f e), (map_maybe f l); congruence.
Qed.

Lemma map_maybe_Some_length :
  forall A B (f : A -> option B) l l',
  map_maybe f l = Some l' ->
  length l = length l'.
Proof.
  intros A B f l.
  induction l as [| e l IH]; intros [| e' l'] H; simpls; auto_false.
  - destruct (f e), (map_maybe f l); discriminate.
  - f_equal. apply IH. destruct (f e), (map_maybe f l); congruence.
Qed.

Lemma map_maybe_None :
  forall A B (f : A -> option B) l,
  map_maybe f l = None ->
  exists e, In e l /\ f e = None.
Proof.
  intros A B f l. induction l as [| e l IH]; auto_false.
  simpl. intros H. destruct (f e) eqn:E.
  - destruct IH as [e' [Hi Hn]].
    + destruct (map_maybe f l); auto_false.
    + exists e'. auto.
  - exists e. auto.
Qed.

Lemma map_maybe_ext2 :
  forall A B (f g : A -> option B) (f' : B -> B) l lf lg,
  (forall a b, g a = Some b -> f a = Some (f' b)) ->
  map_maybe f l = Some lf ->
  map_maybe g l = Some lg ->
  lf = map f' lg.
Proof.
  intros A B f g f' l. induction l as [| a l IH]; intros lf lg Ha Hf Hg; simpls.
  - injection Hf as. injection Hg as. subst. reflexivity.
  - destruct (f a) eqn:Ef, (g a) eqn:Eg, (map_maybe f l), (map_maybe g l); auto_false.
    injection Hf as. injection Hg as. subst. simpl. f_equal.
    + apply Ha in Eg. congruence.
    + apply IH; auto.
Qed.

Fixpoint sublist_refl (A : Set) (l : list A) : sublist l l :=
  match l with
  | [] => sublist_nil []
  | e :: l' => sublist_cons2 e (sublist_refl l')
  end.

Lemma sublist_nil' :
  forall (A : Set) (l : list A), sublist l [] -> l = [].
Proof.
  intros A l H. destruct l; auto.
  inversion H.
Qed.

Lemma sublist_cons1' :
  forall (A : Set) (e : A) (l l' : list A),
  sublist (e :: l) l' ->
  sublist l l'.
Proof.
  intros A e l l'. generalize dependent l. generalize dependent e.
  induction l' as [| e' l' IH]; intros e l H.
  - inversion H.
  - inversion H; subst; clear H.
    + apply IH in H2. apply sublist_cons1, H2.
    + apply sublist_cons1, H1.
Qed.

Lemma sublist_trans :
  forall (A : Set) (l1 l2 l3 : list A),
  sublist l1 l2 ->
  sublist l2 l3 ->
  sublist l1 l3.
Proof.
  intros A l1 l2 l3 H1 H3. generalize dependent l1. induction H3; intros l1 H1.
  - apply sublist_nil' in H1. subst. apply sublist_nil.
  - apply sublist_cons1, IHsublist, H1.
  - inversion H1; subst; clear H1.
    + apply sublist_nil.
    + apply sublist_cons1, IHsublist, H2.
    + apply sublist_cons2, IHsublist, H2.
Qed.

Lemma sublist_extra :
  forall (A : Set) (l1 l : list A),
  sublist l1 l ->
  exists l0, Permutation (l0 ++ l1) l.
Proof.
  intros A l1 l H. induction H.
  - exists l. rewrite app_nil_r. reflexivity.
  - destruct IHsublist as [l0 IH]. exists (x :: l0).
    simpl. apply perm_skip, IH.
  - destruct IHsublist as [l0 IH]. exists l0.
    transitivity (x :: l0 ++ l).
    + replace (x :: l) with ([x] ++ l) by reflexivity.
      rewrite app_comm_cons, app_assoc.
      apply Permutation_app_tail, Permutation_sym, Permutation_cons_append.
    + apply perm_skip, IH.
Qed.

(* TODO reorganize lemmas *)
Lemma sublist_app1 :
  forall (A : Set) (l l' : list A),
  sublist l' (l ++ l').
Proof.
  intros A l l'. induction l; simpl.
  - apply sublist_refl.
  - apply sublist_cons1, IHl.
Qed.

Lemma sublist_app :
  forall (A : Set) (l0 l1 l0' l1' : list A),
  sublist l0 l0' ->
  sublist l1 l1' ->
  sublist (l0 ++ l1) (l0' ++ l1').
Proof.
  intros A l0 l1 l0' l1' H0 H1. induction H0; simpl.
  - eapply sublist_trans; eauto.
    apply sublist_app1.
  - apply sublist_cons1, IHsublist.
  - apply sublist_cons2, IHsublist.
Qed.

Lemma sublist_map :
  forall (A B : Set) (l l' : list A) (f : A -> B),
  sublist l l' ->
  sublist (map f l) (map f l').
Proof.
  intros A B l l' f H. induction H; simpl.
  - apply sublist_nil.
  - apply sublist_cons1, IHsublist.
  - apply sublist_cons2, IHsublist.
Qed.

Lemma sublist_subset :
  forall A l l',
  sublist l l' ->
  forall e : A, In e l -> In e l'.
Proof.
  intros A l l' H. induction H; intros e Hl; simpls; auto_false.
  branches; auto.
Qed.

Lemma sublist_singleton_in :
  forall (A : Set) (e : A) l,
  sublist [e] l <-> In e l.
Proof.
  intros A e l. split; intros H.
  - eapply sublist_subset; eauto.
    left. reflexivity.
  - induction H using In_ind; auto using sublist.
Qed.

Lemma permutation_sublist :
  forall (A : Set) (l l' l2' : list A),
  Permutation l l' ->
  sublist l' l2' ->
  exists l2, sublist l l2 /\ Permutation l2 l2'.
Proof.
  intros A l l' l2' Hp Hs. specialize (sublist_extra Hs) as [l2 He].
  exists (l2 ++ l). split.
  - apply sublist_app1.
  - eapply perm_trans.
    + apply Permutation_app_head, Hp.
    + apply He.
Qed.

Section Eqb.

  Variable A : Set.
  Variable eqb : has_eqb A.
  Hypothesis H : valid_eqb eqb.

  Lemma inb_spec :
    forall l e,
    inb e l = true <-> In e l.
  Proof.
    intros l e.
    induction l as [| e' l IH]; simpl; autorewrite with bool;
    try rewrite IH; auto_false.
    rewrite rewrite_eqb by apply H.
    split; intros []; subst; auto.
  Qed.

  Lemma existsb_inb :
    forall l e,
    existsb (eqb e) l = inb e l.
  Proof.
    intros l e. induction l as [| e' l IH]; simpl; auto.
    rewrite IH. reflexivity.
  Qed.

  Lemma dupb_spec :
    forall l,
    dupb l = false <-> NoDup l.
  Proof.
    intros l. split.
    - induction l as [| e l IH]; simpl; autorewrite with bool; intros Hf;
      constructor; unpack; auto.
      intros Hc. rewrite <- inb_spec in Hc; eauto.
      congruence.
    - intros Hn. induction Hn; simpl; auto.
      rewrite IHHn. rewrite orb_false_r. apply not_true_is_false. intros Hc.
      apply inb_spec in Hc; auto.
  Qed.

  Lemma dupb_true :
    forall l,
    dupb l = true -> NoDup l -> False.
  Proof.
    intros l Ht Hn. rewrite <- dupb_spec in Hn; eauto.
    congruence.
  Qed.

  Lemma in_nodupb :
    forall (l : list A) e,
    In e (nodupb l) <-> In e l.
  Proof.
    intros l e.
    induction l as [| e0 l IH]; simpl; split; intros Hi; try contradiction.
    - destruct (inb e0 l).
      + right. apply IH, Hi.
      + destruct Hi; subst; auto.
        right. apply IH, H0.
    - destruct (inb e0 l) eqn:E, Hi; subst; simpl; rewrite IH; auto.
      apply inb_spec, E.
  Qed.

  Lemma nodupb_nodup :
    forall (l : list A),
    NoDup (nodupb l).
  Proof.
    intros l. induction l as [| e l IH]; simpl.
    - constructor.
    - destruct (inb e l) eqn:E; auto.
      constructor; auto.
      intros Hc. rewrite in_nodupb in Hc by assumption.
      rewrite <- inb_spec in Hc by apply H. congruence.
  Qed.

  Lemma nodupb_unchanged :
    forall (l : list A), NoDup l -> nodupb l = l.
  Proof.
    intros l Hn. induction Hn; simpl; auto.
    rewrite IHHn. destruct (inb x l) eqn:Ei; auto.
    exfalso. apply H0, inb_spec, Ei.
  Qed.

  #[export]
  Instance eqb_list_valid :
    valid_eqb (eqb_list (A:=A)).
  Proof.
    split.
    - intros l. induction l as [| e l IH].
      + reflexivity.
      + cbn. rewrite IH, eqb_refl. reflexivity.
    - intros l. induction l as [| e l IH]; intros [| e' l']; auto_false.
      cbn. rewrite andb_true_iff. intros [He Hl]. apply H in He. apply IH in Hl.
      congruence.
  Qed.

End Eqb.

Lemma NoDup_app :
  forall A (l l' : list A),
  NoDup (l ++ l') <->
  (forall e, In e l -> In e l' -> False) /\ NoDup l /\ NoDup l'.
Proof.
  intros A l l'. split.
  - intros H. induction l; simpls; auto using NoDup.
    apply NoDup_cons_iff in H as [Hn H]. apply IHl in H as [Hi [Hl H']].
    rewrite in_app_iff in Hn. apply Decidable.not_or_iff in Hn as [Hn Hn'].
    splits; auto using NoDup.
    intros e [He | He]; subst; auto.
    apply Hi, He.
  - intros. unpack. induction H0; simpl; auto.
    constructor.
    + intros Hc. apply in_app_iff in Hc as [Hc | Hc]; auto_false.
      apply H in Hc; simpl; auto.
    + apply IHNoDup. intros. eapply H; simpl; eauto.
Qed.

Lemma NoDup_list_prod :
  forall A0 A1 (l0 : list A0) (l1 : list A1),
  NoDup l0 ->
  NoDup l1 ->
  NoDup (list_prod l0 l1).
Proof.
  intros A0 A1 l0 l1 H0 H1.
  induction H0 as [| e l0 Hn H0 IH]; simpl; auto using NoDup.
  apply NoDup_app. splits.
  - intros [e0 e1] Hi Hp.
    apply in_map_iff in Hi as [e1' [He Hi]]. injection He as. subst.
    apply in_prod_iff in Hp as [Hp0 Hp1]. contradiction.
  - apply FinFun.Injective_map_NoDup; auto.
    intros e1 e1' He. injection He as. assumption.
  - assumption.
Qed.

Lemma filter_sublist :
  forall (A : Set) (l : list A) f,
  sublist (filter f l) l.
Proof.
  intros A l f. induction l as [| e l IH]; simpl.
  - apply sublist_nil.
  - destruct (f e).
    + apply sublist_cons2, IH.
    + apply sublist_cons1, IH.
Qed.

Lemma flat_map_map :
  forall A B C (f : A -> B) (g : B -> list C) l,
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof.
  intros A B C f g l. induction l; simpl; f_equal.
  assumption.
Qed.

Lemma flat_map_flat_map :
  forall A B C (f : A -> list B) (g : B -> list C) l,
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof.
  intros A B C f g l. induction l; simpl; try rewrite flat_map_app; f_equal.
  assumption.
Qed.

Lemma flat_map_app_perm :
  forall A B (f g : A -> list B) l,
  Permutation (flat_map f l ++ flat_map g l) (flat_map (fun e => f e ++ g e) l).
Proof.
  intros A B f g l. induction l as [| a l IH]; simpl; auto.
  repeat rewrite <- app_assoc. apply Permutation_app_head.
  rewrite Permutation_app_comm, <- app_assoc. apply Permutation_app_head.
  rewrite Permutation_app_comm. assumption.
Qed.

Lemma flat_map_nil :
  forall A B (l : list A),
  flat_map (fun _ => [] : list B) l = [].
Proof.
  intros A B l. induction l as [| e l IH]; auto.
Qed.

Lemma flat_map_NoDup :
  forall A B (f : A -> list B) l,
  NoDup l ->
  (forall a, In a l -> NoDup (f a)) ->
  (forall a a' b, In a l -> In a' l -> In b (f a) -> In b (f a') -> a = a') ->
  NoDup (flat_map f l).
Proof.
  intros A B f l Hd Hn He. induction l as [| a l IH]; simpls; auto using NoDup.
  inversion_clear Hd. apply NoDup_app. splits; auto.
  - intros b Ha Hl. apply in_flat_map in Hl as [a' [Hl H']].
    apply He with (a:=a) in H'; simpl; auto.
    subst. contradiction.
  - apply IH; auto.
    intros a1 a2 b H1 H2. apply He; auto.
Qed.

Lemma map_maybe_inv :
  forall A B (f : A -> option B) (g : B -> A) l l',
  (forall a b, f a = Some b -> g b = a) ->
  map_maybe f l = Some l' ->
  map g l' = l.
Proof.
  intros A B f g l. induction l as [| a l IH]; simpl; intros l' H Hl.
  - injection Hl as. subst. reflexivity.
  - destruct (f a) eqn:Ea, (map_maybe f l) eqn:Em; auto_false.
    injection Hl as. subst. simpl. f_equal; auto.
Qed.

Lemma map_maybe_exists :
  forall A B (f : A -> option B) l l' b,
  map_maybe f l = Some l' ->
  In b l' ->
  exists a, In a l /\ f a = Some b.
Proof.
  intros A B f l. induction l as [| a l IH]; simpl; intros l' b H Hi.
  - injection H as. subst. contradiction.
  - destruct (f a) eqn:Ea, (map_maybe f l) eqn:El; auto_false.
    injection H as. subst. destruct Hi.
    + subst. exists a. auto.
    + destruct (IH l0 b eq_refl H) as [a' [Hi Hs]].
      exists a'. auto.
Qed.

Lemma flat_map_map_maybe :
  forall A B (f : A -> option (list B)) l,
  flat_map_maybe f l = match map_maybe (fun a => match f a with
                                                 | None => None
                                                 | Some b => Some (a, b)
                                                 end) l with
                       | None => None
                       | Some l' => Some (flat_map snd l')
                       end.
Proof.
  intros A B f l. induction l as [| a l IH]; auto.
  simpl. destruct (f a) eqn:Ea; auto.
  destruct (flat_map_maybe f l) eqn:Ef, (map_maybe _ l) eqn:Em; auto_false.
  simpl. congruence.
Qed.

Lemma flat_map_maybe_Some :
  forall A B (f : A -> option (list B)) l l',
  flat_map_maybe f l = Some l' ->
  forall a, In a l -> exists b, f a = Some b.
Proof.
  intros A B f l.
  induction l as [| a0 l IH]; simpl; intros l' He a Hi; auto_false.
  destruct (f a0) eqn:Ea, (flat_map_maybe f l) eqn:El; auto_false.
  injection He as. subst. destruct Hi; subst; eauto.
Qed.

Lemma NoDup_fst :                                                           
  forall A B (l : list (A * B)) a b b',
  NoDup (map fst l) ->
  In (a, b) l ->
  In (a, b') l ->
  b = b'.
Proof.
  intros A B l. induction l as [| [a0 b0] l IH]; auto_false.
  simpl. intros a b b' Hn H H'. inversion_clear Hn.
  destruct H as [H | H], H' as [H' | H']; eauto.
  - congruence.
  - exfalso. injection H as. subst. apply H0, in_map_iff. exists (a, b'). auto.
  - exfalso. injection H' as. subst. apply H0, in_map_iff. exists (a, b). auto.
Qed.

Lemma forallb_eqb_repeat :
  forall A (eqb : has_eqb A) e l,
  valid_eqb eqb ->
  forallb (eqb e) l = true <-> l = repeat e (length l).
Proof.
  intros A eqb e l Hv. split.
  - induction l as [| e' l IH]; intros H; auto.
    simpls. autorewrite with bool in H. unpack. f_equal.
    + symmetry. apply eqb_sound, H.
    + apply IH, H0.
  - induction l as [| e' l IH]; intros H; auto.
    simpls. injection H as. subst. destruct Hv.
    rewrite eqb_refl, IH by assumption. reflexivity.
Qed.

Lemma map_fst_combine :
  forall A0 A1 (l0 : list A0) (l1 : list A1),
  length l0 = length l1 ->
  map fst (combine l0 l1) = l0.
Proof.
  intros A0 A1 l0. induction l0 as [| e0 l0 IH]; intros [] H; auto_false.
  simpls. f_equal. apply IH. injection H as. assumption.
Qed.

Lemma map_snd_combine :
  forall A0 A1 (l0 : list A0) (l1 : list A1),
  length l0 = length l1 ->
  map snd (combine l0 l1) = l1.
Proof.
  intros A0 A1 l0. induction l0 as [| e0 l0 IH]; intros [] H; auto_false.
  simpls. f_equal. apply IH. injection H as. assumption.
Qed.

Lemma split_map_fst :
  forall A B l (l0 : list A) (l1 : list B),
  split l = (l0, l1) -> l0 = map fst l.
Proof.
  intros A B l.
  induction l as [| [a b] l IH]; intros [| a0 l0] [| b0 l1] H;
  simpls; auto_false; destruct (split l); auto_false.
  injection H as. subst. f_equal. eapply IH. reflexivity.
Qed.

Lemma split_map_snd :
  forall A B l (l0 : list A) (l1 : list B),
  split l = (l0, l1) -> l1 = map snd l.
Proof.
  intros A B l.
  induction l as [| [a b] l IH]; intros [| a0 l0] [| b0 l1] H;
  simpls; auto_false; destruct (split l); auto_false.
  injection H as. subst. f_equal. eapply IH. reflexivity.
Qed.

Lemma fst_split :
  forall A B (l : list (A * B)),
  fst (split l) = map fst l.
Proof.
  intros A B l. induction l as [| [a b] l IH]; auto.
  simpl. destruct (split l). simpls. congruence.
Qed.
  
Lemma snd_split :
  forall A B (l : list (A * B)),
  snd (split l) = map snd l.
Proof.
  intros A B l. induction l as [| [a b] l IH]; auto.
  simpl. destruct (split l). simpls. congruence.
Qed.
