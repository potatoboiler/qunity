From Coq Require Import Bool String Morphisms Basics.
From Qunity Require Import Tactics Syntax Types Sets Lists.
Import ListNotations.
Import Tactics (eqb_refl).

Set Implicit Arguments.

Declare Scope ctx_scope.
Open Scope list_scope.
Open Scope qunity_scope.
Open Scope ctx_scope.

(* A context is a list of bindings from variables to types *)
Definition context : Set := list (string * type).

Definition dom (g : context) : set := map fst g.

(* A well-formed context contains no duplicate variables *)
Definition well_formed (g : context) := NoDup (dom g).

Fixpoint context_find (g : context) x :=
  match g with
  | [] => None
  | (x', t) :: g' => if x =? x' then Some t else context_find g' x
  end.

(* Contexts can be used like applied functions *)
Coercion context_find : context >-> Funclass.

Definition restriction (g : context) (s : set) : context :=
  filter (fun '(x, t) => mem x s) g.

Definition well_formed_check g : bool :=
  negb (dupb (dom g)).

(* Merges two contexts, removes duplicates, fails on conflict *)
Definition merge (d0 d1 : context) : option context :=
  if well_formed_check d0 && well_formed_check d1
  then
    let d := nodupb (d0 ++ d1) in if well_formed_check d then Some d else None
  else None.

(* Fails if ill-formed, otherwise removes and returns the binding for x *)
Fixpoint remove x (g : context) : option (option type * context) :=
  match g with
  | [] => Some (None, [])
  | (x0, t0) :: g1 =>
      match remove x g1, x =? x0 with
      | None, _ | Some (Some _, _), true =>
          None
      | Some (t1, g2), false =>
          match (g1 : context) x0 with
          | None => Some (t1, (x0, t0) :: g2)
          | Some _ => None
          end
      | Some (None, g2), true =>
          Some (Some t0, g2)
      end
  end.

#[export]
Instance eqb_option A `(has_eqb A) : has_eqb (option A) :=
  fun o o' =>
  match o, o' with
  | None, None => true
  | Some e, Some e' => e =? e'
  | _, _ => false
  end.

(* remove everything in g from d, fails on mismatch *)
Fixpoint remove_all (g d : context) : option context :=
  match g with
  | [] =>
      if well_formed_check d then Some d else None
  | (x0, t0) :: g1 =>
      if (g1 : context) x0 =? None
      then match remove x0 d with
           | None => None
           | Some (None, _) => remove_all g1 d
           | Some (Some t1, d1) => if t0 =? t1 then remove_all g1 d1 else None
           end
      else None
  end.

(* Using a context as a product type *)
Fixpoint ctx2type (d : context) :=
  match d with
  | [] => qunit
  | (_, t) :: d' => t * ctx2type d'
  end.

Definition inclusionb (g g' : context) : bool :=
  well_formed_check g &&
  well_formed_check g' &&
  forallb (fun x => g x =? g' x) (dom g).

(* Is g a subset of g'? *)
Definition subcontext (g g' : context) : Prop :=
  forall x t, g x = Some t -> g' x = Some t.

Infix "<=" := subcontext : ctx_scope.

Definition equivb (d d' : context) : bool :=
  inclusionb d d' && inclusionb d' d.

Definition Equiv_context (d d' : context) : Prop :=
  forall x t, d x = Some t <-> d' x = Some t.

Definition no_conflict (g g' : context) : Prop :=
  forall x t t', g x = Some t -> g' x = Some t' -> t = t'.

Lemma dom_union :
  forall g g', dom (g ++ g') = dom g ++ dom g'.
Proof.
  intros g g'. induction g as [| [x t] g]; simpl; auto.
  f_equal. assumption.
Qed.

Lemma dom_nil :
  forall d, dom d = [] -> d = [].
Proof.
  intros d H. destruct d; auto_false.
Qed.

Lemma context_find_inv :
  forall (g : context) x t,
  g x = Some t ->
  exists g0 g1, g = g0 ++ (x, t) :: g1.
Proof.
  intros g x t H. induction g as [| [x' t'] g IH]; try discriminate.
  simpls. destruct (x =? x') eqn:E.
  - apply eqb_sound in E. injection H as. subst.
    exists ([] : context) g. reflexivity.
  - apply IH in H as [g0 [g1 H]]. subst.
    exists ((x', t') :: g0) g1. reflexivity.
Qed.

Lemma context_find_inv_cons :
  forall (g : context) x t,
  g x = Some t ->
  exists g', Permutation g ((x, t) :: g').
Proof.
  intros g x t H. apply context_find_inv in H as [g0 [g1 H]]. subst.
  exists (g0 ++ g1). symmetry. apply Permutation_middle.
Qed.

Lemma well_formed_app :
  forall g g',
  well_formed (g ++ g') <->
  disjoint (dom g) (dom g') /\ well_formed g /\ well_formed g'.
Proof.
  intros g g'. unfold well_formed, dom. rewrite map_app, NoDup_app. reflexivity.
Qed.

#[export]
Instance dom_proper :
  Proper (Permutation (A:=string * type) ==> Permutation (A:=string)) dom.
Proof.
  intros g g' H. apply Permutation_map, H.
Qed.

#[export]
Instance well_formed_perm :
  Proper (Permutation (A:=string*type) ==> impl) well_formed.
Proof.
  intros g g' Hp H. unfold well_formed in *. rewrite Hp in H. apply H.
Qed.

Lemma context_find_None :
  forall (d : context) x, d x = None <-> ~ In x (dom d).
Proof.
  intros d. induction d as [| [x0 t] d IH]; simpl; intros x; split; auto.
  - intros H [He | Hi].
    + subst. rewrite eqb_refl in H. discriminate.
    + destruct (x =? x0); auto_false.
      apply IH in H. contradiction.
  - intros H. destruct (x =? x0) eqn:E.
    + apply eqb_sound in E. subst. tauto.
    + apply IH. tauto.
Qed.

Lemma well_formed_hd :
  forall x t (d : context), well_formed ((x, t) :: d) -> d x = None.
Proof.
  unfold well_formed. simpl. intros x t d H.
  inversion H. apply context_find_None, H2.
Qed.

Lemma well_formed_tl :
  forall x t (d : context), well_formed ((x, t) :: d) -> well_formed d.
Proof.
  unfold well_formed. simpl. intros x t d H. inversion H. assumption.
Qed.

Lemma well_formed_cons :
  forall x t (g : context),
  well_formed ((x, t) :: g) <-> g x = None /\ well_formed g.
Proof.
  intros x t g. split; eauto using well_formed_hd, well_formed_tl.
  unfold well_formed. simpl. intros [Hx Hg]. constructor; auto.
  apply context_find_None, Hx.
Qed.

Lemma well_formed_ind :
  forall P : context -> Prop,
  P [] ->
  (forall x t (d : context),
   d x = None -> well_formed d -> P d -> P ((x, t) :: d)) ->
  forall d, well_formed d -> P d.
Proof.
  intros P H0 Hs d. induction d as [| [x t] d IH]; auto.
  intros H. apply well_formed_tl in H as Hd. apply Hs; auto.
  apply well_formed_hd in H. assumption.
Qed.

Lemma well_formed_check_sound :
  forall d,
  well_formed_check d = true ->
  well_formed d.
Proof.
  unfold well_formed_check, well_formed. intros d H. apply negb_true_iff in H.
  apply dupb_spec in H; auto using eqb_string_valid.
Qed.

Lemma well_formed_check_complete :
  forall d,
  well_formed d ->
  well_formed_check d = true.
Proof.
  intros d H. unfold well_formed_check. apply negb_true_iff.
  induction H using well_formed_ind; simpl; auto.
  rewrite IHwell_formed. rewrite orb_false_r.
  apply not_true_is_false. intros Hc.
  apply inb_spec in Hc; auto using eqb_string_valid.
  apply context_find_None in H. contradiction.
Qed.

Lemma well_formed_check_iff :
  forall d,
  well_formed_check d = true <-> well_formed d.
Proof.
  split; auto using well_formed_check_sound, well_formed_check_complete.
Qed.

Lemma context_find_Some_In :
  forall (d : context) x t,
  well_formed d ->
  d x = Some t <-> In (x, t) d.
Proof.
  intros d x t Hw. induction Hw using well_formed_ind; simpl; split; auto_false.
  - intros Ht. destruct (x =? x0) eqn:Ex.
    + left. apply eqb_sound in Ex. congruence.
    + right. apply IHHw, Ht.
  - intros [He | Hi].
    + injection He as. subst. rewrite eqb_refl. reflexivity.
    + apply IHHw in Hi. rewrite Hi.
      destruct (x =? x0) eqn:Ex; auto.
      apply eqb_sound in Ex. congruence.
Qed.

Lemma context_find_nodupb :
  forall d x, well_formed d -> (nodupb d : context) x = d x.
Proof.
  intros d x H. induction H using well_formed_ind; simpl; auto.
  destruct (inb (x0, t) d) eqn:Ei.
  - rewrite IHwell_formed. destruct (x =? x0) eqn:E; auto.
    rewrite context_find_Some_In by assumption.
    apply eqb_sound in E. subst.
    rewrite <- inb_spec; eauto with eqb_db.
  - simpl. destruct (x =? x0); auto.
Qed.

Lemma nodupb_context_find_None :
  forall (d : context) x,
  d x = None <-> (nodupb d : context) x = None.
Proof.
  intros d x. induction d as [| [x0 t] d IH]; simpl; try tauto.
  destruct (x =? x0) eqn:Ex.
  - apply eqb_sound in Ex. subst. split; auto_false.
    intros H. exfalso. destruct (inb (x0, t) d) eqn:Ei.
    + apply IH in H.
      apply inb_spec in Ei; auto with eqb_db.
      apply context_find_None in H. apply H.
      unfold dom. apply in_map_iff. exists (x0, t). split; auto.
    + simpls. rewrite eqb_refl in H. discriminate.
  - destruct (inb (x0, t) d); simpl; try rewrite Ex; assumption.
Qed.

Lemma merge_spec :
  forall d0 d1 d,
  merge d0 d1 = Some d <->
  d = nodupb (d0 ++ d1) /\ well_formed d /\ well_formed d0 /\ well_formed d1.
Proof.
  intros d0 d1 d. split.
  - unfold merge. intros H.
    destruct (well_formed_check d0) eqn:E0, (well_formed_check d1) eqn:E1;
    auto_false.
    destruct (well_formed_check (nodupb (d0 ++ d1))) eqn:E; auto_false.
    apply well_formed_check_sound in E0, E1, E. injection H as. subst.
    auto.
  - intros [Hd [H [H0 H1]]]. subst. unfold merge.
    apply well_formed_check_complete in H, H0, H1. rewrite H, H0, H1.
    reflexivity.
Qed.

Lemma merge_none :
  forall d0 d1 d,
  merge d0 d1 = Some d ->
  forall x, d x = None <-> d0 x = None /\ d1 x = None.
Proof.
  intros d0 d1 d. rewrite merge_spec. intros [Hd [Hw [H0 H1]]]. subst.
  generalize dependent d1.
  induction d0 as [| [x0 t0] d0 IH]; simpl; intros d1 Hw H1 x.
  - rewrite <- nodupb_context_find_None. tauto.
  - apply well_formed_tl in H0. destruct (inb (x0, t0) (d0 ++ d1)) eqn:Ei; simpl; destruct (x =? x0) eqn:Ex.
    + apply eqb_sound in Ex. subst.
      apply inb_spec in Ei; auto with eqb_db.
      split; intros Hc; exfalso.
      * apply nodupb_context_find_None in Hc. apply context_find_None in Hc.
        apply Hc. unfold dom. apply in_map_iff. exists (x0, t0). auto.
      * unpack. discriminate.
    + apply IH; auto.
    + split; intros; unpack; discriminate.
    + apply well_formed_tl in Hw. apply IH; auto.
Qed.

Lemma merge_some :
  forall d0 d1 d,
  merge d0 d1 = Some d ->
  forall x t, d x = Some t <-> d0 x = Some t \/ d1 x = Some t.
Proof.
  intros d0 d1 d. rewrite merge_spec. intros [Hd [Hw [H0 H1]]] x t. subst.
  repeat rewrite context_find_Some_In by assumption.
  rewrite in_nodupb; auto with eqb_db.
  rewrite in_app_iff. reflexivity.
Qed.

Lemma mergeable_same :
  forall d0 d1 d, merge d0 d1 = Some d ->
  forall x t0 t1, d0 x = Some t0 -> d1 x = Some t1 -> t0 = t1.
Proof.
  intros d0 d1 d H x t0 t1 H0 H1.
  destruct (merge_some _ _ H x t0) as [_ H0'].
  destruct (merge_some _ _ H x t1) as [_ H1'].
  rewrite H0' in H1'; auto.
  injection H1'; auto.
Qed.

Lemma merge_perm :
  forall d0 d1 d,
  merge d0 d1 = Some d ->
  exists d' d0' d1',
  Permutation (d' ++ d0' ++ d1') d /\
  Permutation (d' ++ d0') d0 /\
  Permutation (d' ++ d1') d1.
Proof.
  intros d0 d1 d Hm. specialize (mergeable_same _ _ Hm) as Hs.
  apply merge_spec in Hm as [Hd [Hw [H0 H1]]].
  set (d' := filter (fun '(x, _) => mem x (dom d0) && mem x (dom d1)) d).
  set (d0' := filter (fun '(x, _) => negb (mem x (dom d1))) d0).
  set (d1' := filter (fun '(x, _) => negb (mem x (dom d0))) d1).
  exists d' d0' d1'.
  assert (NoDup d) as Hn. { apply NoDup_map_inv in Hw. assumption. }
  assert (NoDup d0) as Hn0. { apply NoDup_map_inv in H0. assumption. }
  assert (NoDup d1) as Hn1. { apply NoDup_map_inv in H1. assumption. }
  assert (NoDup d') as H'. { apply NoDup_filter. assumption. }
  assert (NoDup d0') as H0'. { apply NoDup_filter. assumption. }
  assert (NoDup d1') as H1'. { apply NoDup_filter. assumption. }
  splits; apply NoDup_Permutation; auto.
  - repeat rewrite NoDup_app. splits; auto.
    + intros [x t] Hi Hi'. apply in_app_iff in Hi'.
      subst d' d0' d1'. repeat rewrite filter_In in *.
      autorewrite with bool in Hi. unpack.
      repeat rewrite negb_true_iff, <- not_true_iff_false, mem_spec in Hi'.
      tauto.
    + intros [x t] Hi0 Hi1. subst d0' d1'. rewrite filter_In in *. unpack.
      repeat rewrite negb_true_iff, <- not_true_iff_false, mem_spec in *.
      apply H4. unfold dom. apply in_map_iff. exists (x, t). auto.
  - intros [x t]. subst. subst d' d0' d1'.
    repeat rewrite in_app_iff. repeat rewrite filter_In.
    autorewrite with bool. rewrite in_nodupb; auto with eqb_db.
    repeat rewrite in_app_iff.
    split; intros; branches; unpack; auto.
    + destruct (mem x (dom d1)) eqn:E; auto.
      left. apply mem_spec in E. splits; auto.
      apply in_map_iff. exists (x, t). auto.
    + destruct (mem x (dom d0)) eqn:E; auto.
      left. apply mem_spec in E. splits; auto.
      apply in_map_iff. exists (x, t). auto.
  - apply NoDup_app. splits; auto.
    intros [x t] Hi Hi'. subst d' d0'. rewrite filter_In in *.
    autorewrite with bool in Hi. unpack.
    rewrite negb_true_iff, <- not_true_iff_false, mem_spec in H2. contradiction.
  - intros [x t]. rewrite in_app_iff. subst. subst d' d0'.
    repeat rewrite filter_In. autorewrite with bool.
    rewrite in_nodupb by auto with eqb_db. rewrite in_app_iff.
    split; intros; try branches; unpack; try branches; auto.
    + unfold dom in H2. apply in_map_iff in H2 as [[x' t'] [Hx Hi]].
      simpls. subst. rewrite <- context_find_Some_In in * by assumption.
      specialize (Hs _ _ _ Hi H). subst. assumption.
    + destruct (mem x (dom d1)) eqn:E; auto.
      left. apply mem_spec in E. splits; auto.
      apply in_map_iff. exists (x, t). auto.
  - apply NoDup_app. splits; auto.
    intros [x t] Hi Hi'. subst d' d1'. rewrite filter_In in *.
    autorewrite with bool in Hi. unpack.
    rewrite negb_true_iff, <- not_true_iff_false, mem_spec in H2. contradiction.
  - intros [x t]. rewrite in_app_iff. subst. subst d' d1'.
    repeat rewrite filter_In. autorewrite with bool.
    rewrite in_nodupb by auto with eqb_db. rewrite in_app_iff.
    split; intros; try branches; unpack; try branches; auto.
    + unfold dom in H3. apply in_map_iff in H3 as [[x' t'] [Hx Hi]].
      simpls. subst. rewrite <- context_find_Some_In in * by assumption.
      specialize (Hs _ _ _ H Hi). subst. assumption.
    + destruct (mem x (dom d0)) eqn:E; auto.
      left. apply mem_spec in E. splits; auto.
      apply in_map_iff. exists (x, t). auto.
Qed.

Lemma remove_Some :
  forall x g t g', remove x g = Some (t, g') -> g x = t.
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; simpl.
  - congruence.
  - intros t g' H.
    destruct (remove x g) as [[[t1 |] g1] |] eqn:E, (x =? x0) eqn:Ex;
    auto_false; try (destruct ((g : context) x0); eapply IH); repeat f_equal;
    congruence.
Qed.

Lemma remove_inclusion :
  forall x g t g', remove x g = Some (t, g') ->
  forall x' t', g' x' = Some t' -> g x' = Some t'.
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; simpl; intros t g' H x' t' H'.
  - injection H as. subst. discriminate.
  - destruct (remove x g) as [[[t1 |] g1] |] eqn:E, (x =? x0) eqn:Ex;
    auto_false.
    + destruct (context_find g x0); auto_false.
      injection H as. subst. simpls.
      destruct (x' =? x0); eauto.
    + apply eqb_sound in Ex. injection H as. subst.
      destruct (x' =? x0) eqn:Ex; eauto.
      apply eqb_sound in Ex. subst. apply remove_Some in E.
      eapply IH in H'; repeat f_equal.
      congruence.
    + destruct (context_find g x0) eqn:Eg; auto_false.
      injection H as. subst. simpls.
      destruct (x' =? x0); eauto.
Qed.

Lemma remove_None :
  forall g x, well_formed g <-> remove x g <> None.
Proof.
  intros g x. split; intros H.
  - induction H using well_formed_ind; auto_false.
    simpl.
    destruct (remove x d) as [[[t1 |] g1] |] eqn:E, (x =? x0) eqn:Ex;
    auto_false; apply remove_Some in E as Hs.
    + apply eqb_sound in Ex. congruence.
    + destruct (d x0) eqn:Eg; auto_false.
    + destruct (d x0) eqn:E0; auto_false.
  - induction g as [| [x0 t0] g IH].
    + constructor.
    + apply well_formed_cons. simpls. split.
      * destruct (remove x g) as [[[t |] g'] |] eqn:Eg,
          (x =? x0) eqn:Ex, ((g : context) x0) eqn:E';
        auto_false.
        apply eqb_sound in Ex. subst. apply remove_Some in Eg. congruence.
      * apply IH. destruct (remove x g); auto_false.
Qed.

Lemma remove_find :
  forall x g t g', remove x g = Some (t, g') -> g' x = None.
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; simpl.
  - intros t g' H. injection H as. subst. reflexivity.
  - intros t g' H.
    destruct (remove x g) as [[[t1 |] g1] |],
        (x =? x0) eqn:Ex, (context_find g x0);
    auto_false; injection H as; subst; simpl.
    + erewrite Ex, IH; reflexivity.
    + eapply IH. reflexivity.
    + eapply IH. reflexivity.
    + rewrite Ex. eapply IH. reflexivity.
Qed.

Lemma remove_all_well_formed0 :
  forall g d' d, remove_all g d' = Some d -> well_formed g.
Proof.
  intros g. induction g as [| [x t] g IH]; simpl; intros d' d H.
  - constructor.
  - apply well_formed_cons. destruct (context_find g x) eqn:Ex; auto_false.
    destruct (remove x d') as [[[t' |] d2] |] eqn:Er; split; auto_false.
    + destruct (t =? t') eqn:Et; auto_false.
      simpls. eauto.
    + simpls. eauto.
Qed.

Lemma remove_all_well_formed1 :
  forall g d' d, remove_all g d' = Some d -> well_formed d.
Proof.
  intros g. induction g as [| [x t] g IH]; simpl; intros d' d H.
  - destruct (well_formed_check d') eqn:E; auto_false.
    apply well_formed_check_sound in E. injection H as. subst. assumption.
  - destruct (context_find g x) eqn:Ex; auto_false.
    destruct (remove x d') as [[[t1 |] d1] |] eqn:Er; auto_false.
    + destruct (t =? t1); auto_false.
      simpls. eauto.
    + simpls. eauto.
Qed.

Lemma context_find_app_None :
  forall (g0 g1 : context) x,
  context_find (g0 ++ g1) x = None <-> g0 x = None /\ g1 x = None.
Proof.
  intros g0 g1 x. split.
  - intros H. induction g0 as [| [x0 t0] g0 IH]; auto.
    simpls. destruct (x =? x0); auto_false.
  - intros [H0 H1]. induction g0 as [| [x0 t0] g0 IH]; auto.
    simpls. destruct (x =? x0); auto_false.
Qed.

Lemma context_find_app_Some :
  forall (g0 g1 : context) x t,
  context_find (g0 ++ g1) x = Some t ->
  g0 x = Some t \/ g1 x = Some t.
Proof.
  intros g0. induction g0 as [| [x0 t0] g0 IH]; auto.
  simpl. intros g1 x t H. destruct (x =? x0); auto.
Qed.

Lemma context_find_app_Some_iff :
  forall (g0 g1 : context) x t,
  well_formed (g0 ++ g1) ->
  context_find (g0 ++ g1) x = Some t <-> g0 x = Some t \/ g1 x = Some t.
Proof.
  intros g0 g1 x t H. apply well_formed_app in H as [Hd [H0 H1]].
  split; auto using context_find_app_Some.
  intros [H | H].
  - induction g0 as [| [x0 t0] g0 IH]; auto_false.
    simpls. apply well_formed_cons in H0 as [Hn H0]. 
    apply disjoint_cons0 in Hd as [].
    destruct (x =? x0); auto.
  - induction g0 as [| [x0 t0] g0 IH]; auto_false.
    simpls.
    apply disjoint_cons0 in Hd as []. apply well_formed_cons in H0 as [].
    destruct (x =? x0) eqn:Ex; auto.
    apply eqb_sound in Ex. subst. apply context_find_None in H2. congruence.
Qed.

Lemma remove_unchanged :
  forall x g g', remove x g = Some (None, g') -> g = g'.
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; simpl; intros g' H.
  - congruence.
  - destruct (remove x g) as [[[t1 |] g1] |] eqn:Er, (x =? x0) eqn:Ex;
    auto_false.
    + destruct (context_find g x0); auto_false.
    + destruct (context_find g x0); auto_false.
      injection H as. subst. f_equal. apply IH. reflexivity.
Qed.

Lemma remove_Permutation :
  forall x g t g',
  remove x g = Some (Some t, g') ->
  Permutation g ((x, t) :: g').
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; auto_false.
  simpl. intros t g' H.
  destruct (remove x g) as [[[t1 |] g1] |] eqn:Eg; auto_false.
  - destruct (x =? x0), (context_find g x0); auto_false.
    injection H as. subst. rewrite IH; eauto using perm_swap.
  - apply remove_unchanged in Eg.
    destruct (x =? x0) eqn:Ex, (context_find g x0); auto_false;
    apply eqb_sound in Ex; injection H as; subst; reflexivity.
Qed.

Lemma remove_all_inclusion :
  forall g d' d, remove_all g d' = Some d ->
  forall x' t', d x' = Some t' -> d' x' = Some t'.
Proof.
  intros g. induction g as [| [x0 t0] g IH]; simpl.
  - intros d' d H. destruct (well_formed_check d'); auto_false.
    injection H as. subst. auto.
  - intros d' d H. destruct (context_find g x0) eqn:Eg; simpls; auto_false.
    destruct (remove x0 d') as [[[t1 |] d1] |] eqn:Ed; simpls; auto_false.
    + destruct (t0 =? t1); auto_false.
      intros x t Hx. eapply remove_inclusion in Ed; eauto.
    + intros x t Hx. eapply remove_unchanged in Ed; eauto.
Qed.

Lemma remove_all_well_formed :
  forall g d' d, remove_all g d' = Some d -> well_formed (g ++ d).
Proof.
  intros g d' d H. apply well_formed_app.
  split; eauto using remove_all_well_formed0, remove_all_well_formed1.
  generalize dependent d. generalize dependent d'.
  induction g as [| [x t] g IH]; simpl; intros d' d H; auto using disjoint_nil0.
  symmetry. apply disjoint_cons1. split.
  - apply context_find_None. destruct (context_find g x) eqn:Eg; auto_false.
    destruct (remove x d') as [[[t1 |] d1] |] eqn:Er; simpls; auto_false.
    + destruct (t =? t1); auto_false.
      apply remove_find in Er.
      destruct (d x) eqn:Ed; auto.
      eapply remove_all_inclusion in Ed; eauto.
      congruence.
    + apply remove_find in Er as Hn. apply remove_unchanged in Er. subst.
      destruct (d x) eqn:Ed; auto.
      eapply remove_all_inclusion in Ed; eauto.
      congruence.
  - destruct (context_find g x), (remove x d') as [[[t1 |] d1] |];
    simpls; auto_false.
    + destruct (t =? t1); auto_false.
      apply IH in H. intros x' Hi H'. eapply H in H'. auto.
    + apply IH in H. intros x' Hi H'. eapply H in H'. auto.
Qed.

#[export]
Instance eqb_option_valid A (eqb : has_eqb A) :
  valid_eqb eqb ->
  valid_eqb (eqb_option eqb).
Proof.
  intros H. split.
  - intros [e |]; cbn.
    + apply H.
    + reflexivity.
  - intros [e |] [e' |]; auto_false.
    cbn. intros He. apply H in He. subst. reflexivity.
Qed.

Lemma remove_all_Permutation :
  forall g d' d, remove_all g d' = Some d ->
  exists g' : context, Permutation (g' ++ d') (g ++ d).
Proof.
  intros g. induction g as [| [x0 t0] g IH]; simpl; intros d' d H.
  - exists ([] : context). destruct (well_formed_check d'); auto_false.
    injection H as. subst. reflexivity.
  - destruct (context_find g x0) eqn:E0; auto_false.
    destruct (remove x0 d') as [[[t1 |] d1] |] eqn:E'; simpls; auto_false.
    + destruct (t0 =? t1) eqn:Et; auto_false.
      apply eqb_sound in Et. subst.
      apply IH in H as [g' H]. exists g'.
      apply remove_Permutation in E'. rewrite E'.
      rewrite <- Permutation_middle. apply perm_skip, H.
    + apply remove_unchanged in E'. subst.
      apply IH in H as [g' H]. exists ((x0, t0) :: g'). simpl.
      apply perm_skip, H.
Qed.

Lemma remove_all_Permutation2 :
  forall g d' d, remove_all g d' = Some d ->
  exists g0 g1 : context, Permutation g (g0 ++ g1) /\ Permutation d' (g0 ++ d).
Proof.
  intros g. induction g as [| [x0 t0] g IH]; simpl.
  - intros d' d H. exists ([] : context) ([] : context). simpl. split; auto.
    destruct (well_formed_check d'); auto_false.
    injection H as. subst. reflexivity.
  - intros d' d H. destruct (context_find g x0) eqn:Eg; auto_false.
    destruct (remove x0 d') as [[[t1 |] d1] |] eqn:Er; simpls; auto_false.
    + destruct (t0 =? t1) eqn:Et; auto_false.
      apply eqb_sound in Et. subst.
      apply remove_Permutation in Er. apply IH in H as [g0 [g1 [Hg Hd]]].
      exists ((x0, t1) :: g0) g1. simpl. rewrite <- Hd. auto.
    + apply remove_unchanged in Er. subst. apply IH in H as [g0 [g1 [Hg Hd]]].
      exists g0 ((x0, t0) :: g1). split; auto.
      rewrite Hg. apply Permutation_middle.
Qed.

#[export]
Instance dom_Proper :
  Proper (Permutation (A:=string*type) ==> Permutation (A:=string)) dom.
Proof.
  intros g g' Hg. apply Permutation_map, Hg.
Qed.

Lemma dom_nodupb_comm :
  forall g, nodupb (dom g) ~= dom (nodupb g).
Proof.
  intros g x. rewrite in_nodupb by auto with eqb_db.
  symmetry. induction g as [| [x0 t0] g IH]; try reflexivity.
  simpl.
  destruct (inb _ g) eqn:E; simpl; rewrite IH; split; intros; try branches;
  subst; auto.
  rewrite inb_spec in E by auto with eqb_db.
  apply in_map_iff. exists (x, t0). auto.
Qed.

Lemma subcontext_nil :
  forall g, [] <= g.
Proof.
  intros g x t H. discriminate.
Qed.

Lemma subcontext_nil_r :
  forall g, g <= [] -> g = [].
Proof.
  intros g H. destruct g as [| [x t] g]; auto.
  specialize (H x t). simpls. rewrite eqb_refl in H. discriminate (H eq_refl).
Qed.

Lemma dom_Some :
  forall g x, In x (dom g) <-> exists t, g x = Some t.
Proof.
  intros g x. split.
  - intros H. induction g as [| [x' t'] g IH]; auto_false.
    simpls. destruct (x =? x') eqn:Ex; eauto.
    apply IH. destruct H; auto.
    subst. rewrite eqb_refl in Ex. discriminate.
  - intros [t H]. induction g as [| [x' t'] g IH]; auto_false.
    simpls. destruct (x =? x') eqn:E; auto.
    left. symmetry. apply eqb_sound, E.
Qed.

Lemma inclusionb_subcontext :
  forall g g',
  inclusionb g g' = true <-> g <= g' /\ well_formed g /\ well_formed g'.
Proof.
  intros g g'. unfold inclusionb.
  autorewrite with bool. rewrite forallb_forall.
  split; intros H; unpack; splits;
  auto using well_formed_check_sound, well_formed_check_complete.
  - intros x t Hx. rewrite <- Hx. symmetry. apply eqb_sound.
    apply H1. apply dom_Some. eauto.
  - intros x Hx. apply dom_Some in Hx as [t Hx].
    rewrite Hx. apply H in Hx. rewrite Hx. apply eqb_refl.
Qed.

Lemma cons_subcontext :
  forall x t (g g' : context),
  g x = None ->
  (x, t) :: g <= g' <-> g' x = Some t /\ g <= g'.
Proof.
  intros x t g g' Hn. split.
  - intros H. split.
    + apply H. simpl. rewrite eqb_refl. reflexivity.
    + intros x' t' H'. apply H. simpl. destruct (x' =? x) eqn:Eq; auto.
      apply eqb_sound in Eq. subst. congruence.
  - intros [Hx Hg] x' t' H'. simpls. destruct (x' =? x) eqn:Eq; auto.
    apply eqb_sound in Eq. subst. congruence.
Qed.

Lemma well_formed_check_cons_None :
  forall x t (g : context),
  g x = None ->
  well_formed_check ((x, t) :: g) = well_formed_check g.
Proof.
  intros x t g H. unfold well_formed_check. simpl. rewrite negb_orb.
  destruct (negb (inb _ _)) eqn:E; auto.
  rewrite negb_false_iff, inb_spec in E; auto with eqb_db.
  apply dom_Some in E as [t' H']. congruence.
Qed.

Lemma remove_all_nil :
  forall g d, remove_all g [] = Some d -> d = [].
Proof.
  intros g. induction g as [| [x t] g IH]; simpl; intros d H.
  - congruence.
  - destruct (context_find g x); auto_false.
Qed.

Lemma remove_all_cons_None :
  forall (g d d' : context) x t,
  g x = None ->
  d x = None ->
  remove_all g d = Some d' ->
  remove_all g ((x, t) :: d) = Some ((x, t) :: d').
Proof.
  intros g. induction g as [| [x' t'] g IH]; simpl; intros d d' x t Hn Hd H.
  - destruct (well_formed_check d) eqn:Ew; auto_false.
    injection H as. subst.
    simpl.
    + rewrite well_formed_check_cons_None by assumption.
      rewrite Ew. reflexivity.
  - destruct (context_find g x' =? None) eqn:Eg; auto_false.
    destruct (x =? x') eqn:Ex; auto_false.
    rewrite valid_eqb_sym, Ex, Hd by auto with eqb_db.
    destruct (remove x' d) as [[[t1 |] d1] |] eqn:Er; simpls; auto_false.
    destruct (t' =? t1) eqn:Et; auto_false.
    apply eqb_sound in Et. subst. apply IH; auto.
    destruct (d1 x) eqn:Ed; auto.
    eapply remove_inclusion in Ed; eauto.
    congruence.
Qed.

#[export]
Instance subcontext_preorder : PreOrder subcontext.
Proof.
  split.
  - intros g x. auto.
  - intros g1 g2 g3 H1 H3 x t Hx. apply H3, H1, Hx.
Qed.

Lemma Permutation_subcontext :
  forall g g',
  Permutation g g' ->
  well_formed g ->
  g <= g'.
Proof.
  intros g g' H Hw. induction H.
  - apply subcontext_nil.
  - destruct x as [x t]. apply well_formed_cons in Hw as [Hn Hw].
    intros x' t' H'. simpls. destruct (x' =? x) eqn:E; auto.
    apply IHPermutation; auto.
  - destruct x as [x0 t0], y as [x1 t1]. intros x t H. simpls.
    repeat rewrite well_formed_cons in Hw. unpack.
    simpls. destruct (x1 =? x0) eqn:Eq; auto_false.
    destruct (x =? x0) eqn:E0, (x =? x1) eqn:E1; auto.
    apply eqb_sound in E0, E1. subst. rewrite eqb_refl in Eq. discriminate.
  - transitivity l'; auto.
    rewrite H in Hw. auto.
Qed.

Lemma remove_unchanged_except :
  forall x g t g',
  remove x g = Some (t, g') ->
  forall x', x <> x' -> g x' = g' x'.
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; simpl; intros.
  - injection H as. subst. reflexivity.
  - destruct (remove x g) as [[[t1 |] g1] |] eqn:Er; auto_false.
    + destruct (x =? x0); auto_false.
      destruct (context_find g x0) eqn:E0; auto_false.
      injection H as. subst. simpl.
      destruct (x' =? x0); auto. eapply IH; eauto.
    + apply remove_unchanged in Er. subst. destruct (x =? x0) eqn:Eq.
      * injection H as. subst. destruct (x' =? x0) eqn:E'; auto.
        apply eqb_sound in Eq, E'. congruence.
      * destruct (g1 x0) eqn:Eg; auto_false.
        injection H as. subst. simpl. reflexivity.
Qed.

Lemma remove_all_subcontext :
  forall g0 g1 g,
  g0 <= g ->
  remove_all g0 g = Some g1 ->
  Permutation (g0 ++ g1) g.
Proof.
  intros g0. induction g0 as [| [x0 t0] g0 IH]; simpl; intros g1 g Hs Hr.
  - destruct (well_formed_check g); auto_false.
    injection Hr as. subst. reflexivity.
  - destruct (context_find g0 x0) eqn:En; auto_false.
    simpls. destruct (remove x0 g) as [[[t' |] g'] |] eqn:E; simpls; auto_false.
    + destruct (t0 =? t') eqn:Et; auto_false.
      apply eqb_sound in Et. subst. apply remove_find in E as Hn.
      apply remove_Permutation in E as Hp. rewrite Hp.
      apply perm_skip, IH; auto.
      rewrite cons_subcontext in Hs by assumption. unpack.
      intros x t Hx.
      apply remove_unchanged_except with (x':=x) in E; try congruence.
      rewrite <- E. apply H0, Hx.
    + apply remove_unchanged in E as Hq. subst.
      rewrite cons_subcontext in Hs by assumption. unpack.
      apply remove_Some in E. congruence.
Qed.

Lemma remove_well_formed :
  forall x g t g', remove x g = Some (t, g') -> well_formed g'.
Proof.
  intros x g. induction g as [| [x0 t0] g IH]; simpl; intros t g' H; auto.
  - injection H as. subst. constructor.
  - destruct (remove x g) as [[[t1 |] g1] |] eqn:Er; auto_false.
    + destruct (x =? x0) eqn:Ex; auto_false.
      destruct (context_find g x0) eqn:Ef; auto_false.
      injection H as. subst. apply well_formed_cons. split; eauto.
      destruct (g1 x0) eqn:E1; auto.
      eapply remove_inclusion in Er; eauto.
      congruence.
    + apply remove_unchanged in Er. subst. destruct (x =? x0) eqn:Ex.
      * injection H as. subst. eauto.
      * destruct (context_find g1 x0) eqn:Ef; auto_false.
        injection H as. subst. apply well_formed_cons. split; eauto.
Qed.

(*
Lemma remove_all_well_formed_iff :
  forall g d,
  remove_all g d <> None <-> well_formed g /\ well_formed d.
Proof.
  intros g d. split.
  - intros H. destruct (remove_all g d) eqn:Er; auto_false.
    clear H. split; eauto using remove_all_well_formed0.
    generalize dependent c. generalize dependent d.
    induction g as [| [x t] g IH]; simpl; intros d d' H.
    + destruct (well_formed_check d) eqn:Ew; auto_false.
      injection H as. subst. apply well_formed_check_sound, Ew.
    + destruct (context_find g x); auto_false.
      simpls. destruct (remove x d) eqn:Er; auto_false.
      rewrite remove_None with (x:=x). intros Hc. congruence.
  - generalize dependent d.
    induction g as [| [x t] g IH]; intros d [Hg Hd] Hc; simpls.
    + rewrite well_formed_check_complete in Hc; auto_false.
    + apply well_formed_cons in Hg as [Hn Hg]. rewrite Hn in Hc. simpls.
      destruct (remove x d) as [[[t1 |] d1] |] eqn:Er.
      * destruct (t =? t1) eqn:Et; try apply IH in Hc; try split;
        remove_all
        eauto using remove_well_formed.

      rewrite Hd.
      destruct (remove x d) eqn:Ex; auto_false.
      congruence.
      Search remove well_formed.
      * injection H as.
    
    + apply remove_all_Permutation in Er. apply remove_all_well_formed in Er. Search Permutation remove_all. assumption.
    + apply
 *)

Lemma Permutation_context_find :
  forall (g g' : context) x t,
  well_formed g ->
  Permutation g ((x, t) :: g') ->
  g x = Some t.
Proof.
  intros g g' x t Hw Hp. apply context_find_Some_In; auto.
  rewrite Hp. left. reflexivity.
Qed.

Lemma subcontext_split :
  forall g0 g,
  well_formed g0 ->
  well_formed g ->
  g0 <= g ->
  exists g1, remove_all g0 g = Some g1 /\ Permutation (g0 ++ g1) g.
Proof.
  intros g0 g H0 Hg Hs. destruct (remove_all g0 g) as [g1 |] eqn:E.
  - exists g1. auto using remove_all_subcontext.
  - exfalso. generalize dependent g.
    induction H0 using well_formed_ind; simpl; intros g Hw Hs Hr.
    + apply well_formed_check_complete in Hw. rewrite Hw in Hr. discriminate.
    + rewrite cons_subcontext in Hs by assumption.
      rewrite H in Hr. unpack. simpls.
      destruct (remove x g) as [[[t1 |] g1] |] eqn:Er.
      * apply remove_Permutation in Er as Hp.
        apply Permutation_context_find in Hp; auto.
        rewrite Hp in H1.  injection H1 as. subst. rewrite eqb_refl in Hr.
        apply remove_well_formed in Er as Hf; auto.
        apply IHwell_formed in Hr as []; auto.
        intros x' t' H'. apply H2 in H' as Ht.
        apply remove_unchanged_except with (x':=x') in Er; congruence.
      * eauto.
      * apply remove_None in Er as []. assumption.
Qed.

#[export]
Instance no_conflict_refl : Reflexive no_conflict.
Proof.
  intros g x t t'. congruence.
Qed.

#[export]
Instance no_conflict_sym : Symmetric no_conflict.
Proof.
  intros g g' H x t t' Ht H'. symmetry. eapply H; eauto.
Qed.

Lemma subcontext_no_conflict :
  forall g g', g <= g' -> no_conflict g g'.
Proof.
  intros g g' H x t t' Ht H'.
  apply H in Ht. congruence.
Qed.

#[export]
Instance cons_subcontext_proper :
  Proper (eq ==> subcontext ==> subcontext) cons.
Proof.
  intros [x t] [x' t'] Hx g g' Hg. injection Hx as. subst.
  intros x t Hx. simpls. destruct (x =? x'); auto.
Qed.

Lemma subcontext_cons :
  forall (g : context) x t, g x = None -> g <= (x, t) :: g.
Proof.
  intros g x t Hn x' t' H'. simpl. destruct (x' =? x) eqn:Ex; auto.
  apply eqb_sound in Ex. congruence.
Qed.

Lemma restriction_subcontext :
  forall g X, well_formed g -> restriction g X <= g.
Proof.
  intros g. induction g as [| [x t] g IH]; simpl; try reflexivity.
  intros X Hw. apply well_formed_cons in Hw as []. destruct (mem x X) eqn:E.
  - rewrite IH by assumption. reflexivity.
  - rewrite IH by assumption. apply subcontext_cons, H.
Qed.
