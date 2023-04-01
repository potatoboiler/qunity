(* The main type inference algorithms are pure_type_check, mixed_type_check, and
 * prog_type_check. Theorems proving their soundness are toward the bottom of
 * this file. *)

From Coq Require Import Bool Basics String Permutation RelationClasses FunInd.
From Qunity Require Import
  Tactics Lists Sets Reals Types Syntax Contexts Typing.
Import Tactics (eqb, eqb_refl).
Import ListNotations QunityNotations.

Set Implicit Arguments.

Open Scope qunity_scope.

Function split_sum_list t0 t1 l : option (list expr * list expr) :=
  match l with
  | [] =>
      Some ([], [])
  | e0 |> left t0' t1' :: l' =>
      match t0 =? t0', t1 =? t1', split_sum_list t0 t1 l' with
      | true, true, Some (l0, l1) => Some (e0 :: l0, l1)
      | _, _, _ => None
      end
  | e1 |> right t0' t1' :: l' =>
      match t0 =? t0', t1 =? t1', split_sum_list t0 t1 l' with
      | true, true, Some (l0, l1) => Some (l0, e1 :: l1)
      | _, _, _ => None
      end
  | _ :: _ =>
      None
  end.

Function add_to_qpair_list e0 e1 l : list (expr * list expr) :=
  match l with
  | [] =>
      [(e0, [e1])]
  | (e0', l1) :: l' =>
      if e0 =? e0'
      then (e0, e1 :: l1) :: l'
      else (e0', l1) :: add_to_qpair_list e0 e1 l'
  end.

Function spread_qpair_list l : option (list (expr * list expr)) :=
  match l with
  | [] =>
      Some []
  | #(e0, e1) :: l' =>
      match spread_qpair_list l' with
      | Some l => Some (add_to_qpair_list e0 e1 l)
      | _ => None
      end
  | _ :: _ =>
      None
  end.

Definition get_single_var l : option string :=
  match l with
  | [var x] => Some x
  | _ => None
  end.

Fixpoint missing_span t l X {struct t} : option (list expr) :=
  match t, l with
  | _, [] =>
      Some [var (fresh X)]
  | _, [var x] =>
      if mem x X then None else Some []
  | qunit, [null] =>
      Some []
  | t0 + t1, _ =>
      match split_sum_list t0 t1 l with
      | None =>
          None
      | Some (l0, l1) =>
          match missing_span t0 l0 X, missing_span t1 l1 X with
          | Some l0', Some l1' =>
              Some (map (left t0 t1) l0' ++ map (right t0 t1) l1')
          | _, _ =>
              None
          end
      end
  | t0 * t1, _ =>
      match spread_qpair_list l with
      | None =>
          None
      | Some l' =>
          match
            missing_span t0 (map fst l') (X ++ flat_map free_vars (flat_map snd l'))
          with
          | None =>
              None
          | Some l0 =>
              flat_map_maybe
                (fun '(e0, l1) => match missing_span t1 l1 (X ++ free_vars e0) with
                                  | Some l1' => Some (map (qpair e0) l1')
                                  | None => None
                                  end) (map (fun e => (e, [])) l0 ++ l')
          end
      end
  | _, _ =>
      None
  end.

Definition span_list t l X : option (list expr) :=
  match missing_span t l X with
  | None => None
  | Some l' => Some (l' ++ l)
  end.

Definition ortho_list t l : option (list expr) :=
  match span_list t l [] with
  | None => None
  | Some l' => Some (filter (fun e => inb e l) l')
  end.

Definition ortho_check t l : bool :=
  match span_list t l [] with
  | None => false
  | Some _ => true
  end.

Fixpoint dephase t e : list expr :=
  match e with
  | e' |> rphase t' (var x) gamma gamma' =>
      if (t =? t') && eqb Variables.x x && eqb_real gamma gamma'
      then dephase t e'
      else [e]
  | ctrl e' t0 l t' =>
      if t =? t'
      then flat_map (fun '(ej, ej') => dephase t ej') l
      else [e]
  | _ => [e]
  end.

Function split_qpair_list l : option (list expr * list expr) :=
  match l with
  | [] =>
      Some ([], [])
  | #(e0, e1) :: l' =>
      match split_qpair_list l' with
      | Some (l0, l1) => Some (e0 :: l0, e1 :: l1)
      | _ => None
      end
  | _ :: _ =>
      None
  end.

Function erases_check x t l : bool :=
  let l' := flat_map (dephase t) l in
  if forallb (eqb (var x)) l'
  then true
  else match t, split_qpair_list l' with
       | t0 * t1, Some (l0, l1) =>
           erases_check x t0 l0 || erases_check x t1 l1
       | _, _ =>
           false
       end.

Function erases_dephased_check x t l : bool :=
  if forallb (eqb (var x)) l
  then true
  else match t, split_qpair_list l with
       | t0 * t1, Some (l0, l1) =>
           erases_check x t0 l0 || erases_check x t1 l1
       | _, _ =>
           false
       end.

Fixpoint partition_context X (g : context) : context * context :=
  match g with
  | [] => ([], [])
  | (x, t) :: g' =>
      let (g0, g1) := partition_context X g' in
      if mem x X then ((x, t) :: g0, g1)
      else (g0, (x, t) :: g1)
  end.

Function partition_ord_context X (g : context) : option (context * context) :=
  match g with
  | [] => Some ([], [])
  | (x, t) :: g' =>
      if mem x X
      then match partition_ord_context X g' with
           | None => None
           | Some (g0, g1) => Some ((x, t) :: g0, g1)
           end
      else if forallb (fun x' => negb (mem x' X)) (dom g')
      then Some ([], (x, t) :: g')
      else None
  end.

Fixpoint partition_pair_context (X0 X1 : set) (d : context) :
  option (context * context * context) :=
  match d with
  | [] => Some ([], [], [])
  | (x, t) :: dp =>
      match mem x X0, mem x X1, partition_pair_context X0 X1 dp with
      | true, true, Some (d', d0, d1) => Some ((x, t) :: d', d0, d1)
      | true, false, Some (d', d0, d1) => Some (d', (x, t) :: d0, d1)
      | false, true, Some (d', d0, d1) => Some (d', d0, (x, t) :: d1)
      | _, _, _ => None
      end
  end.

Module Export Checks.

Section Aux.

  Variable pure_type_check : context -> context -> expr -> option type.
  Variable context_check : context -> type -> expr -> option context.
  Variable prog_type_check : prog -> option prog_type.

  Definition pattern_type_check (g d : context) t t' '(ej, ej') : bool :=
    match context_check [] t ej with
    | None => false
    | Some gj => pure_type_check (g ++ gj) d ej' =? Some t'
    end.

  Fixpoint mixed_type_check
    (d : context) (e : expr) {struct e} :
    option type :=
    match e with
    | #(e0, e1) =>
        match
          well_formed_check d,
          partition_pair_context (free_vars e0) (free_vars e1) d
        with
        | true, Some (d', d0, d1) =>
            match
              mixed_type_check (d' ++ d0) e0, mixed_type_check (d' ++ d1) e1
            with
            | Some t0, Some t1 => Some (t0 * t1)
            | _, _ => None
            end
        | _, _ =>
            None
        end
    | try e0 e1 =>
        let (d0, d1) := partition_context (free_vars e0) d in
        match
          disjointb (dom d0) (dom d1),
          mixed_type_check d0 e0,
          mixed_type_check d1 e1
        with
        | true, Some t0, Some t1 => if t0 =? t1 then Some t0 else None
        | _, _, _ => None
        end
    | e' |> f =>
        match mixed_type_check d e', prog_type_check f with
        | Some t, Some (t0 ~> t1) | Some t, Some (t0 ==> t1) =>
            if t =? t0 then Some t1 else None
        | _, _ => None
        end
    | _ => pure_type_check [] d e
    end.

  Definition first_pattern_context_check
    (g : context) t t' ej ej' :
    option context :=
    match context_check [] t ej with
    | None => None
    | Some gj => context_check (g ++ gj) t' ej'
    end.

  Definition pattern_context_check
    (g : context) (t t' : type) (d : context) '((ej, ej') : expr * expr) : bool :=
    match context_check [] t ej with
    | None => false
    | Some gj => match context_check (g ++ gj) t' ej' with
                 | None => false
                 | Some d' => equivb d d'
                 end
    end.

  Fixpoint mixed_context_check
    (t : type) (e : expr) {struct e} :=
    match e with
    | #(e0, e1) =>
        match t with
        | t0 * t1 =>
            match mixed_context_check t0 e0, mixed_context_check t1 e1 with
            | Some d0, Some d1 => merge d0 d1
            | _, _ => None
            end
        | _ =>
            None
        end
    | try e0 e1 =>
        match mixed_context_check t e0, mixed_context_check t e1 with
        | Some d0, Some d1 =>
            if disjointb (dom d0) (dom d1) then Some (d0 ++ d1) else None
        | _, _ =>
            None
        end
    | e' |> f =>
        match prog_type_check f with
        | Some (t0 ~> t1) | Some (t0 ==> t1) =>
            if t =? t1 then mixed_context_check t0 e' else None
        | _ => None
        end
    | _ => context_check [] t e
    end.

End Aux.

Fixpoint pure_type_check (g d : context) e {struct e} : option type :=
  let mixed_type_check := mixed_type_check pure_type_check prog_type_check in
  match e with
  | null =>
      match well_formed_check g, d with
      | true, [] => Some qunit
      | _, _ => None
      end
  | var x =>
      match well_formed_check g, d with
      | true, [] => g x
      | true, [(x', t)] => match x =? x', g x with
                           | true, None => Some t
                           | _, _ => None
                           end
      | _, _ => None
      end
  | #(e0, e1) =>
      match
        well_formed_check (g ++ d),
        partition_pair_context (free_vars e0) (free_vars e1) d
      with
      | true, Some (d', d0, d1) =>
          match
            pure_type_check g (d' ++ d0) e0, pure_type_check g (d' ++ d1) e1
          with
          | Some t0, Some t1 => Some (t0 * t1)
          | _, _ => None
          end
      | _, _ =>
          None
      end
  | ctrl e t l t' =>
      let Xe := free_vars e in
      let (d, d') := partition_context Xe d in
      let (ej, ej') := split l in
      let (g, g') := partition_context Xe g in
      if
        well_formed_check (g ++ g' ++ d ++ d') &&
        (mixed_type_check (g ++ d) e =? Some t) &&
        ortho_check t ej &&
        forallb
          (pattern_type_check pure_type_check context_check
           (g ++ g') (d ++ d') t t') l &&
        forallb (fun x => erases_check x t' ej') (dom d)
      then Some t'
      else None
  | try _ _ =>
      None
  | e' |> f =>
      match pure_type_check g d e', prog_type_check f with
      | Some t', Some (t0 ~> t1) => if t' =? t0 then Some t1 else None
      | _, _ => None
      end
  end
with context_check (g : context) (t : type) (e : expr) {struct e} : option context :=
  let mixed_context_check := mixed_context_check context_check prog_type_check in
  match e, t with
  | null, qunit =>
      if well_formed_check g then Some [] else None
  | var x, _ =>
      match well_formed_check g, g x with
      | true, None => Some [(x, t)]
      | true, Some t' => if t =? t' then Some [] else None
      | _, _ => None
      end
  | #(e0, e1), t0 * t1 =>
      match context_check g t0 e0, context_check g t1 e1 with
      | Some d0, Some d1 => merge d0 d1
      | _, _ => None
      end
  | ctrl e' t0 l t1, _ =>
      let Xe := free_vars e' in
      let (ej, ej') := split l in
      match t =? t1, mixed_context_check t0 e', l with
      | true, Some d, [] =>
          remove_all g d
      | true, Some d, (e0, e0') :: l =>
          match first_pattern_context_check context_check g t0 t1 e0 e0' with
          | None =>
              None
          | Some d0 =>
              if 
                inclusionb d (g ++ d0) &&
                ortho_check t0 ej &&
                forallb (pattern_type_check pure_type_check context_check g d0 t0 t1) l &&
                forallb (fun x => erases_check x t1 ej') (dom d)
              then Some d0
              else None
          end
      | _, _, _ =>
          None
      end
  | e' |> f, _ =>
      match prog_type_check f with
      | Some (t0 ~> t1) =>
          if t =? t1 then context_check g t0 e' else None
      | _ => None
      end
  | _, _ =>
      None
  end
with prog_type_check (f : prog) : option prog_type :=
  let mixed_type_check := mixed_type_check pure_type_check prog_type_check in
  match f with
  | u3 _ _ _ =>
      Some (bit ~> bit)
  | left t0 t1 =>
      Some (t0 ~> t0 + t1)
  | right t0 t1 =>
      Some (t1 ~> t0 + t1)
  | lambda e t e' =>
      match context_check [] t e with
      | None =>
          None
      | Some d =>
          match pure_type_check [] d e' with
          | None =>
              match mixed_type_check (restriction d (free_vars e')) e' with
              | None => None
              | Some t' => Some (t ==> t')
              end
          | Some t' => Some (t ~> t')
          end
      end
  | rphase t e gamma' gamma =>
      match context_check [] t e with
      | None => None
      | Some _ => Some (t ~> t)
      end
  end.

End Checks.

Definition mixed_type_check := mixed_type_check pure_type_check prog_type_check.

Definition mixed_context_check :=
  mixed_context_check context_check prog_type_check.

Definition pattern_type_check :=
  pattern_type_check pure_type_check context_check.

Definition first_pattern_context_check :=
  first_pattern_context_check context_check.

Definition pattern_context_check :=
  pattern_context_check context_check.

Inductive split_sum t0 t1 : list expr -> list expr -> list expr -> Prop :=
  | split_sum_nil :
      split_sum t0 t1 [] [] []
  | split_sum_left e0 l l0 l1 :
      split_sum t0 t1 l l0 l1 ->
      split_sum t0 t1 (left t0 t1 e0 :: l) (e0 :: l0) l1
  | split_sum_right e1 l l0 l1 :
      split_sum t0 t1 l l0 l1 ->
      split_sum t0 t1 (right t0 t1 e1 :: l) l0 (e1 :: l1).

Inductive split_qpair : list expr -> list expr -> list expr -> Prop :=
  | split_qpair_nil :
      split_qpair [] [] []
  | split_qpair_cons l l0 l1 e0 e1 :
      split_qpair l l0 l1 ->
      split_qpair (#(e0, e1) :: l) (e0 :: l0) (e1 :: l1).

Inductive add_to_qpair :
  expr -> expr -> list (expr * list expr) -> list (expr * list expr) -> Prop :=
  | add_to_qpair_nil e0 e1 :
      add_to_qpair e0 e1 [] [(e0, [e1])]
  | add_to_qpair_hd e0 e1 l1 l :
      add_to_qpair e0 e1 ((e0, l1) :: l) ((e0, e1 :: l1) :: l)
  | add_to_qpair_tl e0 e0' e1 l1 l l' :
      e0 <> e0' ->
      add_to_qpair e0 e1 l l' ->
      add_to_qpair e0 e1 ((e0', l1) :: l) ((e0', l1) :: l').

Inductive spread_qpair : list expr -> list (expr * list expr) -> Prop :=
  | spread_qpair_nil :
      spread_qpair [] []
  | spread_qpair_cons e0 e1 l l' :
      spread_qpair l l' ->
      spread_qpair (#(e0, e1) :: l) (add_to_qpair_list e0 e1 l').

Inductive missing_span_prop : type -> list expr -> set -> list expr -> Prop :=
  | missing_span_var t x X :
      ~ In x X ->
      missing_span_prop t [var x] X []
  | missing_span_empty t X :
      missing_span_prop t [] X [var (fresh X)]
  | missing_span_unit X :
      missing_span_prop qunit [null] X []
  | missing_span_sum t0 t1 l l0 l1 X l0' l1' :
      split_sum t0 t1 l l0 l1 ->
      missing_span_prop t0 l0 X l0' ->
      missing_span_prop t1 l1 X l1' ->
      missing_span_prop (t0 + t1) l X (map (left t0 t1) l0' ++ map (right t0 t1) l1')
  | missing_span_prod t0 t1 l l' l0 lr X :
      spread_qpair l l' ->
      missing_span_prop t0 (map fst l') (X ++ flat_map free_vars (flat_map snd l')) l0 ->
      map fst lr = map (fun e => (e, [])) l0 ++ l' ->
      (forall e0 l1 l1',
       In (e0, l1, l1') lr ->
       missing_span_prop t1 l1 (X ++ free_vars e0) l1') ->
      missing_span_prop (t0 * t1) l X (flat_map (fun '(e0, l1, l1') => map (qpair e0) l1') lr).

Inductive phased t l : list expr -> Prop :=
  | phased_refl :
      phased t l l
  | phased_gphase l0 e l1 gamma :
      phased t l (l0 ++ e :: l1) ->
      phased t l (l0 ++ gphase t gamma e :: l1)
  | phased_ctrl l0 e t' l' l1 :
      phased t l (l0 ++ map snd l' ++ l1) ->
      phased t l (l0 ++ ctrl e t' l' t :: l1).

Inductive part_pair_ctx_prop (X0 X1 : set) :
  context -> context -> context -> context -> Prop :=
  | part_pair_ctx_nil :
      part_pair_ctx_prop X0 X1 [] [] [] []
  | part_pair_ctx_both d d' d0 d1 x t :
      In x X0 ->
      In x X1 ->
      part_pair_ctx_prop X0 X1 d d' d0 d1 ->
      part_pair_ctx_prop X0 X1 ((x, t) :: d) ((x, t) :: d') d0 d1
  | part_pair_ctx_0 d d' d0 d1 x t :
      In x X0 ->
      ~ In x X1 ->
      part_pair_ctx_prop X0 X1 d d' d0 d1 ->
      part_pair_ctx_prop X0 X1 ((x, t) :: d) d' ((x, t) :: d0) d1
  | part_pair_ctx_1 d d' d0 d1 x t :
      ~ In x X0 ->
      In x X1 ->
      part_pair_ctx_prop X0 X1 d d' d0 d1 ->
      part_pair_ctx_prop X0 X1 ((x, t) :: d) d' d0 ((x, t) :: d1).

Lemma split_sum_sound :
  forall t0 t1 l l0 l1,
  split_sum_list t0 t1 l = Some (l0, l1) -> split_sum t0 t1 l l0 l1.
Proof.
  intros t0 t1 l.
  functional induction (split_sum_list t0 t1 l); try discriminate; simpl;
  intros l0' l1' H; injection H as; subst.
  - constructor.
  - apply eqb_sound in e1, e2. subst. auto using split_sum.
  - apply eqb_sound in e0, e2. subst. auto using split_sum.
Qed.

Lemma split_sum_perm :
  forall t0 t1 l l0 l1,
  split_sum t0 t1 l l0 l1 ->
  Permutation l (map (left t0 t1) l0 ++ map (right t0 t1) l1).
Proof.
  intros t0 t1 l l0 l1 H. induction H; simpl; eauto using Permutation.
  rewrite IHsplit_sum. apply Permutation_middle.
Qed.

Lemma split_qpair_sound :
  forall l l0 l1,
  split_qpair_list l = Some (l0, l1) -> split_qpair l l0 l1.
Proof.
  intros l.
  functional induction (split_qpair_list l); try discriminate;
  intros l0' l1' H; injection H as; subst; auto using split_qpair.
Qed.

Lemma spread_qpair_sound :
  forall l l', spread_qpair_list l = Some l' -> spread_qpair l l'.
Proof.
  intros l.
  functional induction (spread_qpair_list l); intros; try discriminate;
  injection H as; subst; auto using spread_qpair.
Qed.

Lemma spread_qpair_flat_map :
  forall l l',
  spread_qpair l l' ->
  Permutation l (flat_map (fun '(e0, l1) => map (qpair e0) l1) l').
Proof.
  intros l l' H. induction H; auto.
  rewrite IHspread_qpair. clear IHspread_qpair H l.
  induction l' as [| [e l1] l IH]; auto.
  simpl. destruct (e0 =? e) eqn:E; simpl.
  - apply eqb_sound in E. subst. reflexivity.
  - rewrite Permutation_middle, IH. reflexivity.
Qed.

Lemma missing_span_sound :
  forall t l X l',
  missing_span t l X = Some l' ->
  missing_span_prop t l X l'.
Proof.
  intros t.
  induction t as [| | t0 IH0 t1 IH1 | t0 IH0 t1 IH1 ]; simpl;
  intros [| [] []] X l' H; auto_false.
  - injection H as. subst. apply missing_span_empty.
  - destruct (mem x X) eqn:E; auto_false.
    injection H as. subst. apply missing_span_var.
    intros H. apply mem_spec in H. congruence.
  - injection H as. subst. apply missing_span_empty.
  - injection H as. subst. apply missing_span_unit.
  - destruct (mem x X) eqn:E; auto_false.
    injection H as. subst. apply missing_span_var.
    intros H. apply mem_spec in H. congruence.
  - injection H as. subst. apply missing_span_empty.
  - destruct (mem x X) eqn:E; auto_false.
    injection H as. subst. apply missing_span_var.
    intros H. apply mem_spec in H. congruence.
  - destruct (split_sum_list _ _ _) as [[l0 l1] |] eqn:Es; auto_false.
    destruct (missing_span t0 l0 X) eqn:E0; auto_false.
    destruct (missing_span t1 l1 X) eqn:E1; auto_false.
    injection H as. subst.
    eapply missing_span_sum; eauto using split_sum_sound.
  - destruct (split_sum_list _ _ _) as [[l0 l1] |] eqn:Es; auto_false.
    destruct (missing_span t0 l0 X) eqn:E0; auto_false.
    destruct (missing_span t1 l1 X) eqn:E1; auto_false.
    injection H as. subst.
    eapply missing_span_sum; eauto using split_sum_sound.
  - injection H as. subst. apply missing_span_empty.
  - destruct (mem x X) eqn:E; auto_false.
    injection H as. subst. apply missing_span_var.
    intros H. apply mem_spec in H. congruence.
  - destruct (spread_qpair_list _) eqn:Es; auto_false.
    destruct (missing_span t0 _ _) eqn:E0; auto_false.
    apply spread_qpair_sound in Es. apply IH0 in E0.
    remember (map _ l0 ++ l) as ll.
    destruct (map_maybe (fun '(e0, l1) =>
                         match missing_span t1 l1 (X ++ free_vars e0) with
                         | Some l1' => Some (e0, l1, l1')
                         | None => None
                         end) ll) as [lr |] eqn:Er.
    + rewrite flat_map_map_maybe in H.
      destruct (map_maybe _ ll) eqn:El; auto_false.
      injection H as.
      assert (l1 = map (fun '(e0, l1, l1') => (e0, l1, map (qpair e0) l1')) lr).
      { eapply map_maybe_ext2; try eassumption.
        intros [ea la] [[eb lb] lb'] He.
        destruct (missing_span t1 la _) eqn:Em; auto_false.
        congruence. }
      subst. rewrite flat_map_map. simpl.
      erewrite flat_map_ext; try eapply missing_span_prod; eauto.
      * eapply map_maybe_inv; try apply Er.
        intros [e le] [[e' le'] l'] H.
        destruct (missing_span t1 le _) eqn:E; auto_false.
        injection H as. subst. reflexivity.
      * intros ei li li' Hi.
        apply IH1.
        apply map_maybe_exists with (b:=(ei, li, li')) in Er; auto.
        destruct Er as [[e' l'] [H' Er]].
        destruct (missing_span t1 l' _) eqn:Em; auto_false.
        congruence.
      * intros [[ei li] li']. reflexivity.
    + exfalso. apply map_maybe_None in Er as [[er lr] [Hi Er]].
      destruct (missing_span t1 lr _) eqn:Em; auto_false.
      apply flat_map_maybe_Some with (a:=(er, lr)) in H; auto.
      destruct H as [lr' Hr]. rewrite Em in Hr. discriminate.
  - destruct (spread_qpair_list _) eqn:Es; auto_false.
    destruct (missing_span t0 _ _) eqn:E0; auto_false.
    apply spread_qpair_sound in Es. apply IH0 in E0.
    remember (map _ l1 ++ l0) as ll.
    destruct (map_maybe (fun '(e0, l1) =>
                         match missing_span t1 l1 (X ++ free_vars e0) with
                         | Some l1' => Some (e0, l1, l1')
                         | None => None
                         end) ll) as [lr |] eqn:Er.
    + rewrite flat_map_map_maybe in H.
      destruct (map_maybe _ ll) eqn:El; auto_false.
      injection H as. subst.
      assert (l2 = map (fun '(e0, l1, l1') => (e0, l1, map (qpair e0) l1')) lr).
      { eapply map_maybe_ext2; try eassumption.
        intros [ea la] [[eb lb] lb'] He.
        destruct (missing_span t1 la _) eqn:Em; auto_false.
        congruence. }
      subst. rewrite flat_map_map. simpl.
      erewrite flat_map_ext; try eapply missing_span_prod; eauto.
      * eapply map_maybe_inv; try apply Er.
        intros [ex le] [[e' le'] l'] H.
        destruct (missing_span t1 le _) eqn:E; auto_false.
        injection H as. subst. reflexivity.
      * intros ei li li' Hi.
        apply IH1.
        apply map_maybe_exists with (b:=(ei, li, li')) in Er; auto.
        destruct Er as [[e' l'] [H' Er]].
        destruct (missing_span t1 l' _) eqn:Em; auto_false.
        congruence.
      * intros [[ei li] li']. reflexivity.
    + exfalso. apply map_maybe_None in Er as [[er lr] [Hi Er]].
      destruct (missing_span t1 lr _) eqn:Em; auto_false.
      apply flat_map_maybe_Some with (a:=(er, lr)) in H; auto.
      destruct H as [lr' Hr]. rewrite Em in Hr. discriminate.
Qed.

Lemma disjoint_fresh :
  forall X, disjoint X [fresh X].
Proof.
  intros X x H [Hx | []]. subst. apply fresh_spec in H as [].
Qed.

Lemma missing_span_orig_disjoint :
  forall t l X l',
  missing_span_prop t l X l' ->
  disjoint X (flat_map free_vars l).
Proof.
  intros t l X l' H. induction H; simpl; auto using disjoint_nil1.
  - apply disjoint_singleton1, H.
  - apply split_sum_perm in H. rewrite H, flat_map_app, disjoint_app1.
    repeat rewrite flat_map_map. simpl.
    split; rewrite flat_map_ext with (g:=free_vars) by reflexivity; assumption.
  - apply spread_qpair_flat_map in H. rewrite H, flat_map_flat_map.
    intros x Hx. rewrite in_flat_map. intros [[e0 l1] [H' Hf]].
    rewrite flat_map_map in Hf. simpls. rewrite <- flat_map_app_perm in Hf.
    apply in_app_or in Hf as [Hf | Hf].
    + apply in_flat_map in Hf as [_ [_ Hf]]. eapply IHmissing_span_prop.
      * apply in_or_app. left. eassumption.
      * apply in_flat_map. exists e0. split; auto.
        apply in_map_iff. exists (e0, l1). split; auto.
    + specialize (H3 e0 l1). 
      eapply or_intror, in_or_app in H'. erewrite <- H1 in H'.
      apply in_map_iff in H' as [[[e' le] l''] [Hs H']].
      injection Hs as. subst. apply H3 in H'. eapply H'; try apply Hf.
      apply in_or_app. auto.
Qed.

Lemma missing_span_free_vars :
  forall t l X l',
  missing_span_prop t l X l' ->
  disjoint X (flat_map free_vars l').
Proof.
  intros t l X l' H.
  induction H; simpl; auto using disjoint_fresh, disjoint_nil1.
  - rewrite flat_map_app, flat_map_map, flat_map_map, disjoint_app1. auto.
  - intros x Hx Hi. apply in_flat_map in Hi as [e [He Hi]].
    apply in_flat_map in He as [[[e0 l1] l1'] [Hr He]].
    apply in_map_iff in He as [e1 [He H']]. subst. simpls.
    apply in_app_or in Hi as [Hi | Hi].
    + assert (In (e0, l1) (map fst lr)) as Hm.
      { apply in_map_iff. exists (e0, l1, l1'). auto. }
      rewrite H1 in Hm. apply in_app_iff in Hm as [Hm | Hm].
      * apply in_map_iff in Hm as [e0' [He Hm]]. injection He as. subst.
        apply disjoint_app0 in IHmissing_span_prop as [IH _].
        apply IH in Hx. apply Hx.
        apply in_flat_map. exists e0. split; auto.
      * apply missing_span_orig_disjoint, disjoint_app0 in H0 as [H0 _].
        apply H0 in Hx. apply Hx, in_flat_map. exists e0. split; auto.
        apply in_map_iff. exists (e0, l1). auto.
    + apply H3 in Hr. apply disjoint_app0 in Hr as [Hr _].
      eapply Hr, in_flat_map; eauto.
Qed.

Lemma split_sum_in_left :
  forall t0 t1 l l0 l1,
  split_sum t0 t1 l l0 l1 ->
  forall e0, In e0 l0 <-> In (left t0 t1 e0) l.
Proof.
  intros t0 t1 l l0 l1 H. induction H; intros e0'; simpl; split; auto.
  - intros [He | Hi]; subst; auto.
    right. apply IHsplit_sum, Hi.
  - intros [He | Hi].
    + injection He as. subst. auto.
    + right. rewrite IHsplit_sum. assumption.
  - intros H0. right. apply IHsplit_sum, H0.
  - intros [Hc | Hi]; try discriminate.
    apply IHsplit_sum, Hi.
Qed.

Lemma split_sum_in_right :
  forall t0 t1 l l0 l1,
  split_sum t0 t1 l l0 l1 ->
  forall e1, In e1 l1 <-> In (right t0 t1 e1) l.
Proof.
  intros t0 t1 l l0 l1 H. induction H; intros e0'; simpl; split; auto.
  - intros H0. right. apply IHsplit_sum, H0.
  - intros [Hc | Hi]; try discriminate.
    apply IHsplit_sum, Hi.
  - intros [He | Hi]; subst; auto.
    right. apply IHsplit_sum, Hi.
  - intros [He | Hi].
    + injection He as. subst. auto.
    + right. rewrite IHsplit_sum. assumption.
Qed.

Lemma split_sum_in :
  forall t0 t1 l l0 l1,
  split_sum t0 t1 l l0 l1 ->
  forall e, In e l -> In e (map (left t0 t1) l0) \/ In e (map (right t0 t1) l1).
Proof.
  intros t0 t1 l l0 l1 H. induction H; intros e []; subst; simpl; auto;
  apply IHsplit_sum in H0 as []; auto.
Qed.

Lemma split_sum_list_NoDup :
  forall t0 t1 l l0 l1,
  split_sum t0 t1 l l0 l1 ->
  NoDup l0 ->
  NoDup l1 ->
  NoDup l.
Proof.
  intros t0 t1 l l0 l1 H. induction H; intros H0 H1; constructor.
  - intros Hc. inversion_clear H0. apply H2.
    rewrite split_sum_in_left; eauto.
  - inversion_clear H0. auto.
  - intros Hc. inversion_clear H1. apply H2.
    rewrite split_sum_in_right; eauto.
  - inversion_clear H1. auto.
Qed.

Lemma split_qpair_combine :
  forall l l0 l1,
  split_qpair l l0 l1 -> l = map (uncurry qpair) (combine l0 l1).
Proof.
  intros l l0 l1 H. induction H; simpl; f_equal.
  assumption.
Qed.

Lemma split_qpair_length :
  forall l l0 l1,
  split_qpair l l0 l1 -> length l0 = length l1.
Proof.
  intros l l0 l1 H. induction H; simpl; auto.
Qed.

Lemma spanning_NoDup :
  forall t l, spanning t l -> NoDup l.
Proof.
  intros t l H. induction H; eauto using NoDup, Permutation_NoDup.
  - rewrite NoDup_app. splits.
    + intros e Hl Hr.
      rewrite in_map_iff in *.
      destruct Hl as [e0 [Hl _]].
      destruct Hr as [e1 [Hr _]].
      subst. discriminate.
    + apply FinFun.Injective_map_NoDup; auto.
      intros e e' He. injection He. auto.
    + apply FinFun.Injective_map_NoDup; auto.
      intros e e' He. injection He. auto.
  - apply flat_map_NoDup.
    + apply NoDup_map_inv in IHspanning. assumption.
    + intros [e0 l1] Hi. apply FinFun.Injective_map_NoDup.
      * intros e e' He. injection He. trivial.
      * eapply H1. eassumption.
    + intros [e0 l1] [e0' l1'] e Hi Hi' Hm Hm'.
      apply in_map_iff in Hm as [ee [Hm Hl1]], Hm' as [e' [Hm' Hl1']].
      subst. injection Hm' as. subst. f_equal.
      eapply NoDup_fst; eassumption.
Qed.

Lemma span_list_spanning :
  forall t l X l', span_list t l X = Some l' -> spanning t l'.
Proof.
  unfold span_list. intros t l X l' H.
  destruct (missing_span t l X) eqn:E; auto_false.
  injection H as. subst. apply missing_span_sound in E.
  induction E; simpl; eauto using spanning; eapply spanning_perm.
  all: swap 1 2. all: swap 3 4.
  - apply spanning_sum.
    + apply IHE1.
    + apply IHE2.
  - repeat rewrite map_app. repeat rewrite <- app_assoc.
    apply Permutation_app_head. rewrite Permutation_app_comm, <- app_assoc.
    apply Permutation_app_head. rewrite Permutation_app_comm.
    symmetry. apply split_sum_perm, H.
  - apply spanning_pair.
    + instantiate (1 := map (fun '(e0, l1, l1') => (e0, l1' ++ l1)) lr).
      rewrite map_map. replace (map _ lr) with (map fst (map fst lr)).
      * rewrite H0, map_app, map_map. simpl. rewrite map_id. assumption.
      * rewrite map_map. apply map_ext. intros [[e0 l1] l1']. reflexivity.
    + intros e0 l1 Hi. apply in_map_iff in Hi as [[[e0' l11] l12] [He Hi]].
      injection He as. subst. eapply H2, Hi.
    + intros e0 l1 Hi. apply in_map_iff in Hi as [[[e0' l11] l12] [He Hi]].
      injection He as. subst. rewrite flat_map_app, disjoint_app1.
      split; try (apply H1, missing_span_free_vars, disjoint_app0 in Hi; tauto).
      assert (In e0 l0 /\ l11 = [] \/ In (e0, l11) l') as Ho.
      { apply in_split_l in Hi. rewrite fst_split, H0 in Hi.
        simpls. apply in_app_iff in Hi as [Hi | Hi]; auto.
        left. apply in_map_iff in Hi as [e [He Hi]]. injection He as. subst.
        auto. }
      destruct Ho; unpack; subst; auto using disjoint_nil1.
      apply missing_span_orig_disjoint in E. rewrite disjoint_app0 in E. unpack.
      symmetry in H5. rewrite flat_map_concat_map in H5. symmetry in H5.
      rewrite disjoint_concat1 in H5. specialize (H5 (free_vars e0)).
      symmetry in H5.
      rewrite flat_map_flat_map, flat_map_concat_map, disjoint_concat1 in H5.
      apply H5.
      * apply in_map, in_map_iff. exists (e0, l11). auto.
      * apply in_map_iff. exists (e0, l11). auto.
  - rewrite flat_map_map.
    rewrite flat_map_ext
      with (g:=fun '(e0, l1, l1') => map (qpair e0) (l1' ++ l1))
      by (intros [[]]; reflexivity).
    assert
      (Permutation l (flat_map (fun '(e0, l1, _) => map (qpair e0) l1) lr))
      as Ha.
    { erewrite flat_map_ext.
      - rewrite <- flat_map_map. rewrite H0, flat_map_app, flat_map_map.
        instantiate (1 := fun '(e0, l1) => map (qpair e0) l1).
        simpl. rewrite flat_map_nil. simpl.
        apply spread_qpair_flat_map, H.
      - simpl. intros [[e0 l1] l1']. reflexivity. }
    rewrite Ha, flat_map_app_perm.
    erewrite flat_map_ext; try apply Permutation_refl.
    intros [[e0 l1] l1']. apply map_app.
Qed.

Lemma span_list_NoDup :
  forall t l X l',
  span_list t l X = Some l' ->
  NoDup l.
Proof.
  unfold span_list. intros t l X l' H.
  destruct (missing_span t l X) eqn:E; auto_false.
  injection H as. subst. apply missing_span_sound in E.
  induction E; eauto using NoDup, split_sum_list_NoDup.
  apply spread_qpair_flat_map in H. rewrite H.
  apply flat_map_NoDup; eauto using NoDup_map_inv.
  - intros [e0 l1] Hi. apply FinFun.Injective_map_NoDup.
    + intros e e' He. congruence.
    + assert (In (e0, l1) (map fst lr)). { rewrite H0. auto using in_or_app. }
      apply in_map_iff in H3 as [[[e00 l11] l1'] [He Hl]].
      injection He as. subst. eapply H2, Hl.
  - intros [e0 l1] [e0' l1'] e Hi Hi' He He'.
    apply in_map_iff in He as [ee [He Hl1]], He' as [e' [He' Hl1']].
    subst. injection He' as. subst. f_equal.
    eapply NoDup_fst; eassumption.
Qed.

Lemma ortho_exists :
  forall t l l',
  (forall e, In e l -> In e l') ->
  NoDup l ->
  spanning t l' ->
  ortho t l.
Proof.
  intros t l l' Hf Hn Hs.
  destruct
    (@permutation_sublist _ l (filter (fun e => inb e l) l') l').
  - apply NoDup_Permutation; eauto using NoDup_filter, spanning_NoDup, Hs.
    intros e. rewrite filter_In, inb_spec; auto using eqb_expr_valid.
    split; intros; unpack; auto.
  - apply filter_sublist.
  - unpack. exists x. split; auto.
    eapply spanning_perm.
    + symmetry. apply H0.
    + assumption.
Qed.

Lemma ortho_check_sound :
  forall t l, ortho_check t l = true -> ortho t l.
Proof.
  unfold ortho_check. intros t l H.
  destruct (span_list t l []) as [l' |] eqn:E; try discriminate.
  clear H.
  apply ortho_exists with (l':=l');
  eauto using span_list_NoDup, span_list_spanning.
  unfold span_list in E.
  destruct (missing_span t l []) eqn:Em; auto_false.
  injection E as. subst. apply missing_span_sound in Em.
  induction Em; auto_false; intros e H'; apply in_app_iff; auto.
Qed.

Lemma flat_map_snd :
  forall A B C (f : B -> list C) (l : list (A * B)),
  flat_map (fun '(_, ej') => f ej') l = flat_map f (map snd l).
Proof.
  intros. induction l as [| [a b] l IH]; simpl; f_equal; auto.
Qed.

#[local]
Instance phased_trans :
  forall t, Transitive (phased t).
Proof.
  intros t l1 l2 l3 H1 H3. generalize dependent l1.
  induction H3; auto using phased.
Qed.

Lemma phased_app :
  forall t l0 l1 l0' l1',
  phased t l0 l0' ->
  phased t l1 l1' ->
  phased t (l0 ++ l1) (l0' ++ l1').
Proof.
  intros t l0 l1 l0' l1' H0 H1. transitivity (l0 ++ l1').
  - induction H1; auto using phased.
    + rewrite IHphased. repeat rewrite app_assoc. repeat constructor.
    + rewrite IHphased. repeat rewrite app_assoc. constructor.
      repeat rewrite app_assoc. constructor.
  - induction H0; auto using phased.
    + rewrite IHphased. repeat rewrite <- app_assoc. repeat constructor.
    + rewrite IHphased. repeat rewrite <- app_assoc. repeat constructor.
Qed.

Lemma phased_flat_map :
  forall t l f,
  (forall e, In e l -> phased t (f e) [e]) ->
  phased t (flat_map f l) l.
Proof.
  intros t l. induction l as [| e l IH]; auto using phased.
  simpl. intros f H.
  replace (e :: l) with ([e] ++ l) by reflexivity. auto using phased_app.
Qed.

Lemma phased_singleton :
  forall t e, phased t (dephase t e) [e].
Proof.
  intros t e. induction e using expr_ind'; simpl; auto using phased.
  - destruct (t =? t') eqn:Et; auto using phased.
    apply eqb_sound in Et. symmetry in Et. subst.
    rewrite flat_map_snd.
    rewrite <- app_nil_l at 1. rewrite <- app_nil_l. constructor.
    simpl. autorewrite with list. apply phased_flat_map.
    intros e' Hi. apply in_map_iff in Hi as [[ej ej'] [He Hi]]. simpls.
    subst. eauto.
  - destruct e2, (t =? t0) eqn:Et; auto using phased.
    destruct (Variables.x =? x) eqn:Ex, (eqb_real gamma gamma') eqn:Eg; simpl;
    auto using phased.
    apply eqb_sound in Et, Ex, Eg. subst.
    rewrite <- app_nil_l at 1. rewrite <- app_nil_l. constructor. assumption.
Qed.

Lemma phased_spec :
  forall t l, phased t (flat_map (dephase t) l) l.
Proof.
  intros t l. induction l as [| e l IH]; auto using phased.
  simpl. replace (e :: l) with ([e] ++ l) by reflexivity.
  apply phased_app; auto using phased_singleton.
Qed.

Lemma erases_phased :
  forall x t l l',
  phased t l l' ->
  erases x t l ->
  erases x t l'.
Proof.
  intros x t l l' H. induction H; auto using erases.
Qed.

Lemma erases_dephased :
  forall x t l, erases x t (flat_map (dephase t) l) -> erases x t l.
Proof.
  intros x t l H. remember (flat_map (dephase t) l) as l'.
  apply erases_phased with (l:=l'); subst; auto using phased_spec.
Qed.

Lemma erases_check_sound :
  forall x t l, erases_check x t l = true -> erases x t l.
Proof.
  intros x t l H. apply erases_dephased.
  generalize dependent H. functional induction (erases_check x t l); auto_false.
  - intros _.
    remember (flat_map (dephase t) l) as l' eqn:E. clear l E.
    rewrite forallb_eqb_repeat in e by apply eqb_expr_valid.
    rewrite e. constructor.
  - autorewrite with bool. intros [H | H].
    + apply IHb in H. remember (flat_map (dephase (t0 * t1)) l) as l'.
      clear l Heql' e. apply split_qpair_sound in e1.
      apply split_qpair_length in e1 as Hl. apply split_qpair_combine in e1.
      subst. apply erases_pair0. rewrite map_fst_combine by assumption.
      apply erases_dephased, H.
    + apply IHb0 in H. remember (flat_map (dephase (t0 * t1)) l) as l'.
      clear l Heql' e. apply split_qpair_sound in e1.
      apply split_qpair_length in e1 as Hl. apply split_qpair_combine in e1.
      subst. apply erases_pair1. rewrite map_snd_combine by assumption.
      apply erases_dephased, H.
Qed.

Lemma partition_ord_context_sound :
  forall X g g0 g1,
  partition_ord_context X g = Some (g0, g1) ->
  g = g0 ++ g1 /\ dom g0 <= X /\ disjoint (dom g1) X.
Proof.
  intros X g.
  functional induction (partition_ord_context X g);
  intros g0' g1' H; auto_false; injection H as; subst; simpl;
  splits; auto_false.
  - f_equal. apply IHo, e1.
  - apply inclusion_cons_iff. split.
    + apply mem_spec, e0.
    + apply IHo in e1. apply e1.
  - apply IHo in e1. apply e1.
  - symmetry. apply disjoint_cons1. split.
    + intros H. apply mem_spec in H. congruence.
    + rewrite forallb_forall in e1. intros x' H Hg. apply e1 in Hg.
      apply mem_spec in H. rewrite H in Hg. discriminate.
Qed.

Lemma partition_context_permutation :
  forall X d d0 d1,
  partition_context X d = (d0, d1) ->
  Permutation d (d0 ++ d1).
Proof.
  intros X d. induction d as [| [x t] d IH]; simpl; intros d0 d1 H.
  - injection H as. subst. reflexivity.
  - destruct (mem x X), (partition_context X d); injection H as; subst;
    rewrite IH; try reflexivity; auto using Permutation_middle.
Qed.

Lemma partition_pair_context_sound :
  forall X0 X1 d d' d0 d1,
  partition_pair_context X0 X1 d = Some (d', d0, d1) ->
  part_pair_ctx_prop X0 X1 d d' d0 d1.
Proof.
  intros X0 X1 d. induction d as [| [x t] d IH]; simpl; intros d' d0 d1 H.
  - injection H as. subst. constructor.
  - destruct (mem x X0) eqn:E0, (mem x X1) eqn:E1,
      (partition_pair_context X0 X1 d)
      as [[[da db] dc] |];
    try discriminate; injection H as; subst;
    try rewrite <- not_true_iff_false in *; rewrite mem_spec in *;
    constructor; auto.
Qed.

Lemma partition_pair_context_perm :
  forall X0 X1 d d' d0 d1,
  part_pair_ctx_prop X0 X1 d d' d0 d1 ->
  Permutation d (d' ++ d0 ++ d1).
Proof.
  intros X0 X1 d d' d0 d1 H. induction H; simpl; auto;
  transitivity ((x, t) :: d' ++ d0 ++ d1); auto.
  - set (d01 := d0 ++ d1).
    apply Permutation_middle.
  - repeat rewrite app_assoc. set (d0' := d' ++ d0).
    apply Permutation_middle.
Qed.

Fixpoint pattern_list_with_contexts t l :
  option (list (expr * expr * context)) :=
  match l with
  | [] =>
      Some []
  | (ej, ej') :: l' =>
      match context_check [] t ej, pattern_list_with_contexts t l' with
      | Some gj, Some lg => Some ((ej, ej', gj) :: lg)
      | _, _ => None
      end
  end.

Lemma pattern_check_pattern_list :
  forall g d t t' l,
  forallb (pattern_type_check g d t t') l = true ->
  pattern_list_with_contexts t l <> None.
Proof.
  intros g d t t' l H Hc. induction l as [| [e0 e0'] l IH]; auto_false.
  simpls.
  destruct (context_check [] t e0), (pattern_list_with_contexts t l); auto_false.
  autorewrite with bool in H. unpack. auto.
Qed.

Lemma pattern_context_check_pattern_list :
  forall g d t t' l,
  forallb (pattern_context_check g t t' d) l =
    true ->
  pattern_list_with_contexts t l <> None.
Proof.
  intros g d t t' l H Hc. induction l as [| [e0 e0'] l IH]; auto_false.
  simpls.
  destruct (context_check [] t e0), (pattern_list_with_contexts t l);
  auto_false.
  autorewrite with bool in H. unpack. auto.
Qed.

Lemma not_None_Some :
  forall A (o : option A),
  o <> None ->
  exists e, o = Some e.
Proof.
  intros A [e |] H.
  - eauto.
  - contradiction.
Qed.

Lemma pattern_list_without_contexts :
  forall t l l', pattern_list_with_contexts t l = Some l' -> l = map fst l'.
Proof.
  intros t l.
  induction l as [| [e e'] l IH]; intros [| [[e0 e0'] g] l'] H;
  simpls; auto_false;
  destruct (context_check [] t e), (pattern_list_with_contexts t l); auto_false.
  injection H as. subst. rewrite <- IH; reflexivity.
Qed.

Lemma pattern_list_has_contexts :
  forall t l l', pattern_list_with_contexts t l = Some l' ->
  forall ej ej' gj, In (ej, ej', gj) l' -> context_check [] t ej = Some gj.
Proof.
  intros t l.
  induction l as [| [e0 e0'] l IH]; simpl;
  intros [| [[e1 e1'] g0] l'] H ej ej' gj []; auto_false.
  - injection H0 as. subst.
    destruct (context_check [] t e0) eqn:E, (pattern_list_with_contexts t l);
    auto_false.
    injection H as. subst. assumption.
  - eapply IH; eauto.
    destruct (context_check [] t e0), (pattern_list_with_contexts t l); congruence.
Qed.

Lemma context_check_has_pure_type :
  forall g d t t' l l',
  forallb (pattern_type_check g d t t') l = true ->
  pattern_list_with_contexts t l = Some l' ->
  forall ej ej' gj,
  In (ej, ej', gj) l' -> pure_type_check (g ++ gj) d ej' = Some t'.
Proof.
  intros g d t t' l.
  induction l as [| [e0 e0'] l IH];
  intros [| [[e1 e1'] g0] l'] Hf H' ej ej' gj []; simpls; auto_false.
  - injection H as. subst. destruct (context_check [] t e0); auto_false.
    autorewrite with bool in Hf. unpack. apply eqb_sound in H.
    destruct (pattern_list_with_contexts t l); auto_false.
    injection H' as. subst. assumption.
  - autorewrite with bool in Hf. unpack. eapply IH; eauto.
    destruct (context_check [] t e0), (pattern_list_with_contexts t l); congruence.
Qed.

Lemma partition_context_restriction :
  forall X d,
  exists d', partition_context X d = (restriction d X, d').
Proof.
  intros X d. induction d as [| [x t] d IH]; simpl; eauto.
  destruct IH as [d' H']. rewrite H'.
  destruct (mem x X); eauto.
Qed.

Lemma has_channel_type_restriction :
  forall d e e' t t',
  has_pure_type [] d e t ->
  has_mixed_type (restriction d (free_vars e')) e' t' ->
  has_prog_type (lambda e t e') (t ==> t').
Proof.
  intros d e e' t t' H H'.
  destruct (partition_context_restriction (free_vars e') d) as [d' Hd].
  apply partition_context_permutation in Hd.
  apply has_channel_type_abs with (d:=restriction d (free_vars e')) (d0:=d');
  auto.
  rewrite <- Hd. assumption.
Qed.

Lemma context_check_well_formed :
  forall e,
  (forall g t d, context_check g t e = Some d -> well_formed d) /\
  (forall t d, mixed_context_check t e = Some d -> well_formed d).
Proof.
  intros e. induction e using expr_ind'; simpl; split; auto_false.
  - intros g [] d H; auto_false.
    destruct (well_formed_check g); auto_false.
    injection H as. subst. constructor.
  - intros [] d H; auto_false.
    injection H as. subst. constructor.
  - intros g t d H. destruct (well_formed_check g); auto_false.
    destruct (g x).
    + destruct (t =? t0); auto_false.
      injection H as. subst. constructor.
    + injection H as. subst. repeat constructor. intros [].
  - intros t d H. injection H as. subst. repeat constructor. intros [].
  - intros g [] d H; auto_false.
    destruct (context_check g t0 e1) eqn:E1, (context_check g t1 e2) eqn:E2;
    auto_false.
    apply IHe1 in E1. apply IHe2 in E2. apply merge_spec in H. unpack. auto.
  - intros [] d H; auto_false.
    destruct (mixed_context_check t0 e1); auto_false.
    destruct (mixed_context_check t1 e2); auto_false.
    apply merge_spec in H. unpack. assumption.
  - intros g t0 d H'. destruct (split _); auto_false.
    destruct (t0 =? t'); auto_false.
    fold mixed_context_check in H'.
    destruct (mixed_context_check t e) eqn:E; auto_false.
    destruct l as [| [e0 e0'] l].
    + apply remove_all_well_formed1 in H'. assumption.
    + fold first_pattern_context_check in H'.
      destruct (first_pattern_context_check g t t' e0 e0') eqn:Ef;
      auto_false.
      destruct (inclusionb c _), (ortho_check t l0); auto_false.
      destruct (forallb _ l), (forallb _ (dom c)); auto_false.
      injection H' as. subst.
      repeat unfold first_pattern_context_check,
        Checks.first_pattern_context_check in Ef.
      destruct (context_check [] t e0) eqn:Ec; auto_false.
      apply IHe in E. eapply H in Ec; simpl; eauto.
      eapply H0 in Ef; simpl; eauto.
  - intros t0 d H'. destruct (split _); auto_false.
    destruct (t0 =? t'); auto_false.
    fold mixed_context_check in H'.
    destruct (mixed_context_check t e) eqn:E; auto_false.
    destruct l as [| [e0 e0'] l].
    + destruct (well_formed_check c); auto_false.
      injection H' as. subst. apply IHe in E. assumption.
    + fold first_pattern_context_check in H'.
      destruct (first_pattern_context_check [] t t' e0 e0') eqn:Ef; auto_false.
      destruct (inclusionb c _), (ortho_check t l0); auto_false.
      destruct (forallb _ l), (forallb _ (dom c)); auto_false.
      injection H' as. subst.
      unfold first_pattern_context_check,
        Checks.first_pattern_context_check in Ef.
      destruct (context_check [] t e0) eqn:Ec; auto_false.
      apply IHe in E. eapply H in Ec; simpl; eauto.
      eapply H0 in Ef; simpl; eauto.
  - intros t d H. destruct (mixed_context_check t e1) eqn:E1; auto_false.
    destruct (mixed_context_check t e2) eqn:E2; auto_false.
    destruct (disjointb _ _) eqn:Ed; auto_false.
    injection H as. subst. apply well_formed_app.
    apply disjointb_true in Ed. apply IHe1 in E1. apply IHe2 in E2.
    splits; assumption.
  - intros g t d H. destruct (t =? bit); auto_false.
    apply IHe in H. assumption.
  - intros t d H. destruct (t =? bit); auto_false.
    apply IHe in H. assumption.
  - intros g t d H. destruct (t =? _); auto_false.
    apply IHe in H. assumption.
  - intros t d H. destruct (t =? _); auto_false.
    apply IHe in H. assumption.
  - intros g t d H. destruct (t =? _); auto_false.
    apply IHe in H. assumption.
  - intros t d H. destruct (t =? _); auto_false.
    apply IHe in H. assumption.
  - intros g t0 d H. destruct (context_check [] t e1); auto_false.
    destruct (pure_type_check [] c e2); auto_false.
    + destruct (t0 =? t1); auto_false.
      apply IHe3 in H. assumption.
    + fold mixed_type_check in H.
      destruct (mixed_type_check _ e2); discriminate.
  - intros t0 d H. destruct (context_check [] t e1); auto_false.
    destruct (pure_type_check [] c e2); auto_false.
    + destruct (t0 =? t1); auto_false.
      apply IHe3 in H. assumption.
    + fold mixed_type_check in H.
      destruct (mixed_type_check _ e2); auto_false.
      destruct (t0 =? t1); auto_false.
      apply IHe3 in H. assumption.
  - intros g t0 d H. destruct (context_check [] t e2); auto_false.
    destruct (t0 =? t); auto_false.
    apply IHe1 in H. assumption.
  - intros t0 d H. destruct (context_check [] t e2); auto_false.
    destruct (t0 =? t); auto_false.
    apply IHe1 in H. assumption.
Qed.

Lemma partition_context_not_In :
  forall X g g0 g1,
  partition_context X g = (g0, g1) ->
  forall x, In x X -> g1 x = None.
Proof.
  intros X g. induction g as [| [x0 t0] g IH]; simpl.
  - intros g0 g1 H x Hi. injection H as. subst. reflexivity.
  - intros g0 g1 H x Hi. destruct (partition_context X g) as [g0' g1'].
    destruct (mem x0 X) eqn:E0; injection H as; subst; eauto.
    simpl. destruct (x =? x0) eqn:Ex; eauto.
    apply eqb_sound in Ex. subst. apply mem_spec in Hi. congruence.
Qed.

Lemma in_restriction :
  forall g X x t, restriction g X x = Some t -> In x X.
Proof.
  intros g. induction g as [| [x0 t0] g IH]; simpl; auto_false.
  intros X x t H.
  destruct (mem x0 X) eqn:Em; simpls.
  - destruct (x =? x0) eqn:Ex.
    + apply eqb_sound in Ex. subst. apply mem_spec in Em. assumption.
    + eapply IH, H.
  - eapply IH, H.
Qed.

Lemma partition_context_split_perm :
  forall g d g0 g1 d0 d1 c : context,
  well_formed (g ++ d) ->
  well_formed c ->
  partition_context (dom c) g = (g0, g1) ->
  partition_context (dom c) d = (d0, d1) ->
  subcontext c (g ++ d) ->
  Permutation c (g0 ++ d0).
Proof.
  intros. assert (well_formed (g0 ++ d0)).
  { apply partition_context_permutation in H1, H2. rewrite H1, H2 in H.
    repeat rewrite well_formed_app in *. repeat rewrite dom_union in H.
    rewrite disjoint_app0, disjoint_app1 in H. unpack.
    splits; auto. }
  apply NoDup_Permutation; try (eapply NoDup_map_inv; eauto).
  intros [x t]. repeat rewrite <- context_find_Some_In; auto.
  rewrite context_find_app_Some_iff; auto. split; intros; try branches. 
  - apply H3 in H5 as Ha. apply context_find_app_Some in Ha as [H' | H'].
    + left. apply partition_context_permutation in H1 as Hp.
      apply partition_context_not_In with (x:=x) in H1;
      try (apply dom_Some; eauto).
      rewrite well_formed_app in *. unpack.
      rewrite context_find_Some_In in * by assumption.
      rewrite Hp, in_app_iff in H'. destruct H'; auto.
      apply context_find_Some_In in H10; try congruence.
      rewrite Hp in H8. apply well_formed_app in H8. unpack. assumption.
    + right. apply partition_context_permutation in H2 as Hp.
      apply partition_context_not_In with (x:=x) in H2;
      try (apply dom_Some; eauto).
      rewrite well_formed_app in *. unpack.
      rewrite context_find_Some_In in * by assumption.
      rewrite Hp, in_app_iff in H'. destruct H'; auto.
      apply context_find_Some_In in H10; try congruence.
      rewrite Hp in H9. apply well_formed_app in H9. unpack. assumption.
  - apply partition_context_permutation in H1 as Hp.
    apply well_formed_app in H4. unpack.
    rewrite context_find_Some_In in * by assumption.
    destruct (partition_context_restriction (dom c) g) as [g' H'].
    rewrite H' in H1. injection H1 as. subst.
    rewrite <- context_find_Some_In in * by assumption.
    apply in_restriction in H5 as Hr. apply well_formed_app in H.
    unpack. specialize (restriction_subcontext (dom c) H1) as Hx.
    apply Hx in H5. rewrite dom_Some in Hr. destruct Hr as [tn Hn].
    rewrite Hn. f_equal.
    eapply subcontext_no_conflict with (x:=x).
    + apply H3.
    + apply Hn.
    + apply context_find_app_Some_iff; auto.
      apply well_formed_app. splits; assumption.
  - apply partition_context_permutation in H2 as Hp.
    apply well_formed_app in H4. unpack.
    rewrite context_find_Some_In in * by assumption.
    destruct (partition_context_restriction (dom c) d) as [d' H'].
    rewrite H' in H2. injection H2 as. subst.
    rewrite <- context_find_Some_In in * by assumption.
    apply in_restriction in H5 as Hr. apply well_formed_app in H.
    unpack. specialize (restriction_subcontext (dom c) H8) as Hx.
    apply Hx in H5. rewrite dom_Some in Hr. destruct Hr as [tn Hn].
    rewrite Hn. f_equal.
    eapply subcontext_no_conflict with (x:=x).
    + apply H3.
    + apply Hn.
    + apply context_find_app_Some_iff; auto.
      apply well_formed_app. splits; assumption.
Qed.

Lemma pure_check_mixed_check :
  forall e d t,
  pure_type_check [] d e = Some t ->
  mixed_type_check d e = Some t.
Proof.
  intros e. induction e; simpl; auto_false.
  - intros d t H. destruct (well_formed_check d); auto.
    destruct (partition_pair_context _ _ _) as [[[p' p0] p1] |]; auto.
    destruct (pure_type_check [] _ e1) eqn:E1; auto_false.
    apply IHe1 in E1. rewrite E1.
    destruct (pure_type_check [] _ e2) eqn:E2; auto_false.
    apply IHe2 in E2. rewrite E2. assumption.
  - intros d t H. destruct (pure_type_check [] d e) eqn:E; auto_false.
    apply IHe in E. rewrite E.
    destruct (prog_type_check f) as [[] |] eqn:Ef; auto_false.
Qed.

Lemma mixed_type_check_null :
  forall d, mixed_type_check d null = pure_type_check [] d null.
Proof.
  intros []; auto.
Qed.

Lemma type_check_sound :
  forall e,
  (forall g d t, pure_type_check g d e = Some t -> has_pure_type g d e t) /\
  (forall g t d, context_check g t e = Some d -> has_pure_type g d e t) /\
  (forall d t, mixed_type_check d e = Some t -> has_mixed_type d e t) /\
  (forall t d, mixed_context_check t e = Some d -> has_mixed_type d e t).
Proof.
  intros e.
  induction e using expr_prog_ind
    with (Pf := fun f =>
                forall t, prog_type_check f = Some t -> has_prog_type f t);
  simpl; try splits 4; auto_false.
  - intros g d t H. destruct (well_formed_check g) eqn:Ew, d; auto_false.
    injection H as. subst. constructor. apply well_formed_check_sound, Ew.
  - intros g t d H. destruct t, (well_formed_check g) eqn:Ew; auto_false.
    injection H as. subst. constructor. apply well_formed_check_sound, Ew.
  - intros [] t H; auto_false.
    injection H as. subst. repeat constructor.
  - intros [] d H; auto_false.
    injection H as. subst. repeat constructor.
  - intros g d t H.
    destruct (well_formed_check g) eqn:Eg; auto_false.
    apply well_formed_check_sound in Eg.
    destruct d as [| [x' t'] []]; auto_false.
    + apply has_type_find_cvar; assumption.
    + destruct (x =? x') eqn:Ee, (g x) eqn:Ex; auto_false.
      apply eqb_sound in Ee. injection H as. subst. constructor; assumption.
  - intros g t d H.
    destruct (well_formed_check g) eqn:Ew; auto_false.
    apply well_formed_check_sound in Ew. destruct (g x) eqn:E; auto_false.
    + destruct (t =? t0) eqn:Et; auto_false.
      apply eqb_sound in Et. injection H as. subst.
      apply has_type_find_cvar; assumption.
    + injection H as. subst. constructor; assumption.
  - intros [| [x0 t0] []] t H; auto_false.
    destruct (x =? x0) eqn:E; auto_false.
    apply eqb_sound in E. injection H as. subst.
    repeat constructor.
  - intros t d H. injection H as. subst. repeat constructor.
  - intros g d t H.
    destruct (well_formed_check (g ++ d)) eqn:Ew; auto_false.
    apply well_formed_check_sound in Ew.
    destruct (partition_pair_context _ _ d) as [[[d' d0] d1] |] eqn:Ed;
    auto_false.
    destruct (pure_type_check g (d' ++ d0) e1) eqn:E0; auto_false.
    destruct (pure_type_check g (d' ++ d1) e2) eqn:E1; auto_false.
    apply partition_pair_context_sound, partition_pair_context_perm in Ed.
    rewrite Ed. injection H as. subst. rewrite Ed in Ew. constructor.
    + assumption.
    + apply IHe1 in E0. apply E0.
    + apply IHe2 in E1. apply E1.
  - intros g [] d H; auto_false.
    destruct (context_check g t0 e1) eqn:E0; auto_false.
    destruct (context_check g t1 e2) eqn:E1; auto_false.
    apply IHe1 in E0. apply IHe2 in E1.
    apply merge_spec in H as Hw. unpack. subst.
    apply merge_perm in H as [d' [d0 [d1 [H [H0' H1']]]]]. rewrite <- H.
    constructor.
    + apply well_formed_app. apply pure_typed_well_formed in E0, E1. rewrite H.
      rewrite well_formed_app in *.
      rewrite <- dom_nodupb_comm, nodupb_equiv, dom_union, disjoint_app1.
      tauto.
    + rewrite H0'. assumption.
    + rewrite H1'. assumption.
  - intros d t H. destruct (well_formed_check d) eqn:Ew; auto_false.
    destruct (partition_pair_context _ _ d) as [[[d' d0] d1] |] eqn:Ep;
    auto_false.
    destruct (mixed_type_check _ e1) eqn:E1; auto_false.
    destruct (mixed_type_check _ e2) eqn:E2; auto_false.
    injection H as. subst. apply well_formed_check_sound in Ew.
    apply IHe1 in E1. apply IHe2 in E2.
    apply partition_pair_context_sound, partition_pair_context_perm in Ep.
    rewrite Ep. apply has_mixed_type_pair; auto.
    rewrite <- Ep. assumption.
  - intros [] d H; auto_false.
    destruct (mixed_context_check t0 e1) eqn:E1; auto_false.
    destruct (mixed_context_check t1 e2) eqn:E2; auto_false.
    apply IHe1 in E1. apply IHe2 in E2.
    apply merge_spec in H as Hm.
    apply merge_perm in H as [d' [d0 [d1 [H [H0 H1]]]]].
    unpack. subst.
    rewrite <- H. apply has_mixed_type_pair.
    + rewrite H. assumption.
    + rewrite H0. assumption.
    + rewrite H1. assumption.
  - intros g d t0 H'.
    destruct (partition_context _ d) as [d0 d'] eqn:Ed.
    destruct (split l) as [ej ej'] eqn:Es.
    destruct (partition_context _ g) as [g0 g1] eqn:Ep.
    fold mixed_type_check in H'. fold pattern_type_check in H'.
    destruct (well_formed_check _) eqn:Ew, (mixed_type_check _ e) eqn:Em;
    auto_false.
    apply well_formed_check_sound in Ew.
    apply IHe in Em.
    destruct (Some t1 =? Some t) eqn:Et; auto_false.
    apply eqb_sound in Et. injection Et as. subst.
    destruct (ortho_check t ej) eqn:Eo; auto_false.
    apply ortho_check_sound in Eo.
    destruct (forallb _ _) eqn:Ef; auto_false.
    destruct (forallb _ (dom _)) eqn:Ee; auto_false.
    injection H' as. subst.
    apply partition_context_permutation in Ep as Hp. rewrite Hp.
    apply partition_context_permutation in Ed as Hp'. rewrite Hp'.
    apply pattern_check_pattern_list in Ef as El.
    apply not_None_Some in El as [l' Hf].
    apply split_map_fst in Es as E1. apply split_map_snd in Es. subst.
    apply pattern_list_without_contexts in Hf as Hw. subst.
    constructor; auto.
    + unfold compose. rewrite <- map_map. assumption.
    + intros gj e0 e0' Hi. eapply H.
      * apply in_map with (f:=fst) in Hi. apply Hi.
      * eapply pattern_list_has_contexts in Hi; eauto.
    + intros gj e0 e0' Hi. eapply context_check_has_pure_type in Ef; eauto.
      eapply H0 in Ef.
      * rewrite app_assoc. assumption.
      * apply in_map with (f:=fst) in Hi. apply Hi.
    + intros x Hi. unfold compose. rewrite <- map_map.
      apply erases_check_sound.
      rewrite forallb_forall in Ee. apply Ee. assumption.
  - intros g t0 d Hd.
    destruct (split _) as [ej ej'] eqn:Ej.
    destruct (t0 =? t') eqn:Et; auto_false.
    fold mixed_context_check in Hd. fold first_pattern_context_check in Hd.
    fold pattern_context_check in Hd.
    destruct (mixed_context_check t e) eqn:Em; auto_false.
    apply eqb_sound in Et. subst.
    apply IHe in Em.
    apply split_map_fst in Ej as E1. apply split_map_snd in Ej. subst.
    destruct l as [| [e0 e0'] l].
    + apply remove_all_Permutation2 in Hd as Hp.
      destruct Hp as [g0 [g1 [Hg Hp]]]. rewrite Hg. 
      replace d with (d ++ []) by apply app_nil_r.
      set (l := [] : list (expr * expr * context)).
      replace [] with (map fst l) by reflexivity. constructor; auto_false.
      * simpl. autorewrite with list.
        apply remove_all_well_formed in Hd. rewrite app_assoc, <- Hg. apply Hd.
      * rewrite <- Hp. assumption.
      * apply ortho_nil.
      * intros. apply erases_nil.
    + destruct (first_pattern_context_check g t t' e0 e0') eqn:Ef; auto_false.
      destruct (inclusionb c _) eqn:Ei, (ortho_check t _) eqn:Eo; auto_false.
      destruct (forallb _ l) eqn:Ea, (forallb _ (dom c)) eqn:Ec; auto_false.
      apply ortho_check_sound in Eo.
      injection Hd as. subst.
      unfold first_pattern_context_check,
        Checks.first_pattern_context_check in Ef.
      destruct (context_check [] t e0) eqn:Et; auto_false.
      eapply H in Et; simpl; eauto.
      eapply H0 in Ef; simpl; eauto.
      destruct (partition_context (dom c) g) as [g0 g1] eqn:Eg.
      apply partition_context_permutation in Eg as Hg. rewrite Hg.
      destruct (partition_context (dom c) d) as [d0 d1] eqn:Ed.
      apply partition_context_permutation in Ed as Hd. rewrite Hd.
      fold pattern_type_check in Ea.
      apply pattern_check_pattern_list in Ea as H'.
      apply not_None_Some in H' as [l' H'].
      apply pattern_list_without_contexts in H' as Ho. subst.
      replace (e0 =>> e0') with (fst (e0, e0', c0)) in * by reflexivity.
      rewrite <- map_cons in *. rewrite map_map in Eo.
      fold (compose (A:=expr*expr*context) fst fst) in Eo.
      constructor; auto.
      * apply pure_typed_well_formed in Ef.
        rewrite Permutation_app_comm, app_assoc, well_formed_app in Ef. unpack.
        rewrite Permutation_app_comm in H2. rewrite Hg in H2.
        apply partition_context_permutation in Ed.
        rewrite Hd in H2. rewrite <- app_assoc in H2. assumption.
      * apply inclusionb_subcontext in Ei. unpack.
        rewrite <- partition_context_split_perm; eauto.
      * intros gj ek ek' [Hq | Hi]; try (injection Hq as; subst; apply Et).
        eapply H, pattern_list_has_contexts; eauto.
        right. apply in_map_iff. exists (ek, ek', gj). split; auto.
        reflexivity.
      * rewrite Hg, Hd, <- app_assoc in Ef.
        intros gj ek ek' [Hq | Hi]; try (injection Hq as; subst; apply Ef).
        assert (In (ek =>> ek') (map fst l')).
        { apply in_map_iff. exists (ek, ek', gj). auto. }
        destruct (H0 ek ek'); simpl; auto.
        rewrite app_assoc, <- Hg, <- Hd.
        eapply context_check_has_pure_type in Hi; eauto.
      * intros x Hi. rewrite forallb_forall in Ec.
        destruct (partition_context_restriction (dom c) d) as [d1' H1].
        rewrite H1 in Ed. injection Ed as. subst.
        apply dom_Some in Hi as [ti Ht]. apply in_restriction in Ht.
        apply Ec, erases_check_sound in Ht. unfold compose. rewrite <- map_map.
        assumption.
  - intros d t0 H'. constructor.
    destruct (partition_context _ d) as [d0 d'] eqn:Ed.
    destruct (split l) as [ej ej'] eqn:Es.
    fold mixed_type_check in H'. fold pattern_type_check in H'.
    destruct (well_formed_check _) eqn:Ew, (mixed_type_check _ e) eqn:Em;
    auto_false.
    apply well_formed_check_sound in Ew.
    apply IHe in Em.
    destruct (Some t1 =? Some t) eqn:Et; auto_false.
    apply eqb_sound in Et. injection Et as. subst.
    destruct (ortho_check t ej) eqn:Eo; auto_false.
    apply ortho_check_sound in Eo.
    destruct (forallb _ _) eqn:Ef; auto_false.
    destruct (forallb _ (dom _)) eqn:Ee; auto_false.
    injection H' as. subst.
    apply partition_context_permutation in Ed as Hp'. rewrite Hp'.
    apply pattern_check_pattern_list in Ef as El.
    apply not_None_Some in El as [l' Hf].
    apply split_map_fst in Es as E1. apply split_map_snd in Es. subst.
    apply pattern_list_without_contexts in Hf as Hw. subst.
    replace ([]) with ([] ++ [] : context) by reflexivity. constructor; auto.
    + unfold compose. rewrite <- map_map. assumption.
    + intros gj e0 e0' Hi. eapply H.
      * apply in_map with (f:=fst) in Hi. apply Hi.
      * eapply pattern_list_has_contexts in Hi; eauto.
    + intros gj e0 e0' Hi. eapply context_check_has_pure_type in Ef; eauto.
      eapply H0 in Ef.
      * rewrite app_assoc. assumption.
      * apply in_map with (f:=fst) in Hi. apply Hi.
    + intros x Hi. unfold compose. rewrite <- map_map.
      apply erases_check_sound.
      rewrite forallb_forall in Ee. apply Ee. assumption.
  - intros t0 d Hd. constructor.
    destruct (split _) as [ej ej'] eqn:Ej.
    destruct (t0 =? t') eqn:Et; auto_false.
    fold mixed_context_check in Hd. fold first_pattern_context_check in Hd.
    fold pattern_context_check in Hd.
    destruct (mixed_context_check t e) eqn:Em; auto_false.
    apply eqb_sound in Et. subst.
    apply IHe in Em.
    apply split_map_fst in Ej as E1. apply split_map_snd in Ej. subst.
    destruct l as [| [e0 e0'] l].
    + destruct (well_formed_check c) eqn:Ew; auto_false.
      apply well_formed_check_sound in Ew. injection Hd as. subst.
      replace [] with ([] ++ [] : context) by apply app_nil_r.
      replace d with (d ++ []) by apply app_nil_r.
      set (l := [] : list (expr * expr * context)).
      replace [] with (map fst l) by reflexivity. constructor; auto_false.
      * simpl. autorewrite with list. assumption.
      * apply ortho_nil.
      * intros. apply erases_nil.
    + destruct (first_pattern_context_check [] t t' e0 e0') eqn:Ef; auto_false.
      destruct (inclusionb c _) eqn:Ei, (ortho_check t _) eqn:Eo; auto_false.
      destruct (forallb _ l) eqn:Ea, (forallb _ (dom c)) eqn:Ec; auto_false.
      apply ortho_check_sound in Eo.
      injection Hd as. subst.
      unfold first_pattern_context_check,
        Checks.first_pattern_context_check in Ef.
      destruct (context_check [] t e0) eqn:Et; auto_false.
      eapply H in Et; simpl; eauto.
      eapply H0 in Ef; simpl; eauto.
      destruct (partition_context (dom c) d) as [d0 d1] eqn:Ed.
      apply partition_context_permutation in Ed as Hd. rewrite Hd.
      fold pattern_type_check in Ea.
      apply pattern_check_pattern_list in Ea as H'.
      apply not_None_Some in H' as [l' H'].
      apply pattern_list_without_contexts in H' as Ho. subst.
      replace (e0 =>> e0') with (fst (e0, e0', c0)) in * by reflexivity.
      rewrite <- map_cons in *. rewrite map_map in Eo.
      fold (compose (A:=expr*expr*context) fst fst) in Eo.
      replace [] with ([] ++ [] : context) by reflexivity.
      constructor; auto.
      * apply pure_typed_well_formed in Ef.
        rewrite Permutation_app_comm, app_assoc, well_formed_app in Ef. unpack.
        simpls. autorewrite with list in *.
        rewrite <- Hd. assumption.
      * apply inclusionb_subcontext in Ei. unpack.
        replace d with ([] ++ d) in H3 by reflexivity.
        rewrite <- partition_context_split_perm; eauto.
        reflexivity.
      * intros gj ek ek' [Hq | Hi]; try (injection Hq as; subst; apply Et).
        eapply H, pattern_list_has_contexts; eauto.
        right. apply in_map_iff. exists (ek, ek', gj). split; auto.
        reflexivity.
      * rewrite Hd in Ef.
        intros gj ek ek' [Hq | Hi]; try (injection Hq as; subst; apply Ef).
        assert (In (ek =>> ek') (map fst l')).
        { apply in_map_iff. exists (ek, ek', gj). auto. }
        destruct (H0 ek ek'); simpl; auto.
        unpack. rewrite <- Hd.
        eapply context_check_has_pure_type in Hi; eauto.
        apply H2, Hi.
      * intros x Hi. rewrite forallb_forall in Ec.
        destruct (partition_context_restriction (dom c) d) as [d1' H1].
        rewrite H1 in Ed. injection Ed as. subst.
        apply dom_Some in Hi as [ti Ht]. apply in_restriction in Ht.
        apply Ec, erases_check_sound in Ht. unfold compose. rewrite <- map_map.
        assumption.
  - intros d t H. destruct (partition_context _ d) as [d1 d2] eqn:Ep.
    destruct (disjointb _ _) eqn:Ed; auto_false.
    destruct (mixed_type_check d1 e1) eqn:E1; auto_false.
    destruct (mixed_type_check d2 e2) eqn:E2; auto_false.
    destruct (t0 =? t1) eqn:Et; auto_false.
    apply eqb_sound in Et. injection H as. subst.
    apply partition_context_permutation in Ep. rewrite Ep.
    apply disjointb_true in Ed. apply IHe1 in E1. apply IHe2 in E2.
    apply has_type_try; assumption.
  - intros t d H. destruct (mixed_context_check t e1) eqn:E1; auto_false.
    destruct (mixed_context_check t e2) eqn:E2; auto_false.
    destruct (disjointb _ _) eqn:Ed; auto_false.
    injection H as. subst.
    apply IHe1 in E1. apply IHe2 in E2. apply disjointb_true in Ed.
    apply has_type_try; assumption.
  - intros g d t H.
    destruct (pure_type_check g d e) eqn:E,
      (prog_type_check f) as [[] |] eqn:Ef;
    auto_false.
    destruct (t0 =? t1) eqn:Et; auto_false.
    apply eqb_sound in Et. injection H as. subst.
    apply IHe in E.
    eapply has_pure_type_app; eauto.
  - intros g t d H. destruct (prog_type_check f) as [[] |] eqn:E; auto_false.
    destruct (t =? t') eqn:Et; auto_false.
    apply IHe in H. apply eqb_sound in Et. subst.
    eapply has_pure_type_app; eauto.
  - intros d t H. destruct (mixed_type_check d e) eqn:E; auto_false.
    destruct (prog_type_check f) as [[] |] eqn:Ef; auto_false;
    destruct (t0 =? t1) eqn:Et; auto_false;
    apply eqb_sound in Et; injection H as; subst; apply IHe in E;
    eapply has_mixed_type_app; eauto using has_prog_type.
  - intros t d H. destruct (prog_type_check f) as [[] |] eqn:E; auto_false;
    destruct (t =? t') eqn:Et; auto_false;
    apply IHe in H; apply eqb_sound in Et; subst;
    eapply has_mixed_type_app; eauto using has_prog_type.
  - intros t Ht. injection Ht as. subst. eauto using has_prog_type.
  - intros t Ht. injection Ht as. subst. eauto using has_prog_type.
  - intros t Ht. injection Ht as. subst. eauto using has_prog_type.
  - intros t' Ht. destruct (context_check [] t e1) eqn:E1; auto_false.
    destruct (pure_type_check [] c e2) eqn:E2.
    + injection Ht as. subst. 
      apply IHe1 in E1. apply IHe2 in E2. eauto using has_prog_type.
    + fold mixed_type_check in Ht. clear E2.
      destruct (mixed_type_check _ e2) eqn:E2; auto_false.
      injection Ht as. subst. apply IHe2 in E2. apply IHe1 in E1.
      eauto using has_channel_type_restriction.
  - intros [t0 t1 | t0 t1]; destruct (context_check [] t e) eqn:E; auto_false.
    intros H. injection H as. subst. apply IHe in E. eauto using has_prog_type.
Qed.

Theorem pure_type_check_sound :
  forall g d e t,
  pure_type_check g d e = Some t ->
  has_pure_type g d e t.
Proof.
  intros g d e t H. apply type_check_sound in H. assumption.
Qed.

Theorem mixed_type_check_sound :
  forall d e t,
  mixed_type_check d e = Some t ->
  has_mixed_type d e t.
Proof.
  intros d e t H. apply type_check_sound in H. assumption.
Qed.

Theorem prog_type_check_sound :
  forall f t,
  prog_type_check f = Some t ->
  has_prog_type f t.
Proof.
  intros f t H.
  destruct f; simpls; auto_false; try (injection H as; subst; constructor).
  destruct (context_check [] t0 e) eqn:E; auto_false.
  apply type_check_sound in E.
  destruct (pure_type_check [] c e') eqn:Ep.
  - apply type_check_sound in Ep. injection H as. subst.
    apply has_coherent_type_abs with (d:=c); assumption.
  - fold mixed_type_check in H.
    destruct (mixed_type_check (restriction c (free_vars e')) e') eqn:Em;
    auto_false.
    apply type_check_sound in Em. injection H as. subst.
    destruct (partition_context_restriction (free_vars e') c) as [d' H'].
    apply partition_context_permutation in H'.
    apply has_channel_type_abs
      with (d:=restriction c (free_vars e')) (d0:=d');
    auto.
    rewrite <- H'. assumption.
  - destruct (context_check [] t0 e) eqn:E; auto_false.
    injection H as. subst. apply type_check_sound in E.
    econstructor. apply E.
Qed.

(*
Print Assumptions pure_type_check_sound.
Print Assumptions mixed_type_check_sound.
Print Assumptions prog_type_check_sound.
 *)

Module Completeness.

  Conjecture ortho_check_complete :
    forall t l, ortho t l -> ortho_check t l = true.

  Conjecture erases_check_complete :
    forall x t l, erases x t l -> erases_check x t l = true.

  Conjecture pure_type_check_complete :
    forall g d e t, has_pure_type g d e t -> pure_type_check g d e = Some t.

  Conjecture mixed_type_check_complete :
    forall d e t, has_mixed_type d e t -> mixed_type_check d e = Some t.

  Conjecture pure_prog_type_check_complete :
    forall f t t', 
    has_prog_type f (t ~> t') ->
    prog_type_check f = Some (t ~> t').

  Conjecture mixed_prog_type_check_complete :
    forall f t t', 
    has_prog_type f (t ==> t') ->
    ~ has_prog_type f (t ~> t') ->
    prog_type_check f = Some (t ==> t').

End Completeness.

