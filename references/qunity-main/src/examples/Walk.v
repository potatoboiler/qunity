From Coq Require Import List String Permutation ZArith.
From Qunity Require Import Types Reals Syntax Contexts Typing QList Typechecking.
Import ListNotations QunityNotations Variables.

Open Scope nat_scope.
Open Scope qunity_scope.

Definition reflect t e : prog :=
  rphase t e 0%Z pi.

Definition adj (f : prog) t : prog :=
  lambda (f x) t x.

Definition mat t (l : list (expr * expr)) t' : prog :=
  lambda x t
  (ctrl x t (map (fun '(ej, ej') => (ej =>> #(x, ej'))) l) (t * t')
   |> lambda
       (ctrl x' t' (map (fun '(ej, ej') => (ej' =>> #(ej, x'))) l) (t * t'))
       (t * t') x').

Definition child := bit.
Definition vleft := zero.
Definition vright := one.
Definition coin := maybe child.
Definition cdown := nothing child.
Definition cleft := just child vleft.
Definition cright := just child vright.
Fixpoint vertex n := match n with
                     | 0 => void
                     | S n' => qunit + (vertex n' * child)
                     end.
Definition root n := left qunit (vertex n * child) null.
Definition qcons e n e0 := right qunit (vertex n * child) #(e, e0).
Definition r1 n : expr := qcons (root n) (S n) vleft.
Definition r2 n : expr := root (S n).
Definition leaf n := array child n.

Lemma has_type_qcons :
  forall e n e0,
  has_pure_type [] [] e (vertex n) ->
  has_pure_type [] [] e0 child ->
  has_pure_type [] [] (qcons e n e0) (vertex (S n)).
Proof.
  intros e n e0 H H0. unfold qcons. eapply has_pure_type_app.
  - constructor.
  - replace [] with ([] ++ [] ++ [] : context) at 2 by reflexivity.
    constructor; simpl; auto.
    constructor.
Qed.

Lemma has_type_root :
  forall n, has_pure_type [] [] (root n) (vertex (S n)).
Proof.
  intros n. unfold root. induction n as [| n IH]; simpl; repeat econstructor.
Qed.

(* The fallible "asleaf" projection function *)
Fixpoint asleaf n :=
  match n with
  | 0 => lambda (r1 0) (vertex 2) null
  | S n' => lambda (qcons x (S n) x0) (vertex (2 + n)) #(x0, asleaf n' x)
  end.

Open Scope Z_scope.

Definition u : expr :=
  zero
  |> u3 (2 * arccos (1 / sqrt 3))%real 0 0
  |> lambda x bit
      (ctrl x bit [zero =>> #(x, zero); one =>> #(x, plus)] (bit * bit))
  |> mat (bit * bit)
      [#(zero, zero) =>> cdown; #(one, zero) =>> cleft; #(one, one) =>> cright]
      coin.

Definition u' (n : nat) : expr :=
  zero
  |> u3 (2 * arccos (1 / sqrt (sqrt (Z.of_nat n))))%real 0 0
  |> mat bit [zero =>> cdown; one =>> cleft] coin.

Definition v : string := "v".
Definition v' : string := "v'".
Definition c : string := "c".
Definition l : string := "l".


Definition diffusion n (f : prog) : prog :=
  lambda #(c, v) (coin * vertex (2 + n))
  (ctrl v (vertex (2 + n))
    [ qcons (qcons v' n x) (S n) x' =>>
      ctrl (try (just (leaf n) (qcons (qcons v' n x) (S n) x' |> asleaf n)) (nothing (leaf n)))
          (maybe (leaf n))
          [ nothing (leaf n) =>> #(c |> reflect coin u, v);
            just (leaf n) l =>>
            ctrl (f l) bit
            [zero =>> #(c, v); one =>> #(c, v) |> gphase (coin * vertex (2 + n)) pi]
                (coin * vertex (2 + n)) ]
                (coin * vertex (2 + n));
      r1 n =>> #(c |> reflect coin (u' n), v);
      r2 n =>> #(c, v) ]
      (coin * vertex (2 + n))).

Fixpoint downcast n : prog :=
  match n with
  | O =>
      lambda v (vertex 1) (ctrl v (vertex 1) [] void)
  | S n' =>
      lambda v (vertex (S n))
      (ctrl v (vertex (S n))
       [root n =>> #(v, root n');
        qcons v' n x =>> #(v, qcons (downcast n' v') n' x)]
      (vertex (S n) * vertex n)
       |> lambda (ctrl v (vertex n)
                  [root n' =>> #(root n, v);
                   qcons v' n' x =>> #(qcons (adj (downcast n') (vertex n') v') n x, v)]
                 (vertex (S n) * vertex n))
                 (vertex (S n) * vertex n) v)
  end.

Definition leftchild n : prog :=
  lambda v (vertex n) (downcast n (qcons v n vleft)).

Definition rightchild n : prog :=
  lambda v (vertex n) (downcast n (qcons v n vright)).

Definition nextcoin n : prog :=
  lambda x (coin * vertex (S n))
  (ctrl x (coin * vertex (S n))
    [#(cdown, qcons v n vleft) =>> #(x, cleft);
     #(cdown, qcons v n vright) =>> #(x, cright);
     #(cleft, v) =>> #(x, cdown);
     #(cright, v) =>> #(x, cdown)]
    (coin * vertex (S n) * coin)).

Definition c' : string := "c'".

Definition walk n : prog :=
  lambda x (coin * vertex (S n))
    (nextcoin n x
     |> lambda #(#(c, v), c') (coin * vertex (S n) * coin)
        (ctrl #(c, c') (coin * coin)
         [#(cdown, cleft) =>> #(#(c', adj (leftchild (S n)) (vertex (S n)) v), c);
          #(cdown, cright) =>> #(#(c', adj (rightchild (S n)) (vertex (S n)) v), c);
          #(cleft, cdown) =>> #(#(c', leftchild (S n) v), c);
          #(cright, cdown) =>> #(#(c', rightchild (S n) v), c)]
          (coin * vertex (S n) * coin))
     |> adj (nextcoin n) (coin * vertex (S n) * coin)).

Module Typing.

  Example n : nat := 3.

  Example f : prog := lambda x (leaf n) zero.

  Proposition asleaf_type :
    has_prog_type (asleaf n) (vertex (n + 2) ~> leaf n).
  Proof.
    apply prog_type_check_sound. reflexivity.
  Qed.

  Proposition f_type :
    has_prog_type f (leaf n ==> bit).
  Proof.
    apply prog_type_check_sound. reflexivity.
  Qed.

  Proposition diffusion_type :
    has_prog_type (diffusion n f) (coin * vertex (n + 2) ~> coin * vertex (n + 2)).
  Proof.
    apply prog_type_check_sound. reflexivity.
  Qed.

  Proposition walk_type :
    has_prog_type (walk n) (coin * vertex (S n) ~> coin * vertex (S n)).
  Proof.
    apply prog_type_check_sound. reflexivity.
  Qed.

End Typing.
