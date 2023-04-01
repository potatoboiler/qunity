From Coq Require Import ZArith List.
From Qunity Require Import Reals Types Syntax Typing Typechecking QList.
Import ListNotations QunityNotations Variables.

Open Scope real_scope.

Definition couple k :=
  lambda #(x0, x1) (bit * bit)
  (ctrl (#(x0, x1) |> qand) bit
   [zero =>> #(x1, x0);
    one =>> (#(x1, x0) |> gphase (bit * bit) (2 * pi / 2 ^ k))]
   (bit * bit)).

Fixpoint rotations n :=
  match n with
  | O =>
      qid qunit
  | S n' =>
      match n' with
      | O => lambda #(x, null) (bit * qunit) #(had x, null)
      | S n'' =>
          lambda #(x0, x) (array bit n)
          (#(x0, x |> rotations n')
           |> lambda #(x0, #(x1, x)) (array bit n)
              #(#(x0, x1) |> couple n, x)
           |> lambda #(#(x0, x1), x) ((bit * bit) * array bit n'')
              #(x0, #(x1, x)))
      end
  end.

(* Quantum fourier transform *)
Fixpoint qft n :=
  match n with
  | O =>
      qid qunit
  | S n' =>
      lambda x (array bit n)
      (x |> rotations n |> lambda #(x0, x) (array bit n) #(x0, x |> qft n'))
  end.

Proposition qft3_type :
  has_prog_type (qft 3) (array bit 3 ~> array bit 3).
Proof.
  apply prog_type_check_sound. reflexivity.
Qed.

