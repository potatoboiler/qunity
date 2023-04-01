From Coq Require Import String ZArith.
From Qunity Require Import Reals Sets Types Syntax Contexts Typing Typechecking.
Import ListNotations QunityNotations Variables.

Local Notation bit := (qunit + qunit).

(* Deutsch's algorithm *)
Definition deutsch f :=
  zero
  |> had
  |> lambda x bit
       (ctrl (x |> f)
           bit [zero =>> x; one =>> (x |> gphase bit pi)] bit)
  |> had.

Proposition qnot_type :
  has_prog_type qnot (bit ~> bit).
Proof.
  apply prog_type_check_sound. reflexivity.
Qed.

Proposition deutsch_type :
  has_mixed_type [] (deutsch qnot) bit.
Proof.
  apply mixed_type_check_sound. reflexivity.
Qed.
