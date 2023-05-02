From Qunity Require Import Types Syntax.
Import QunityNotations Variables.

(* Fixed-length array of t *)
Fixpoint array t n :=
  match n with
  | O => qunit
  | S n' => t * array t n'
  end.

(* Repeat an expression n times *)
Fixpoint replicate e n :=
  match n with
  | O => null
  | S n' => #(e, replicate e n')
  end.
