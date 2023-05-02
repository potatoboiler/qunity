From Coq Require Import Bool ZArith Reals.
From Qunity Require Import Tactics.

Declare Scope real_scope.
Open Scope real_scope.
Delimit Scope real_scope with real.

Inductive real :=
  | pi
  | euler
  | const : Z -> real
  | negate : real -> real
  | plus : real -> real -> real
  | times : real -> real -> real
  | div : real -> real -> real
  | sin : real -> real
  | cos : real -> real
  | tan : real -> real
  | arcsin : real -> real
  | arccos : real -> real
  | arctan : real -> real
  | exp : real -> real
  | ln : real -> real
  | sqrt : real -> real.

Notation "- r" := (negate r) : real_scope.
Infix "+" := plus : real_scope.
Notation "r1 - r2" := (r1 + (-r2)) : real_scope.
Infix "*" := times : real_scope.
Infix "/" := div : real_scope.

Fixpoint pow r n : real :=
  match n with
  | 0 => const 1
  | S n' => r * pow r n'
  end.

Infix "^" := pow : real_scope.

(* syntactic equality, not semantic *)
#[export]
Instance eqb_real : has_eqb real :=
  fix eqb_real r r' :=
  match r, r' with
  | pi, pi
  | euler, euler =>
      true
  | const n, const n' =>
      Z.eqb n n'
  | -r1, -r1'
  | sin r1, sin r1'
  | cos r1, cos r1'
  | tan r1, tan r1'
  | arcsin r1, arcsin r1'
  | arccos r1, arccos r1'
  | arctan r1, arctan r1'
  | exp r1, exp r1'
  | ln r1, ln r1'
  | sqrt r1, sqrt r1' =>
      eqb_real r1 r1'
  | r1 + r2, r1' + r2'
  | r1 * r2, r1' * r2'
  | r1 / r2, r1' / r2' =>
      eqb_real r1 r1' && eqb_real r2 r2'
  | _, _ =>
      false
  end.

Fixpoint rsem r : R :=
  match r with
  | pi => PI
  | euler => Rtrigo_def.exp 1
  | const n => IZR n
  | - r' => - rsem r'
  | r1 + r2 => rsem r1 + rsem r2
  | r1 * r2 => rsem r1 * rsem r2
  | r1 / r2 => rsem r1 / rsem r2
  | sin r' => Rtrigo_def.sin (rsem r')
  | cos r' => Rtrigo_def.cos (rsem r')
  | tan r' => Rtrigo1.tan (rsem r')
  | arcsin r' => asin (rsem r')
  | arccos r' => acos (rsem r')
  | arctan r' => atan (rsem r')
  | exp r' => Rtrigo_def.exp (rsem r')
  | ln r' => Rpower.ln (rsem r')
  | sqrt r' => R_sqrt.sqrt (rsem r')
  end.

#[export]
Hint Resolve Z.eqb_spec : bdestruct.

Lemma eqb_real_refl :
  forall r, eqb_real r r = true.
Proof.
  induction r; simpl; auto using Z.eqb_refl with bool.
Qed.

#[export]
Instance eqb_real_spec :
  valid_eqb eqb_real.
Proof.
  split; auto using eqb_real_refl.
  intros r.
  induction r; intros [] H; auto_false;
  cbn in *; try rewrite Z.eqb_eq in *; autorewrite with bool in *; unpack;
  subst; f_equal; auto.
Qed.

#[export]
Hint Rewrite eqb_real_refl eqb_real_spec : bool.
