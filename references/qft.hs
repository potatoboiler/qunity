module Qft where

import qualified Prelude

data Nat =
   O
 | S Nat

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

data String =
   EmptyString
 | String0 Ascii0 String

data Real =
   Pi
 | Euler
 | Const Z
 | Negate Real
 | Plus Real Real
 | Times Real Real
 | Div Real Real
 | Sin Real
 | Cos Real
 | Tan Real
 | Arcsin Real
 | Arccos Real
 | Arctan Real
 | Exp Real
 | Ln Real
 | Sqrt Real

pow :: Real -> Nat -> Real
pow r n =
  case n of {
   O -> Const (Zpos XH);
   S n' -> Times r (pow r n')}

data Type =
   Void
 | Qunit
 | Superpos Type Type
 | Joint Type Type

data Expr =
   Null
 | Var String
 | Qpair Expr Expr
 | Ctrl Expr Type (([]) ((,) Expr Expr)) Type
 | Try Expr Expr
 | Apply Prog Expr
data Prog =
   U3 Real Real Real
 | Left Type Type
 | Right Type Type
 | Lambda Expr Type Expr
 | Rphase Type Expr Real Real

x :: String
x =
  String0 (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.True Prelude.True Prelude.False) EmptyString

x0 :: String
x0 =
  String0 (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.True Prelude.True Prelude.False) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.False Prelude.False) EmptyString)

x1 :: String
x1 =
  String0 (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.True Prelude.True Prelude.False) (String0 (Ascii
    Prelude.True Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.False Prelude.False) EmptyString)

bit :: Type
bit =
  Superpos Qunit Qunit

zero :: Expr
zero =
  Apply (Left Qunit Qunit) Null

one :: Expr
one =
  Apply (Right Qunit Qunit) Null

qid :: Type -> Prog
qid t =
  Lambda (Var x) t (Var x)

had :: Prog
had =
  U3 (Div Pi (Const (Zpos (XO XH)))) (Const Z0) Pi

equals :: Type -> Expr -> Prog
equals t e =
  Lambda (Var x) t (Try (Apply (Lambda e t one) (Var x)) zero)

gphase :: Type -> Real -> Prog
gphase t gamma =
  Rphase t (Var x) gamma gamma

qand :: Prog
qand =
  equals (Joint bit bit) (Qpair one one)

array :: Type -> Nat -> Type
array t n =
  case n of {
   O -> Qunit;
   S n' -> Joint t (array t n')}

couple :: Nat -> Prog
couple k =
  Lambda (Qpair (Var x0) (Var x1)) (Joint bit bit) (Ctrl (Apply qand (Qpair
    (Var x0) (Var x1))) bit ((:) ((,) zero (Qpair (Var x1) (Var x0))) ((:)
    ((,) one (Apply
    (gphase (Joint bit bit) (Div (Times (Const (Zpos (XO XH))) Pi)
      (pow (Const (Zpos (XO XH))) k))) (Qpair (Var x1) (Var x0)))) ([])))
    (Joint bit bit))

rotations :: Nat -> Prog
rotations n =
  case n of {
   O -> qid Qunit;
   S n' ->
    case n' of {
     O -> Lambda (Qpair (Var x) Null) (Joint bit Qunit) (Qpair (Apply had
      (Var x)) Null);
     S n'' -> Lambda (Qpair (Var x0) (Var x)) (array bit n) (Apply (Lambda
      (Qpair (Qpair (Var x0) (Var x1)) (Var x)) (Joint (Joint bit bit)
      (array bit n'')) (Qpair (Var x0) (Qpair (Var x1) (Var x)))) (Apply
      (Lambda (Qpair (Var x0) (Qpair (Var x1) (Var x))) (array bit n) (Qpair
      (Apply (couple n) (Qpair (Var x0) (Var x1))) (Var x))) (Qpair (Var x0)
      (Apply (rotations n') (Var x)))))}}

qft :: Nat -> Prog
qft n =
  case n of {
   O -> qid Qunit;
   S n' -> Lambda (Var x) (array bit n) (Apply (Lambda (Qpair (Var x0) (Var
    x)) (array bit n) (Qpair (Var x0) (Apply (qft n') (Var x)))) (Apply
    (rotations n) (Var x)))}

