module Deutsch where

import Prelude qualified

data Positive
  = XI Positive
  | XO Positive
  | XH

data Z
  = Z0
  | Zpos Positive
  | Zneg Positive

data Ascii0
  = Ascii
      Prelude.Bool
      Prelude.Bool
      Prelude.Bool
      Prelude.Bool
      Prelude.Bool
      Prelude.Bool
      Prelude.Bool
      Prelude.Bool

data String
  = EmptyString
  | String0 Ascii0 String

data Real
  = Pi
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

data Type
  = Void
  | Qunit
  | Superpos Type Type
  | Joint Type Type

data Expr
  = Null
  | Var String
  | Qpair Expr Expr
  | Ctrl Expr Type (([]) ((,) Expr Expr)) Type
  | Try Expr Expr
  | Apply Prog Expr

data Prog
  = U3 Real Real Real
  | Left Type Type
  | Right Type Type
  | Lambda Expr Type Expr
  | Rphase Type Expr Real Real

x :: String
x =
  String0
    ( Ascii
        Prelude.False
        Prelude.False
        Prelude.False
        Prelude.True
        Prelude.True
        Prelude.True
        Prelude.True
        Prelude.False
    )
    EmptyString

zero :: Expr
zero =
  Apply (Left Qunit Qunit) Null

one :: Expr
one =
  Apply (Right Qunit Qunit) Null

had :: Prog
had =
  U3 (Div Pi (Const (Zpos (XO XH)))) (Const Z0) Pi

gphase :: Type -> Real -> Prog
gphase t gamma =
  Rphase t (Var x) gamma gamma

deutsch :: Prog -> Expr
deutsch f =
  Apply
    had
    ( Apply
        ( Lambda
            (Var x)
            (Superpos Qunit Qunit)
            ( Ctrl
                (Apply f (Var x))
                (Superpos Qunit Qunit)
                ( (:)
                    ((,) zero (Var x))
                    ((:) ((,) one (Apply (gphase (Superpos Qunit Qunit) Pi) (Var x))) ([]))
                )
                (Superpos Qunit Qunit)
            )
        )
        (Apply had zero)
    )
