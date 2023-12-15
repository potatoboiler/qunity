open Stdlib
(* open Hardcaml *)

(**
    https://diskuv.github.io/dkml-dune-dsl/dkml-dune-dsl/index.html
    https://discuss.ocaml.org/t/any-tutorial-on-designing-edsl-in-ocaml/10781
    https://okmij.org/ftp/ML/#DSLs
    https://gist.github.com/polytypic/08929bfe060f9cafe0d45f2b4ebf9f38 -- discusses the general typing scheme I need to impl in OCaml
    https://github.com/o1-labs/snarky
    *)

open Symtab
open Openqasm

(* Base types for type checking *)
type type0 = Void | Qunit | Superpos of type0 * type0 | Joint of type0 * type0

type expr =
  | Null
  | Var of string
  | Qpair of expr * expr
  | Ctrl of expr * type0 * (expr * expr) list * type0
  | Try of expr * expr
  | Apply of expr * expr (* originally prog * expr *)
  | U3 of float * float * float
  | Left of type0 * type0
  | Right of type0 * type0
  | Lambda of expr * type0 * expr
  (* | Rphase of type0 * expr * float * float *)
  | Rphase of type0 * float * float (* gate only *)

type expr_types = Expr of expr | Foo of float * float

let qubit = Superpos (Qunit, Qunit)
let tab = Symtab.empty

(* Constants *)
let pi = Float.pi
let zero = Left (Qunit, Qunit)
let one = Right (Qunit, Qunit)
let had = U3 (pi /. 2., 0., pi)

(* Sugar *)
(* let gphase t gamma x = Rphase (t, x, gamma, gamma) *)
let gphase t gamma = Rphase (t, gamma, gamma)

(* Compilation code *)
let typecheck : expr_types -> (unit, string) result = fun _ -> failwith "TODO"

let compile : expr_types -> Openqasm.directive list =
 fun x ->
  let default_program_header = [ Version (2, 0); Include "qelib.inc" ] in
  let compile_expr e =
    match e with
    | Lambda _ -> failwith ""
    | Apply _ -> failwith ""
    | _ -> failwith "TODO"
  in
  default_program_header
  @ match x with Expr e -> compile_expr e | _ -> failwith "Bad typing?"

(* Test driver *)
let x = compile (Expr zero)
let basic = Apply (had, zero)

(* note: f is a classical oracle
   f: B -> B *)
let deutsch f =
  Apply
    ( had,
      Apply
        ( Lambda
            ( Var "x",
              qubit,
              Ctrl
                ( Apply (f, Var "x"),
                  qubit,
                  [ (zero, Var "x"); (one, Apply (gphase qubit pi, Var "x")) ],
                  qubit ) ),
          Apply (had, zero) ) )

(* Create simple cnot using hardcaml *)
(* Qunity only supports ctrl, try/except, etc., and phasing.*)
