(* 
open Stdlib
open Symtab
open Openqasm

type type0 = Void | Qunit | Superpos of type0 * type0 | Joint of type0 * type0

(* Base types for type checking *)
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
  | Lambda of expr list * type0 * expr
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

type subcircuit = {
  name : string;
  input_name : string;
  input_size : int;
  output_name : string;
  output_size : int;
  prep_name : string;
  prep_size : int;
  flag_name : string;
  flag_size : int;
  garbage_name : string;
  garbage_size : int;
}

let compile (x : expr_types) : Openqasm.directive list =
  let default_program_header = [ Version (2, 0); Include "qelib.inc" ] in
  let rec compile_expr (e : expr) : subcircuit =
    match e with
    (* Generate a gate def and then add ancilla which are passed to the oracle instantiation? *)
    | Lambda (vars, input_t, body) -> failwith ""
    | Apply (f, x) ->
        let compiled_x = compile_expr x in
        let compiled_f = compile_expr f in
        failwith "TODO"
    | Ctrl (arg, arg_t, branches, out_t) -> failwith ""
    | U3 (f1, f2, f3) -> failwith "TODO"
    | _ -> failwith "TODO"
  in
  default_program_header
  @ match x with Expr e -> [] | _ -> failwith "Bad typing?"

(* create output module interface -  *)

(* Test driver *)
let x = compile (Expr zero)
let basic = Apply (had, zero)
let compiled_basic = Expr basic |> compile

(* note: f is a classical oracle
   f: B -> B *)
let deutsch f =
  Apply
    ( had,
      Apply
        ( Lambda
            ( [ Var "x" ],
              qubit,
              Ctrl
                ( Apply (f, Var "x"),
                  qubit,
                  [ (zero, Var "x"); (one, Apply (gphase qubit pi, Var "x")) ],
                  qubit ) ),
          Apply (had, zero) ) )
          *)