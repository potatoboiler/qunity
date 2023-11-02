open Stdlib
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
  | Apply of prog * expr

and prog =
  | U3 of float * float * float
  | Left of type0 * type0
  | Right of type0 * type0
  | Lambda of expr * type0 * expr
  | Rphase of type0 * expr * float * float

type expr_types = Expr of expr | Prog of prog | Foo of float * float

let tab = Symtab.empty

(* Constants *)
let pi = Float.pi
let zero = Left (Qunit, Qunit)
let one = Right (Qunit, Qunit) (* Convert this to  *)
let had = U3 (pi /. 2., 0., pi)

(* Sugar *)
let gphase t gamma x = Rphase (t, x, gamma, gamma)

(* Compilation code *)
let typecheck : expr_types -> (unit, string) result = fun _ -> failwith "TODO"

let compile : expr_types -> Openqasm.directive list =
 fun x ->
  let compile_expr e = match e with _ -> failwith "TODO"
  and compile_prog p =
    match p with Left (Qunit, Qunit) -> [ Qubit ] | _ -> failwith "TODO"
  in
  [ Version (3, 0); Include "qelib.inc" ]
  @
  match x with
  | Expr e -> compile_expr e
  | Prog p -> compile_prog p
  | _ -> failwith "Bad typing?"

(* Test driver *)
let x = compile (Prog zero)
