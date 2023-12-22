open Stdlib
(* open Hardcaml *)

let todo = failwith "TODO"

(**
    https://diskuv.github.io/dkml-dune-dsl/dkml-dune-dsl/index.html
    https://discuss.ocaml.org/t/any-tutorial-on-designing-edsl-in-ocaml/10781
    https://okmij.org/ftp/ML/#DSLs
    https://gist.github.com/polytypic/08929bfe060f9cafe0d45f2b4ebf9f38 -- discusses the general typing scheme I need to impl in OCaml
    https://github.com/o1-labs/snarky
    *)

type qubit_primitive = [ `Qubit | `QubitReg of int | `State ]

type gate_primitive =
  [ `Rphase of float * float
  | `U3 of float * float * float
  | `NamedPrim of string ]

type ast_node =
  [ gate_primitive
  | qubit_primitive
  | `ApplySeq of ast_node list
  | `Prod of ast_node list
  | `Pair of ast_node * ast_node
  | (*| `Apply of gate_construct * ast_node *)
    `Lambda of
    string * qubit_primitive * ast_node
  | `TryCatch of
    ast_node * ast_node
    (* Pair is product unless we have a quantum channel, but we need to think about how to implement this... measurements? *)
  | `Ctrl of (ast_node * ast_node) list ]

(* Create simple cnot using hardcaml *)
(* Qunity only supports ctrl, try/except, etc., and phasing.*)

type wire =
  | Input of qubit_primitive
  | Output of int
  | Connected of string * int
  | Ancilla of int (* ? *)
  | Combined of (wire * int) list

type subcircuit = {
  name : string;
  input : wire list;
  output : wire list;
  prep : wire; (* ancilla input *)
  flag : wire; (* clean ancilla output *)
  garbage : wire; (* dirty output ancilla *)
  operation : string option;
  internals : subcircuit_internals list;
}

and subcircuit_internals =
  | Product of subcircuit_internals list
  | Prim of gate_primitive

type graph = { edges : string Symtab.symtab; nodes : subcircuit Symtab.symtab }

let build_graph (ast : ast_node) : graph =
  let name_counter = ref 0 in
  let wire_counter = ref 0 in
  let rec builder (graph : graph) (ast : ast_node) =
    match ast with
    | `ApplySeq ls ->
        let folder (graph : graph) (ast : ast_node) =
          match ast with
          (* gate_primitive *)
          (* Generate  *)
          | `Rphase (f1, f2) -> todo
          | `U3 (f1, f2, f3) -> todo
          | `NamedPrim s -> todo
          (* rest *)
          | qubit_primitive -> todo
          | _ -> todo
        in
        List.fold_left folder graph ls
    | _ -> todo
  in

  builder { edges = Symtab.empty; nodes = Symtab.empty } ast
(* returns output lists and dependency graph *)
(* pair ( x, y )*)

let rec compile expr =
  (* assumign the expr type checks *)
  let preprocess e = () in
  match expr with _ -> failwith "TODO"

let basic_hadamard_example = `ApplySeq [ `State; `NamedPrim "had" ]

let deutsch_example =
  `ApplySeq
    [ `Qubit; `NamedPrim "had"; `Lambda ("x", `Qubit, []); `NamedPrim "had" ]
(*zero
  |> had
  |> lambda x bit
       (ctrl (x |> f)
           bit [zero =>> x; one =>> (x |> gphase bit pi)] bit)
  |> had.
*)
