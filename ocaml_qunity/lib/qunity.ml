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

(** 
  Given the graph, we try to deduce the wire sizes and indices belongong to each circuit, then we drop into Qiskit
  PyML bindings to generate these based on graph traversal
  pyml to staq?
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
  | Combined of wire list * wire list
(*
  Wire | Gate
  Wire can be a product wire (in/out) / max but the ancillas are always generated independently   
  *)

type wire_op = Had

type subcircuit =
  | Subcircuit of {
      name : string;
      input : wire;
      output : wire;
      prep : wire; (* ancilla input *)
      flag : wire; (* clean ancilla output *)
      garbage : wire; (* dirty output ancilla *)
      operation : string option;
    }
  | Wire of wire

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
          | `U3 (f1, f2, f3) ->
              let subc_name = string_of_int !name_counter in
              let in_wire_name = !wire_counter in
              let out_wire_name = !wire_counter + 1 in
              let () =
                wire_counter := !wire_counter + 1;
                name_counter := !name_counter + 1
              in
              let subc =
                Subcircuit
                  {
                    name = subc_name;
                    input = Connected ("out__" ^ string_of_int in_wire_name, 1);
                    output = Connected ("out__" ^ string_of_int out_wire_name, 1);
                    prep = Ancilla 0;
                    flag = Ancilla 0;
                    garbage = Ancilla 0;
                    operation = None;
                  }
              in
              {
                nodes = graph.nodes |> Symtab.add subc_name subc;
                edges = graph.edges |> Symtab.add "" "";
              }
          | `NamedPrim s -> todo
          (* qubit_primitive *)
          | `Qubit | `QubitReg _ | `State -> todo (* other operations *)
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

(*
https://dl.acm.org/doi/10.1145/3586039 - Modular synthesis (can we describe states on the control gate and have ti auto synthesize for us? )
- we still need to specify sizes, which might be deducible from the inputs
*)