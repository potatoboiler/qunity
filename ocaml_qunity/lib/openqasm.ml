type operand = QubitOp | Bit of bool | QubitRegOp of int | BitReg of int

type directive =
  | Reset of operand
  | Qubit
  | QubitReg of int
  | Version of int * int
  | Include of string

let convert_to_qasm : directive list -> string list =
  let mappings d = match d with _ -> "" in
  fun ds -> List.map mappings ds
