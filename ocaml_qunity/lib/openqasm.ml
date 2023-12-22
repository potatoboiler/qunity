type gate_primitive = [ `X ] 
type operand = [ `QubitOp | `Bit of bool | `QubitRegOp of int | `BitReg of int | gate_primitive ]

type directive =
  | Reset of operand
  | Qubit
  | QubitReg of int
  | Version of int * int
  | Include of string
  | CX of operand
  | U of float * float * float * operand

let convert_to_qasm : directive list -> string list =
  let mappings d = match d with _ -> "" in
  fun ds -> List.map mappings ds
