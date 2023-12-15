open Hardcaml
open Hardcaml.Signal

module I = struct
  type 'a t =
    { clock : 'a
    ; clear : 'a
    ; incr : 'a
    }
  [@@deriving hardcaml]
end

module O = struct
  type 'a t =
    { dout : 'a[@bits 8]
    }
  [@@deriving hardcaml]
end
let create (i : _ I.t) =
    { O.dout =
        reg_fb
          (Reg_spec.create ~clock:i.clock ~clear:i.clear ())
          ~enable:i.incr
          ~width:8
          ~f:(fun d -> d +:. 1)
    }

let circuit = Circuit.create_exn ~name:"test" [ output "b" (input "a" 1) ]
let () = Rtl.print Verilog circuit
let x = Circuit.create_with_interface (module I) (module O) ~name:"clock_example" create
let () = Rtl.print Verilog x