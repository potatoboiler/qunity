From Coq Require Import String.
From Qunity Require Import Reals Sets Syntax QList.
Import ListNotations QunityNotations Variables.

(* The Deutsch-Jozsa algorithm *)
Definition deutsch_jozsa n f :=
  let bitarray := array bit n in
  let multiplus := replicate plus n in
  multiplus
    |> lambda x bitarray
         (ctrl (x |> f)
             bit [zero =>> x; one =>> (x |> gphase bit pi)] bitarray)
    |> equals bitarray multiplus.
