deutsch f :=
  zero
  |> had
  |> lambda x bit
       (ctrl (x |> f)
           bit [zero =>> x; one =>> (x |> gphase bit pi)] bit)
  |> had