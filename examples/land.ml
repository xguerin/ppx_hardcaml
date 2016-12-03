let v0 a b = [%hw a lor  b];;
let v1 a b = [%hw a land b];;
let v2 a b = [%hw a lxor b];;
let v3     = [%hw   lnot a];;

let some_fun a b =
  let i0 = [%hw a lor  b]
  and i1 = [%hw a land b]
  and i2 = [%hw a lxor b]
  and i3 = [%hw   lnot a] in
  [%hw i0 land (i1 land i2) ]

let subscript_fun signal =
  let%hw subsr = signal.[1,2] in
  subsr
