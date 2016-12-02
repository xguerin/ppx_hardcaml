let v0 a b = [%hw a lor  b];;
let v1 a b = [%hw a land b];;
let v2 a b = [%hw a lxor b];;
let v3 a   = [%hw   lnot a];;
