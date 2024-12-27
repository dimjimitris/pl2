let rec f (f : int) : int = f in
let g : int -> int = (fun (g : int) -> g) in
f 5 + g 5