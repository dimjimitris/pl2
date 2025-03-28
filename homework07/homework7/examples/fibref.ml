let prev : ref int = ref 0 in
let curr : ref int = ref 1 in
let rec fib (n : int) : () =
  if n == 0 then ()
  else 
    let temp : int = !curr in 
    let x : () = curr := !prev + !curr in
    let y : () = prev := temp in
    fib (n - 1)
in
let t : () = fib 8 in 
!prev