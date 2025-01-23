let x = ref 42
let ref_example () = Printf.printf "The value of x is: %d\n" !x
let () = ref_example ()
