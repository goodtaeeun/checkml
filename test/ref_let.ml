let ref_example () =
  let x = ref 42 in
  Printf.printf "The value of x is: %d\n" !x

let () = ref_example ()
