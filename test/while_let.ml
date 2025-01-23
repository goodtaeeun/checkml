let while_example () =
  let x = 0 in
  while x < 1 do
    Printf.printf "This will print once since x is always 0.\n";
    exit 0 (* Ensures the while loop stops *)
  done
