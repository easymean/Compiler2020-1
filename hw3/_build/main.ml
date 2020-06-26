open Parse2

let cfg1 = (
  [N "E"; N "T"; N "F"],
  [T "+"; T "*"; T "("; T ")"; T "id"],
  N "E",
  [
    (N "E", [N "E"; T "+"; N "T"]);
    (N "E", [N "T"]);
    (N "T", [N "T"; T "*"; N "F"]);
    (N "T", [N "F"]);
    (N "F", [T "("; N "E"; T ")"]);
    (N "F", [T "id"])
  ])

let cfg2 = (
  [N "S"; N "L"; N "R"],
  [T "="; T ";"; T "id"; T "*"],
  N "S",
  [
    (N "S", [N "L"; T "="; N "R"; T ";"]);
    (N "S", [N "R"; T ";"]);
    (N "L", [T "id"]);
    (N "L", [T "*"; N "R"]);
    (N "R", [N "L"])
  ]
)

let cfg3 = (
  [N "S"; N "E"],
  [T "a"; T "b"; T "e"; T "i"; T "t"],
  N "S",
  [
   (N "S", [T "i"; N "E"; T "t"; N "S"; T "e"; N "S"]);
   (N "S", [T "i"; N "E"; T "t"; N "S"]);
   (N "S", [T "a"]);
   (N "E", [T "b"])
  ] 
)

let cfg4 = (
  [N "S"; N "E"],
  [T "a"; T "b"; T "e"; T "i"; T "t"; T "{"; T "}"],
  N "S",
  [
   (N "S", [T "i"; N "E"; T "t"; T "{"; N "S"; T "}"; T "e"; T "{"; N "S"; T "}"]);
   (N "S", [T "i"; N "E"; T "t"; T "{"; N "S"; T "}"]);
   (N "S", [T "a"]);
   (N "E", [T "b"])
  ] 
)

(* let cfg1 = (* 4 *) (
  [N "S"; N "V"; N "W"], 
  [T "("; T ")"; T "a"; T "b"; T "c"; T "d"], 
  N "S", 
  [
    (N "S", [T "("; N "S"; T ")"; N "V"; N "W"]); 
    (N "S", [T "a"; N "S"; T "b"; N "V"; N "W"]); 
    (N "S", [T "d"; N "V"; N "W"]); 
    (N "V", [N "V"; T "a"]); 
    (N "V", []); (N "W", [N "W"; T "c"]); (N "W", [])
    ]
  )
let cfg2 = (* 6 *)  ([N "M"; N "L"; N "LC"; N "INT"; N "ID"; N "ID'"; N "STR"; N "WS"; N "WS'"; N "DG"; N "LT"; N "DQ"; N "CHAR"; N "CHAR'"],  [T "("; T ")"; T "\""; T " "; T "\\n"; T "0"; T "1"; T "2"; T "3"; T "4"; T "5"; T "6"; T "7"; T "8"; T "9"; T "a"; T "b"; T "c"; T "d"; T "e"; T "f"; T "g"; T "h"; T "i"; T "j"; T "k"; T "l"; T "m"; T "n"; T "o"; T "p"; T "q"; T "r"; T "s"; T "t"; T "u"; T "v"; T "w"; T "x"; T "y"; T "z"], N "M", [(N "M", [N "WS"; N "INT"; N "WS"]); (N "M", [N "WS"; N "ID"; N "WS"]); (N "M", [N "WS"; N "STR"; N "WS"]); (N "M", [N "WS"; N "L"; N "WS"]); (N "L", [T "("; N "WS"; N "LC"; T ")"]); (N "LC", []); (N "LC", [N "LC"; N "WS'"; N "M"]); (N "INT", [N "INT"; N "DG"]); (N "ID", [N "LT"; N "ID'"]); (N "ID'", []); (N "ID'", [N "ID'"; N "LT"]); (N "ID'", [N "ID'"; N "DG"]); (N "STR", [N "DQ"; N "CHAR"; N "DQ"]); (N "WS", []); (N "WS", [N "WS"; N "WS'"]); (N "WS'", [N "WS'"; T " "]); (N "WS'", [N "WS'"; T "\\n"]); (N "DG", [T "0"]); (N "DG", [T "1"]); (N "DG", [T "2"]); (N "DG", [T "3"]); (N "DG", [T "4"]); (N "DG", [T "5"]); (N "DG", [T "6"]); (N "DG", [T "7"]); (N "DG", [T "8"]); (N "DG", [T "9"]); (N "LT", [T "a"]); (N "LT", [T "b"]); (N "LT", [T "c"]); (N "LT", [T "d"]); (N "LT", [T "e"]); (N "LT", [T "f"]); (N "LT", [T "g"]); (N "LT", [T "h"]); (N "LT", [T "i"]); (N "LT", [T "j"]); (N "LT", [T "k"]); (N "LT", [T "l"]); (N "LT", [T "m"]); (N "LT", [T "n"]); (N "LT", [T "o"]); (N "LT", [T "p"]); (N "LT", [T "q"]); (N "LT", [T "r"]); (N "LT", [T "s"]); (N "LT", [T "t"]); (N "LT", [T "u"]); (N "LT", [T "v"]); (N "LT", [T "w"]); (N "LT", [T "x"]); (N "LT", [T "y"]); (N "LT", [T "z"]); (N "DQ", [T "\""]); (N "CHAR", []); (N "CHAR", [N "CHAR"; N "CHAR'"]); (N "CHAR'", [N "DG"]); (N "CHAR'", [N "LT"]); (N "CHAR'", [T " "])])
let cfg3 = (* 10 *)  (
  [N "S"; N "A"; N "B";], 
  [T "a"; T "b";], 
  N "S", 
  [
    (N "S", [N "A"; T "a"; N "A"; T "b";]); (N "S", [N "B"; T "b"; N "B"; T "a";]); (N "A", []); (N "B", [])
    ]
  )
let cfg4 = (* 13 *)  (
  [N "expr"; N "lvalue"; N "var";], 
  [T "0"; T "1"; T "="; T "f"; T "x"; T "y"; T "*"; T "("; T ")";], 
  N "expr", 
  [
    (N "expr", [T "0"]); 
    (N "expr", [T "1"]); 
    (N "expr", [N "lvalue"]); 
    (N "expr", [N "lvalue"; T "="; N "expr";]); 
    (N "expr", [N "lvalue"; T "("; N "expr"; T ")";]); 
    (N "lvalue", [N "var"]); 
    (N "lvalue", [T "*"; N "lvalue";]); 
    (N "var", [T "f"]); 
    (N "var", [T "x"]); 
    (N "var", [T "y"])
    ]
  )   
let cfg5 = (* 13 *)  (
    [N "S"; N "A"; N "B";], 
    [T "a"; T "b";], 
    N "S", 
    [
      (N "S", [N "A"; T "a"; N "A"; T "b";]); 
      (N "S", [N "B"; T "b"; N "B"; T "a";]); 
      (N "A", []); 
      (N "B", [])
      ]
    )
     *)

let s1 = [T "i"; T "b"; T "t"; T "a"; T "e"; T "{"; T "i"; T "b"; T "t"; T "a"; T "e"; T "a"; T "}"; End]
let s2 = [T "i"; T "b"; T "t"; T "{"; T "a"; T "}"; T "e"; T "{"; T "i"; T "b"; T "t"; T "{"; T "a"; T "}"; T "e"; T "{"; T "a"; T "}"; T "}"; End]
let s3 = [T"id"; T"*";T"id";End]
let cfgs = [cfg1; cfg2; cfg3; cfg4] (* true false false true *)


let main () =
  List.iter (fun cfg ->
    print_endline (string_of_bool (check_SLR cfg))
  ) cfgs;
  print_endline "";
  print_endline (string_of_bool (parse cfg1 s3));
  print_endline (string_of_bool (parse cfg4 s1));
  print_endline (string_of_bool (parse cfg4 s2)) 


let _ = main ()
