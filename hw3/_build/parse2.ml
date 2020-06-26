type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production

type item = symbol * symbol list * symbol list
type state = item BatSet.t
type state_num = (state, int) BatMap.t
type edge = ((int * symbol),  int) BatMap.t
type automata = state_num * edge

type action = S of string | R of string | G of string | A of string
type table = ((int*symbol), (action*int) BatSet.t) BatMap.t

type first = (symbol, symbol BatSet.t) BatMap.t
type follow = (symbol, symbol BatSet.t) BatMap.t

let string_of_symbol: symbol-> string
=fun a -> match a with
| T str -> str
| N str -> str
| Epsilon -> "Epsilon"
| End -> "End"

let string_of_action: (action * int)-> string
=fun (a, n) -> match a with
| S str -> str ^ string_of_int n
| R str -> str ^ string_of_int n
| G str -> str ^ string_of_int n
| A str -> str ^ string_of_int n

let string_of_set set =
"{" ^ (BatSet.fold (fun s str -> str ^ string_of_symbol s ^",") set "" ) ^ "}"

let string_of_parsing_set set =
"{" ^ (BatSet.fold (fun s str -> str ^ string_of_action s ^",") set "" ) ^ "}"

let string_of_list list =
List.fold_left (fun str s -> str ^ string_of_symbol s ^ "") "" list

let string_of_item (s, s_l, s_l') =
 "(" ^ string_of_symbol s ^ "->" ^ string_of_list s_l ^ "." ^ string_of_list s_l' ^ ")"

let string_of_state set = 
"{" ^ BatSet.fold (fun s str -> str ^ string_of_item s ^",") set "" ^ "}"

let print_edge (n,s) n' =
print_endline (string_of_int n ^ "," ^ string_of_symbol s ^ " -> " ^ string_of_int n')


let update_set : symbol -> (symbol, symbol BatSet.t) BatMap.t-> symbol BatSet.t
= fun symbol map ->
match symbol with 
| End -> BatSet.empty
| Epsilon -> BatSet.singleton symbol
| T str -> BatSet.singleton symbol
| N str -> 
    let checked_set = BatMap.find_default BatSet.empty symbol map in
    match BatSet.is_empty checked_set with
    |true -> BatSet.empty
    |false -> BatMap.find symbol map


let rec update_map : (symbol * symbol list) -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
= fun (s, s_l) map ->
let old_set = BatMap.find_default BatSet.empty s map in
match s_l with
| [] -> BatMap.add s (BatSet.union old_set (update_set Epsilon map)) map
| hd::tl ->  
    let tmp_set = update_set hd map in
        if BatSet.mem Epsilon tmp_set then 
        let removed_Epsilon_set = BatSet.remove Epsilon tmp_set in
        let updated_map = BatMap.add s (BatSet.union old_set removed_Epsilon_set) map in
        update_map (s, tl) updated_map
        else BatMap.add s (BatSet.union old_set tmp_set) map


let rec fixed_first : production -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
 = fun prod map -> 
    let updated_map = List.fold_left (fun map (s, s_l) -> update_map (s,s_l) map) map prod in
    if BatMap.equal (fun val1 val2 -> BatSet.equal val1 val2) updated_map map then updated_map
    else fixed_first prod updated_map
   
let get_FIRST: cfg -> (symbol, symbol BatSet.t) BatMap.t
= fun cfg ->
let (n_l,t_l,_,production) = cfg in
let init_map = BatMap.empty in
let init_map = List.fold_left (fun map t -> BatMap.add t (BatSet.singleton t) map) init_map t_l in
let init_map = List.fold_left (fun map nt -> BatMap.add nt (BatSet.empty) map) init_map n_l in
fixed_first production init_map


let rec get_FIRST_string: symbol list-> (symbol, symbol BatSet.t) BatMap.t -> symbol BatSet.t -> symbol BatSet.t
= fun list first set->
match list with
| [] -> BatSet.add Epsilon set 
| hd::tl -> 
let tmp_set = BatMap.find hd first in
if BatSet.mem Epsilon tmp_set then 
    let new_set = BatSet.union (BatSet.remove Epsilon tmp_set) set in
    get_FIRST_string tl first new_set
else BatSet.union tmp_set set


let rec make_follow_by_first: (symbol * symbol list) -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
= fun (s, s_l) first follow ->
if List.length s_l <2 then follow
else  
    let hd = List.hd s_l in
    let tl = List.tl s_l in
    match hd with
    | N str -> 
        let old_set = BatMap.find_default BatSet.empty hd follow in
        let first_set = get_FIRST_string tl first BatSet.empty in
        let removed_Epsilon_set = BatSet.remove Epsilon first_set in
        let updated_follow = BatMap.add hd (BatSet.union removed_Epsilon_set old_set) follow in
        make_follow_by_first (s, tl) first updated_follow 
    | _ -> make_follow_by_first (s, tl) first follow

let rec update_follow : (symbol * symbol list) -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
= fun (s, s_l) first follow -> 
    let len = List.length s_l in
    if len = 0 then follow
    else if len = 1 then 
        let hd = List.hd s_l in
        match hd with
        | N str -> BatMap.add hd (BatSet.union (BatMap.find_default BatSet.empty hd follow) (BatMap.find_default BatSet.empty s follow)) follow
        | _ -> follow
    else
        let hd = List.hd s_l in
        let tl = List.tl s_l in
        match hd with
        | N str -> 
            let first_set = get_FIRST_string tl first BatSet.empty in
            if BatSet.mem Epsilon first_set then 
                let updated_follow = BatMap.add hd (BatSet.union (BatMap.find_default BatSet.empty hd follow) (BatMap.find_default BatSet.empty s follow)) follow in update_follow (s, tl) first updated_follow
            else update_follow (s, tl) first follow
        | _ -> update_follow (s, tl) first follow


let rec fixed_follow1 : production -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t-> (symbol, symbol BatSet.t) BatMap.t
 = fun prod first follow -> 
    let updated_map = List.fold_left (fun map (s, s_l) -> make_follow_by_first (s, s_l) first map ) follow prod in
    if BatMap.equal (fun val1 val2 -> BatSet.equal val1 val2) updated_map follow then updated_map
    else fixed_follow1 prod first updated_map

let rec fixed_follow2 : production -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t-> (symbol, symbol BatSet.t) BatMap.t
 = fun prod first follow -> 
    let updated_map = List.fold_left (fun map (s, s_l) -> update_follow (s, s_l) first map) follow prod in
    if BatMap.equal (fun val1 val2 -> BatSet.equal val1 val2) updated_map follow then updated_map
    else fixed_follow2 prod first updated_map


let get_FOLLOW: cfg -> (symbol, symbol BatSet.t) BatMap.t-> (symbol, symbol BatSet.t) BatMap.t
= fun cfg first->
let (n_l,t_l,s,production) = cfg in
let init_map = BatMap.empty in
let init_map = List.fold_left (fun map nt -> BatMap.add nt (BatSet.empty) map) init_map n_l in
let init_map = BatMap.add s (BatSet.singleton End) init_map in
let updated_map = fixed_follow1 production first init_map in
fixed_follow2 production first updated_map



(* find productions such that symbol -> symbol list *)
let find_prod: symbol -> cfg -> (symbol * symbol list) BatSet.t
=fun symbol cfg ->
let set = BatSet.empty in
let (_, _, _, p_l) = cfg in
List.fold_left (fun acc prod ->
    let (s, s_l) = prod in
    if s = symbol then BatSet.add prod acc
    else acc) set p_l


let closure: state -> cfg -> state
=fun state cfg ->
let (n_l, _, _, p_l) = cfg in
BatSet.fold (fun i acc1 -> 
    let (sym, s_l, s_l') = i in
    match s_l' with 
    | [] -> acc1
    | hd :: tl  -> 
    if List.mem hd n_l then 
        let prod_set = find_prod hd cfg in (* find all related prods *)
        (* print_endline("this is related prod set of " ^ string_of_symbol hd ^ ": ");
        BatSet.iter (fun (s, s_l)-> print_endline(string_of_symbol s ^ " -> " ^ string_of_list s_l)) prod_set; *)
        BatSet.fold (fun (s, s_l) acc2 -> 
            let tmp_item =  (s ,[],s_l) in
            BatSet.add tmp_item acc2) prod_set acc1
    else acc1) state state 


let rec fixed_closure: state->cfg->state
= fun state cfg ->
let result = closure state cfg in
(* print_endline("this is temp state");
BatSet.iter (fun item -> print_item item) result; *)
if BatSet.equal result state then result
else fixed_closure result cfg



let goto: state -> symbol -> cfg -> state
= fun state symbol cfg ->
let tmp_state = BatSet.empty in
let j = BatSet.fold (fun i acc -> 
    let (s, s_l, s_l') = i in
    match s_l' with 
    | [] -> acc
    | hd :: tl -> 
    if hd = symbol then 
         let new_item = (s , s_l@(hd::[]), tl) in BatSet.add new_item acc
    else acc
   ) state tmp_state in fixed_closure j cfg

(*add new state to cfg*)
let update_cfg: cfg -> cfg
= fun cfg ->
let (n_l, t_l, start, p_l) = cfg in
let new_start = N "A'"  in
let n_l = new_start :: n_l in
let p_l = (new_start,start::[]) :: p_l in
let start = new_start in (n_l, t_l, start, p_l)


(*get state I0 *)
let init_closure: cfg -> state
= fun cfg ->
let (_, _, _, p_l) = cfg in
let (s,s_l) = List.hd p_l in
let init = BatSet.add (s,[],s_l) BatSet.empty in
fixed_closure init cfg


let automata: (automata * int) -> cfg -> (automata * int)
= fun (automata, num) cfg ->
let (state_set, edge) = automata in
BatMap.foldi (fun state i ((state_set, edge), num)->
    BatSet.fold (fun item ((cur_state_set, cur_edge), cur_num)->  
    let (s, s_l, s_l') = item in
    match s_l' with 
    | [] -> ((cur_state_set, cur_edge), cur_num)
    | hd :: tl ->
    let new_state = goto state hd cfg in
    (*if j already exists *)
    if BatMap.mem new_state cur_state_set then 
        (*check if edge exists *)
        if BatMap.mem (i, hd) cur_edge then ((cur_state_set, cur_edge), cur_num)
        else 
        let cur_state_num = BatMap.find new_state cur_state_set in
        let new_edge = BatMap.add (i, hd) cur_state_num cur_edge in
            ((cur_state_set, new_edge), cur_num)
    else  (*if j does not exist, then add new state and new edge*)
        let new_state_set = BatMap.add new_state (cur_num+1) cur_state_set in
        let new_edge = BatMap.add (i, hd) (cur_num+1) cur_edge in
            ((new_state_set, new_edge), (cur_num+1))
    ) state ((state_set, edge), num) ) state_set (automata, num)


let rec make_automata: (automata*int) -> cfg -> (automata * int)
= fun (am, num) cfg ->
let (new_am, new_num) = automata (am,num) cfg in
let (new_state_set, new_edge) = new_am in
let (state_set, edge) = am in
if BatMap.equal (fun m1 m2 -> m1 = m2) new_state_set state_set && BatMap.equal (fun m1 m2 -> m1 = m2) new_edge edge
    then (new_am, new_num)
else make_automata (new_am,new_num) cfg


let get_automata: cfg -> (automata * int)
 = fun cfg ->
 let cfg = update_cfg cfg in
 let init_state = init_closure cfg in
 let state_map = BatMap.add init_state 0 BatMap.empty in
 let edge = BatMap.empty in
 make_automata ((state_map,edge),0) cfg


(* add accept condition*)
 let add_accept: table -> table
 =fun table ->
    let old_set = BatMap.find_default BatSet.empty (1, End) table in
    let new_set = BatSet.add (A "a", 0) old_set in
    BatMap.add (1, End) new_set table
 

(* using original cfg, make follow *)
(* add reduce n *)
let parse_by_follow: cfg -> int -> state_num -> table -> table
= fun cfg from state_map table ->
let first = get_FIRST cfg in
let follow = get_FOLLOW cfg first in
let (_, _, _, p_l) = cfg in
let item_set = BatMap.filterv (fun value -> value=from) state_map in
BatMap.foldi (fun state i acc1-> 
   BatSet.fold (fun item acc -> 
    let (s, s_l, s_l') = item in
    match s_l' with 
    |[] -> 
        let rec find_idx : int -> production -> int
        = fun idx prod ->
        match prod with 
        | [] -> idx
        | hd :: tl -> 
            if hd = (s,s_l) then idx
            else find_idx (idx+1) tl in
        let idx = find_idx 1 p_l in
        let y_set = BatMap.find_default BatSet.empty s follow in
        (***********************debugging *********************)
        (* print_endline ("rule is " ^ string_of_symbol s^ " -> " ^ string_of_list s_l ^" "^ string_of_int idx);
        print_endline( "follow set" ^ string_of_symbol s ^ ":" ^ string_of_set y_set); *)
        (***********************debugging *********************)
        BatSet.fold (fun y acc2 -> 
        let old_set = BatMap.find_default BatSet.empty (from,y) acc2 in
        BatMap.add (from,y) (BatSet.add (R"r",idx) old_set) acc2) y_set acc
    | _ -> acc
    ) state acc1 ) item_set table


 let parsing_table: cfg -> automata -> table
 = fun cfg automata -> 
 let table = BatMap.empty in
 let (state_num , edge) = automata in
 (***************debugging*************)
 (* print_endline("this is state map");
 BatMap.iter (fun key value -> print_endline (string_of_int value ^ ":" ^string_of_state key)) state_num; *)
 (***************debugging*************)
 let table = BatMap.foldi (fun key j acc ->
    let (from, symbol) = key in
    match symbol with
    | T str -> 
        let old_set = BatMap.find_default BatSet.empty (from, symbol) acc in
        let new_set = BatSet.add (S "s",j) old_set in
        BatMap.add (from,symbol) new_set acc
    | N str -> 
        let old_set = BatMap.find_default BatSet.empty (from, symbol) acc in
        let new_set = BatSet.add (G "g",j) old_set in
        BatMap.add (from,symbol) new_set acc
    | _ -> acc
    ) edge table in
    let table = BatMap.foldi (fun key value acc -> parse_by_follow cfg value state_num acc
    ) state_num table in add_accept table
 

let get_parsing_table: cfg -> table
= fun cfg ->
let (automata, num) = get_automata cfg in
parsing_table cfg automata

let rec list_pop: int list -> int -> int list
= fun list num ->
if num = 0 then list
else 
    list_pop (List.tl list) (num-1)


let rec do_parse: cfg -> (int list * symbol list ) -> bool
= fun cfg (stack , sentence) ->
let table = get_parsing_table cfg in
let (_, _,_, p_l) = cfg in
match sentence with 
    | [] -> false
    | hd :: tl ->
    let top = List.hd stack in
    let res_set = BatMap.find_default BatSet.empty (top,hd) table in
    if BatSet.is_empty res_set then false
    else 
        let ((act, num),_) = BatSet.pop res_set in
        match act with 
        | S str -> 
            let stack = num :: stack in
            do_parse cfg (stack, tl)
        | R str -> 
            let (s, s_l) = List.nth p_l (num-1) in (* get the rule k *)
            let cnt = List.length s_l in (* get the length of right side of rule k *)
            let pop_stack = list_pop stack cnt in (* pop stack as many times as the number of symbols *)
            let top = List.hd pop_stack in
            let tmp_res_set = BatMap.find_default BatSet.empty (top,s) table in
            let ((_, tmp_num),_) = BatSet.pop tmp_res_set in (* get goto n *)
            let push_stack = tmp_num :: pop_stack in (* push n to the stack *)
            do_parse cfg (push_stack,sentence)
        | A str -> true
        | _ -> true

   
let check_SLR : cfg -> bool
=fun cfg -> 
let (automata, num) = get_automata cfg in
let (state_set, edge) = automata in 
BatMap.iter (fun key value -> print_endline(string_of_int value ^ ":" ^ string_of_state key)) state_set; 
BatMap.iter (fun (n,s) n' -> print_edge (n,s) n') edge;
let parsing_table = get_parsing_table cfg in
(***********************debugging *********************)
BatMap.iter (fun (from, symbol) value -> 
print_endline (string_of_int from ^ "," ^ string_of_symbol symbol ^ ":" ^ string_of_parsing_set value )) parsing_table;
(***********************debugging *********************)
BatMap.foldi (fun key value acc ->
if BatSet.cardinal value > 1 then acc && false
else acc) parsing_table true


let parse : cfg -> symbol list -> bool
=fun cfg sentence -> 
do_parse cfg ([0], sentence)