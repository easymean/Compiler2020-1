type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production


let string_of_symbol: symbol-> string
=fun a -> match a with
| T str -> str
| N str -> str
| Epsilon -> "Epsilon"
| End -> "End"

let string_of_set set =
"{" ^ (BatSet.fold (fun s str -> str ^ string_of_symbol s ^",") set "" ) ^ "}"

let string_of_list list =
List.fold_left (fun str s -> str ^ string_of_symbol s ^ "") "" list

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



let make_PARSING_TABLE : cfg -> (((symbol * symbol) , (symbol * symbol list)) BatMap.t) * bool
= fun cfg -> 
let (_,_,_,prod_list) = cfg in
let first = get_FIRST cfg in
let follow = get_FOLLOW cfg first in
let parsing_table = BatMap.empty and bool = true in
List.fold_left (fun (map,b) (s, s_l)-> (*fold for production list and acc val is (parsing table,bool) *)
    let first_set = get_FIRST_string s_l first BatSet.empty in
   BatSet.fold (fun s_e (map,b) -> (*fold for first set and acc val is (parsing table,bool) *)
    match s_e with
    | T str ->
        if BatMap.mem (s, s_e) map then (BatMap.add (s,s_e) (s,s_l) map, b&&false)
        else (BatMap.add (s,s_e) (s,s_l) map, b)
    | _ -> (*first set has epsilon*)
        let follow_set = BatMap.find s follow in
        BatSet.fold (fun f_s_e (map,b)-> (*fold for follow set and acc val is (parsing table,bool) *)
        match f_s_e with
         | T str ->
            if BatMap.mem (s,f_s_e) map then (BatMap.add (s,f_s_e) (s,s_l) map, b&&false)
            else (BatMap.add (s,f_s_e) (s,s_l) map, b)
        | _ -> (*follow set has end*)
            if BatMap.mem (s,End) map then (BatMap.add (s,End) (s,s_l) map, b&&false)
            else (BatMap.add (s,End) (s,s_l) map, b)
        ) follow_set (map,b)
    ) first_set (map, b)
) (parsing_table,bool) prod_list
    
 

let do_parsing : cfg -> symbol list -> bool
= fun cfg string ->
let (_, _, s, _) = cfg in
let (parsing_table, res) = make_PARSING_TABLE cfg in
let stack = s::End::[] in
let rec check: symbol list -> symbol list -> bool
= fun string stack ->
    let top = List.hd stack in
    if top = End then true
    else 
        let hd = List.hd string and tl = List.tl string in
        if hd = top then check tl (List.tl stack)
        else 
            match top with
            | T str -> false
            | _ -> 
            if BatMap.mem (top, hd) parsing_table then
                let (_, s_l) = BatMap.find (top, hd) parsing_table in
                check string (s_l @ (List.tl stack))
            else false in
(check string stack)

let check_LL1 : cfg -> bool
=fun cfg ->
let first = get_FIRST cfg in
print_endline("first set");
BatMap.iter (fun key value -> print_endline (string_of_symbol key ^ ":" ^ string_of_set value)) first;
let follow = get_FOLLOW cfg first in
print_endline("follow set");
BatMap.iter (fun key value -> print_endline (string_of_symbol key ^ ":" ^ string_of_set value)) follow;

let (parsing_table, bool) = make_PARSING_TABLE cfg in
bool


let parse : cfg -> symbol list -> bool
=fun cfg sentence -> do_parsing cfg sentence
