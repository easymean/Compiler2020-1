open Regex

exception Not_implemented

type state = int
type states = state BatSet.t
type set_of_states = states BatSet.t
let alphabet_set = BatSet.add B (BatSet.singleton A) 

(*return new nfa with init state and final states *)
let make_base () = 
  let new_nfa = Nfa.create_new_nfa () in
  let (final, new_nfa) = Nfa.create_state new_nfa in
  Nfa.add_final_state new_nfa final


(*return only one final state *)
let get_final_state: Nfa.t -> Nfa.state
= fun nfa -> List.hd (BatSet.elements (Nfa.get_final_states nfa))

(*return (init, one final state) *)
let get_is_final : Nfa.t -> (Nfa.state * Nfa.state)
= fun t -> (Nfa.get_initial_state t, get_final_state t)


(* unit two nfa and return t1*)
let unit_nfas: (Nfa.t * Nfa.t) -> Nfa.t
= fun (t1, t2)->
  let t1 = Nfa.add_states t1 (Nfa.get_states t2) in
  let t1 = Nfa.add_edges t1 (Nfa.get_edges t2) in
  let (is_t1, is_t2) = (Nfa.get_initial_state t1, Nfa.get_initial_state t2) in
  let t1 = Nfa.add_epsilon_edge t1 (is_t1, is_t2) in
  Nfa.add_epsilon_edge t1 (get_final_state t2, get_final_state t1)


let or_compiler : (Nfa.t * Nfa.t) -> Nfa.t
=fun (t1, t2) ->
  let or_nfa = make_base() in 
  let connect_t1 = unit_nfas (or_nfa, t1) in unit_nfas (connect_t1, t2)


let concat_compiler : (Nfa.t * Nfa.t) -> Nfa.t
= fun (t1, t2) ->
  let nfa = make_base() in 
  let (is, final) = get_is_final nfa and 
  (is_t1, final_t1)= get_is_final t1 and 
  (is_t2, final_t2)= get_is_final t2 and
  states_t1_t2 = BatSet.union (Nfa.get_states t1) (Nfa.get_states t2) in
  let (edges_t1,edges_t2 ) = (Nfa.get_edges t1, Nfa.get_edges t2) in 
  let nfa = Nfa.add_states nfa states_t1_t2 in 
  let nfa = Nfa.add_edges nfa edges_t1 in
  let nfa = Nfa.add_edges nfa edges_t2 in
  let nfa = Nfa.add_epsilon_edge nfa (is, is_t1) in
  let nfa = Nfa.add_epsilon_edge nfa (final_t1, is_t2) in
  Nfa.add_epsilon_edge nfa (final_t2, final)

  

let star_compiler : Nfa.t -> Nfa.t
= fun t ->
  let (is, final) = get_is_final t in
  let new_nfa = Nfa.add_epsilon_edge t (final, is) in
  let base_nfa = make_base() in 
  let (new_is, new_final) = (Nfa.get_initial_state base_nfa, get_final_state base_nfa) in
  let star_nfa = unit_nfas (base_nfa, new_nfa) in
  Nfa.add_epsilon_edge star_nfa (new_is, new_final)


let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
  let nfa = make_base () in
  let init = Nfa.get_initial_state nfa in
  let final = get_final_state nfa in
  match regex with
  | Empty -> nfa
  | Epsilon -> 
    Nfa.add_epsilon_edge nfa (init, final)
  | Alpha a ->
    Nfa.add_edge nfa (init, a, final)
  | OR (t1, t2) ->
    or_compiler (regex2nfa t1, regex2nfa t2)
  | CONCAT (t1, t2) -> concat_compiler (regex2nfa t1, regex2nfa t2)
  | STAR (t) -> star_compiler (regex2nfa t)


let rec epsilon_closure : Nfa.t -> Nfa.states -> Dfa.state
= fun nfa states ->
  let next_epsilon_states = BatSet.empty in
  let next_epsilon_states = BatSet.fold (fun state acc
  -> BatSet.union acc (Nfa.get_next_state_epsilon nfa state)) states next_epsilon_states in
  if BatSet.is_empty next_epsilon_states then states
  else BatSet.fold (fun state acc
  -> BatSet.union (epsilon_closure nfa next_epsilon_states) acc) next_epsilon_states states


(* get union state set which is input of epsilon_closure*)
let input_for_epsilon_closure : Nfa.t -> Dfa.state -> alphabet -> Dfa.state
= fun nfa dfa_state a ->
    BatSet.fold (fun nfa_state acc -> 
    BatSet.union (Nfa.get_next_state nfa nfa_state a) acc) dfa_state BatSet.empty
  

(*check whether temp set becomes final state*)
let check_element : Nfa.t -> Dfa.state -> bool
= fun nfa state -> BatSet.mem (get_final_state nfa) state

let rec subset_construction : Nfa.t -> Dfa.t -> Dfa.states -> Dfa.t
= fun nfa dfa w ->
  if BatSet.is_empty w then dfa
  else
    let (hd,tl) = BatSet.pop w in
    let (hd, w, dfa) = BatSet.fold (fun a (q, wset, dfa) -> 
      let union_set = input_for_epsilon_closure nfa hd a in
      let temp_set = epsilon_closure nfa union_set in
      let dfa_t = Dfa.add_state dfa temp_set in
      let dfa_t = Dfa.add_edge dfa_t (hd, a, temp_set) in
      let wset = if dfa_t = dfa then wset
        else BatSet.add temp_set wset in
      let result = check_element nfa temp_set in
      let dfa_t =  match result with
        | false -> dfa_t
        | true -> Dfa.add_final_state dfa_t temp_set
      in (q, wset, dfa_t)) alphabet_set (hd, tl, dfa) in
      subset_construction nfa dfa w

  

let nfa2dfa : Nfa.t -> Dfa.t
=fun nfa -> 
  let init_state_dfa = epsilon_closure nfa (BatSet.singleton (Nfa.get_initial_state nfa)) in
  let dfa = Dfa.create_new_dfa init_state_dfa in
  let dfa_is = Dfa.get_initial_state dfa in
  let result = check_element nfa dfa_is in
    let dfa =  match result with
      | false -> dfa
      | true -> Dfa.add_final_state dfa dfa_is in
  let w = BatSet.singleton dfa_is in
  match BatSet.is_empty w with
  | true -> dfa
  | false -> 
    let dfa = subset_construction nfa dfa w
    in dfa  


(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa


let get_next: Dfa.t -> alphabet list -> Dfa.state
=fun dfa str -> 
  let start = Dfa.get_initial_state dfa in
  List.fold_left (fun a l -> Dfa.get_next_state dfa a l) start str


let run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa str -> 
  let result = get_next dfa str in
  Dfa.is_final_state dfa result 
  
