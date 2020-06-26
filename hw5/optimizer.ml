(********** Make control flow graph *************)
module IntSet = Set.Make(
        struct 
            type t = int
            let compare = compare
        end
)

type block = int
type cfg_map = (block, IntSet.t) PMap.t
type block_map = (block, T.linstr) PMap.t

(*update block number*)
let block_num = ref 0
let new_block_num() = block_num:= !block_num +1; !block_num

let make_block : T.program -> (block_map * T.label)
= fun t ->
    List.fold_left (fun (acc_map, acc) list -> 
        let (lb, instr) = list in
            match instr with
            | T.SKIP -> (acc_map, lb)
            | _ -> 
                let num = new_block_num() in
                if acc > -1 then 
                    let new_list = (acc, instr) in (PMap.add num new_list acc_map, -1)
                else (PMap.add num list acc_map, -1)
    ) (PMap.empty,-1) t

let find_label : block_map -> T.label -> int
= fun blocks label ->
    PMap.foldi (fun block_num linstr acc -> 
        let (lb, instr) = linstr in
            if label = lb then block_num 
            else acc
        ) blocks 0

let make_cfg : block_map -> cfg_map
= fun blocks ->
    let cfg = PMap.empty in
    PMap.foldi (fun key value acc -> 
        let (label, instr) = value in
        let block_set = IntSet.add (key+1) IntSet.empty in
             match instr with 
            | T.UJUMP next -> 
                let next_block = find_label blocks next in
                let block_set = IntSet.add next_block block_set in PMap.add key block_set acc
            | T.CJUMP (_,next) -> 
                let next_block = find_label blocks next in
                let block_set = IntSet.add next_block block_set in PMap.add key block_set acc
            | T.CJUMPF (_,next) -> 
                let next_block = find_label blocks next in
                let block_set = IntSet.add next_block block_set in PMap.add key block_set acc   
            | _ -> PMap.add key block_set acc 
        ) blocks cfg

(* Liveness Analysis *)
module LA = struct 

    module VarSet = Set.Make(
        struct 
            type t = T.var
            let compare = compare
        end
    )

    type in_map = (int, VarSet.t) PMap.t
    type out_map = (int, VarSet.t) PMap.t
    type def_map = (int, VarSet.t) PMap.t
    type use_map = (int, VarSet.t) PMap.t

    let get_def_use : block_map -> (def_map * use_map)
    = fun blocks ->
        let (defs, uses) = (PMap.empty, PMap.empty) in
        PMap.foldi (fun key value (acc1, acc2) -> 
            let (label, instr) = value in
            let def_set = VarSet.empty and use_set = VarSet.empty in
                match instr with 
                | T.ALLOC (var, _) -> (* x = alloc(n) *)
                    let def_set = VarSet.add var def_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.ASSIGNV (var1, _, var2, var3) -> (* x = y bop z *)
                    let def_set = VarSet.add var1 def_set in
                    let use_set = VarSet.add var2 use_set in
                    let use_set = VarSet.add var3 use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.ASSIGNC (var1, _, var2, _) -> (* x = y bop n *)
                    let def_set = VarSet.add var1 def_set in
                    let use_set = VarSet.add var2 use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.ASSIGNU (var1, _, var2) ->  (* x = uop y *)
                    let def_set = VarSet.add var1 def_set in
                    let use_set = VarSet.add var2 use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)    
                | T.COPY (var1, var2) -> (* x = y *)
                    let def_set = VarSet.add var1 def_set in
                    let use_set = VarSet.add var2 use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.COPYC (var, _) -> (* x = n *)
                    let def_set = VarSet.add var def_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.UJUMP _ -> (* goto L *)
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)                               
                | T.CJUMP (var, _) ->      (* if x goto L *)
                    let use_set = VarSet.add var use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.CJUMPF (var, _) ->      (* ifFalse x goto L *)
                    let use_set = VarSet.add var use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.LOAD (var, arr) ->        (* x = a[i] *)
                    let (a,i) = arr in
                    let def_set = VarSet.add var def_set in
                    let use_set = VarSet.add i use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.STORE (arr, var) ->       (* a[i] = x *)
                    let (a,i) = arr in
                    let def_set = VarSet.add i def_set in
                    let use_set = VarSet.add var use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.READ var ->             (* read x *)
                    let use_set = VarSet.add var use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | T.WRITE var  ->            (* write x *)
                    let use_set = VarSet.add var use_set in
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
                | _ ->
                    (PMap.add key def_set acc1, PMap.add key use_set acc2)
            ) blocks (defs, uses)


(* constant analysis*)
module CA = struct 

    module VarSet = Set.Make(
        struct 
            type t = T.var
            let compare = compare
        end
    )

    type domain = 
        | BOT 
        | TOP 
        | CON of int

    type abs_map = (T.var, domain) PMap.t

    type in_map = (int, abs_map) PMap.t
    type out_map = (int, abs_map) PMap.t

    let join : domain -> domain -> domain
    = fun d1 d2 -> match d1 with
        | TOP -> (match d2 with
            | TOP -> TOP
            | CON i -> TOP 
            | BOT -> BOT)
        | CON i -> (match d2 with
            | TOP -> TOP
            | CON j -> 
                if i = j then CON i
                else TOP
            | BOT -> BOT)
        | _ -> BOT 

    let order : domain -> domain -> domain
     = fun d1 d2 -> match d1 with
        | TOP -> (match d2 with
            | TOP -> TOP
            | CON i -> CON i 
            | BOT -> BOT)
        | CON i -> (match d2 with
            | TOP -> CON i
            | CON j -> CON j
            | BOT -> CON i)
        | BOT -> (match d2 with
            | TOP -> BOT
            | CON i -> CON i 
            | BOT -> BOT)


    let transfer : T.instr -> abs_map -> abs_map
    = fun instr abs ->
        match instr with
        | T.ASSIGNV (var1, _, var2, var3) -> (* x = y bop z *)
            let d2 = 
                if PMap.mem var2 abs then PMap.find var2 abs
                else TOP in
            let abs =  PMap.add var2 d2 abs in
            let d3 = 
                if PMap.mem var3 abs then PMap.find var3 abs
                else TOP in
            let abs =  PMap.add var3 d3 abs in
            let order_domain = order d2 d3 in
            let d1 = 
                if PMap.mem var1 abs then order (PMap.find var1 abs) order_domain
                else order TOP order_domain in
            PMap.add var1 d1 abs
        | T.ASSIGNC (var1, _, var2, num) -> (* x = y bop n *)
            let d2 = 
                if PMap.mem var2 abs then PMap.find var2 abs
                else TOP in
            let abs =  PMap.add var2 d2 abs in
            let d1 = 
                if PMap.mem var2 abs then order (PMap.find var2 abs) d2
                else order TOP d2 in 
            PMap.add var1 d1 abs 
        | T.ASSIGNU (var1, _, var2) ->  (* x = uop y *)
            let d2 = 
                if PMap.mem var2 abs then PMap.find var2 abs
                else TOP in
            let abs =  PMap.add var2 d2 abs in
            let d1 = 
                if PMap.mem var2 abs then order (PMap.find var2 abs) d2
                else order TOP d2 in
            PMap.add var1 d1 abs    
        | T.COPY (var1, var2) -> (* x = y *)
            let d2 = 
                if PMap.mem var2 abs then PMap.find var2 abs
                else TOP in
            let abs =  PMap.add var2 d2 abs in
            let d1 = 
                if PMap.mem var2 abs then order (PMap.find var2 abs) d2
                else order TOP d2 in
            PMap.add var1 d1 abs
        | T.COPYC (var, num) -> (* x = n *)
            let d1 = CON num in PMap.add var d1 abs
        | _ -> abs      

let find_t : block_map -> string -> IntSet.t 
= fun blocks str ->
    PMap.foldi (fun key value acc -> 
        let (lb, instr) = value in
            match instr with
            | T.COPY (var1, var2) ->
                if String.equal var2 str then IntSet.add key acc
                else acc
            |_ -> acc) blocks IntSet.empty

let constant_folding : block_map -> block_map 
= fun blocks ->
    PMap.foldi (fun key value acc -> 
        let (label, instr) = value in
            match instr with 
            | T.COPYC (var, i) -> 
                if (String.get var 0) == 't' then 
                    let related_block = find_t acc var in
                    let acc = PMap.add key (label, T.SKIP) acc in
                    IntSet.fold (fun set acc2 -> 
                        (* let (n_lb, T.instr (v1, v2)) = PMap.find set acc2 in
                        PMap.add set (n_lb, T.COPYC (v1, i)) acc2  *)
                    ) related_block acc
                else acc
            |_ -> acc) blocks blocks

    

let optimize : T.program -> T.program
=fun t -> 
    (************** this is for debugging******************)
    let (blocks, label) = make_block t in
    let cfg = make_cfg blocks in t
    



(*
let optimize : T.program -> T.program
=fun t -> t (* TODO *)
*)