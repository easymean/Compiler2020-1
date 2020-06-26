let decl_translator: S.decl -> T.program
= fun (typ, id) ->
match typ with 
| S.TINT -> [(0, T.COPYC(id, 0))]
| S.TARR n -> [(0, T.ALLOC(id, n))]

(*update temporary variable*)
let tmp_idx = ref 0
let new_tmp_idx() = tmp_idx:= !tmp_idx +1; !tmp_idx
let get_new_tmp_var : unit -> T.var
= fun () -> 
let new_idx = new_tmp_idx() in 
"t" ^ (string_of_int new_idx)

(*update label*)
let lb_idx = ref 1
let new_lb_idx() = lb_idx:= !lb_idx +1; !lb_idx


(*translate uop*)
let uop_translate: T.uop -> (T.var * T.program) -> (T.var * T.program)
= fun uop (old_tmp_var, codes) ->
let snd_tmp_var = get_new_tmp_var() in
(snd_tmp_var, codes @ [(0, T.ASSIGNU(snd_tmp_var, uop, old_tmp_var))])


(*translate bop*)
let bop_translate: T.bop -> (T.var * T.program) -> (T.var * T.program) -> (T.var * T.program)
= fun bop (tmp1, code1) (tmp2, code2) ->
let trd_tmp_var = get_new_tmp_var() in
(trd_tmp_var, code1 @ code2 @ [(0, T.ASSIGNV(trd_tmp_var, bop, tmp1, tmp2))])


let rec exp_translator: S.exp -> (T.var * T.program)
= fun exp -> 
match exp with
| S.NUM a -> 
    let fst_tmp_var = get_new_tmp_var() in (fst_tmp_var, [(0, T.COPYC(fst_tmp_var,a))])
| S.LV lv -> 
    (match lv with 
    | S.ID id -> 
        let fst_tmp_var = get_new_tmp_var() in (fst_tmp_var, [(0, T.COPY(fst_tmp_var,id))])
    | S.ARR (id, e) -> 
        let (old_tmp_var, code) = exp_translator e in
        let snd_tmp_var = get_new_tmp_var() in
        (snd_tmp_var, code @ [(0, T.LOAD(snd_tmp_var, (id,old_tmp_var)))])
    )    
| S.MINUS e ->
    let (tmp_var, code) = exp_translator e in
    uop_translate T.MINUS (tmp_var, code)     
| S.NOT e ->
    let (tmp_var, code) = exp_translator e in
    uop_translate T.NOT (tmp_var, code)
| S.ADD (e1, e2) ->
    let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.ADD (tmp1, code1) (tmp2, code2)
| S.SUB (e1, e2) ->
    let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.SUB (tmp1, code1) (tmp2, code2)
| S.MUL (e1, e2) ->
    let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.MUL (tmp1, code1) (tmp2, code2)
| S.DIV (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.DIV (tmp1, code1) (tmp2, code2)
| S.LT (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.LT (tmp1, code1) (tmp2, code2)
| S.LE (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.LE (tmp1, code1) (tmp2, code2)
| S.GT (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.GT (tmp1, code1) (tmp2, code2)
| S.GE (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.GE (tmp1, code1) (tmp2, code2)
| S.EQ (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.EQ (tmp1, code1) (tmp2, code2)
| S.AND (e1, e2) ->
     let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.AND (tmp1, code1) (tmp2, code2)
| S.OR (e1, e2) ->
    let (tmp1, code1) = exp_translator e1 and (tmp2, code2) = exp_translator e2 in
    bop_translate T.OR (tmp1, code1) (tmp2, code2)

let rec stmt_translator: S.stmt -> T.program
= fun stmt -> 
match stmt with
| S.ASSIGN (lv ,e1) ->
    (match lv with
    | S.ID id -> 
        let (tmp,code) = exp_translator e1 in
        code @ [(0, T.COPY(id,tmp))]
    | S.ARR (id, e2) -> 
        let (tmp2, code2) = exp_translator e2 in
        let (tmp,code) = exp_translator e1 in
        code @ code2 @ [(0, T.STORE((id,tmp2),tmp))])
| S.IF (e, stmt1, stmt2) ->
    let (tmp,code) = exp_translator e in
    let code_t = stmt_translator stmt1 and code_f = stmt_translator stmt2 in
    let l_t = new_lb_idx() and l_f = new_lb_idx() and l_x = new_lb_idx() in
    code @ [(0, T.CJUMP (tmp,l_t))] @ [(0, T.UJUMP l_f)] @ [(l_t, T.SKIP)] 
    @ code_t @ [(0, T.UJUMP l_x)] @ [(l_f, T.SKIP)] 
    @ code_f @ [(0, T.UJUMP l_x)] @ [(l_x, T.SKIP)]
| S.WHILE (e, stmt) ->
    let (tmp,code) = exp_translator e and code_b = stmt_translator stmt in
    let l_e = new_lb_idx() and l_x = new_lb_idx() in
    [(l_e, T.SKIP)] @ code @ [(0, T.CJUMPF(tmp, l_x))] @ code_b
    @ [(0, T.UJUMP l_e)] @ [(l_x, T.SKIP)]   
| S.DOWHILE (stmt, e) ->
    (stmt_translator stmt) @ (stmt_translator (S.WHILE (e, stmt)))
| S.READ id -> 
    [(0, T.READ id)]
| S.PRINT e ->
    let (tmp,code) = exp_translator e in
    code @ [(0, T.WRITE tmp)]
| S.BLOCK block -> 
    let (decls, stmts) = block in
    let decl_list = List.fold_left (fun acc decl -> acc @ (decl_translator decl)) [] decls in
    let stmt_list = List.fold_left (fun acc stmt -> acc @ (stmt_translator stmt)) [] stmts in
    decl_list @ stmt_list

let translate : S.program -> T.program
= fun (decls, stmts) ->  
    let decl_list = List.fold_left (fun acc decl -> acc @ (decl_translator decl) ) [] decls in
    let stmt_list = List.fold_left (fun acc stmt -> acc @ (stmt_translator stmt)) [] stmts in
    decl_list @ stmt_list @ [(0, T.HALT)]

