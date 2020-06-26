type var = string
type aexp = 
  | Int of int
  | Var of var
  | Plus of aexp * aexp
  | Mult of aexp * aexp 
  | Minus of aexp * aexp 
 
type bexp = 
  | True 
  | False
  | Eq of aexp * aexp 
  | Le of aexp * aexp 
  | Neg of bexp 
  | Conj of bexp * bexp 

type cmd = 
  | Assign of var * aexp 
  | Skip
  | Seq of cmd * cmd
  | If of bexp * cmd * cmd
  | While of bexp * cmd 

(* x:=1; y:=2; a:=x+y; b:=x-y *) 
let test1 = 
  Seq (Assign ("x", Int 1), 
    Seq (Assign ("y", Int 2), 
      Seq (Assign ("a", Plus  (Var "x", Var "y")), 
           Assign ("b", Minus (Var "x", Var "a")))))


(* x:=10; y:=2; while (x!=1) do (y:=y*x; x:=x-1) *)
let test2 = 
  Seq (Assign ("x", Int 10), 
    Seq (Assign("y", Int 2), 
         While (Neg (Eq (Var "x", Int 1)),
                Seq(Assign("y", Mult(Var "y", Var "x")), 
                    Assign("x", Minus(Var "x", Int 1))))))

(* a:=10; b:=2; q:=0; r:=a; while (b<=r) { r:=r-b; q:=q+1 } *)
let test3 = 
  Seq (Assign ("a", Int 10), 
    Seq (Assign ("b", Int 2), 
      Seq (Assign ("q", Int 0), 
        Seq (Assign ("r", Var "a"), 
           While (Le (Var "b", Var "r"),
                Seq(Assign("r", Minus(Var "r", Var "b")), 
                    Assign("q", Plus(Var "q", Int 1))))))))

module ABool = struct
  type t = Bot | Top | TT | FF
  let alpha b = if b then TT else FF

  (* partial order *)
  let order : t -> t -> bool 
  =fun b1 b2 -> 
  match b1 with
  | Bot -> (match b2 with
    | Bot -> true
    | Top -> true
    | TT -> true
    | FF -> true)
  | Top -> (match b2 with
    | Bot -> false
    | Top -> true
    | TT -> false
    | FF -> false)
  | TT -> (match b2 with
    | Bot -> false
    | Top -> true
    | TT -> true
    | FF -> false)
  | FF -> (match b2 with
    | Bot -> false
    | Top -> true
    | TT -> false
    | FF -> true)

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun b1 b2 ->  match b1 with
  | Bot -> (match b2 with
    | Bot -> Bot
    | Top -> Top
    | TT -> TT
    | FF -> FF)
  | Top -> (match b2 with
    | Bot -> Top
    | Top -> Top
    | TT -> Top
    | FF -> Top)
  | TT -> (match b2 with
    | Bot -> TT
    | Top -> Top
    | TT -> TT
    | FF -> Top)
  | FF -> (match b2 with
    | Bot -> FF
    | Top -> Top
    | TT -> Top
    | FF -> FF)

  (* abstract negation *)
  let neg : t -> t 
  =fun b -> match b with
    | Bot -> Bot
    | Top -> Top
    | TT -> FF
    | FF -> TT

  (* abstract conjunction *)
  let conj : t -> t -> t
  =fun b1 b2 ->match b1 with
  | Bot -> (match b2 with
    | Bot -> Bot
    | Top -> Bot
    | TT -> Bot
    | FF -> Bot)
  | Top -> (match b2 with
    | Bot -> Bot
    | Top -> Top
    | TT -> Top
    | FF -> FF)
  | TT -> (match b2 with
    | Bot -> Bot
    | Top -> Top
    | TT -> TT
    | FF -> FF)
  | FF -> (match b2 with
    | Bot -> Bot
    | Top -> FF
    | TT -> FF
    | FF -> FF)
end

module AValue = struct
  type t = Bot | Top | Neg | Zero | Pos | NonPos | NonZero | NonNeg
  let alpha : int -> t 
  =fun n -> if n = 0 then Zero else if n > 0 then Pos else Neg
  let to_string s = 
    match s with 
    | Bot -> "Bot" 
    | Top -> "Top" 
    | Pos -> "Pos" 
    | Neg -> "Neg" 
    | Zero -> "Zero"
    | NonNeg -> "NonNeg"
    | NonZero -> "NonZero"
    | NonPos -> "NonPos"

  (* partial order *)
  let order : t -> t -> bool
  =fun s1 s2 -> match s1 with
  | Bot -> (match s2 with
    | Bot -> true 
    | Top -> true 
    | Pos -> true 
    | Neg -> true 
    | Zero -> true
    | NonNeg -> true
    | NonZero -> true
    | NonPos -> true) 
  | Top -> (match s2 with
    | Bot -> false
    | Top -> true 
    | Pos -> false 
    | Neg -> false 
    | Zero -> false
    | NonNeg -> false
    | NonZero -> false
    | NonPos -> false) 
  | Pos -> (match s2 with
    | Bot -> false 
    | Top -> true 
    | Pos -> true 
    | Neg -> false 
    | Zero -> false
    | NonNeg -> true
    | NonZero -> true
    | NonPos -> false)
  | Neg -> (match s2 with
    | Bot -> false 
    | Top -> true 
    | Pos -> false 
    | Neg -> true 
    | Zero -> false
    | NonNeg -> false
    | NonZero -> true
    | NonPos -> true) 
  | Zero -> (match s2 with
    | Bot -> false 
    | Top -> true 
    | Pos -> false 
    | Neg -> false 
    | Zero -> true
    | NonNeg -> true
    | NonZero -> false
    | NonPos -> true)
  | NonNeg -> (match s2 with
    | Bot -> false 
    | Top -> true 
    | Pos -> false 
    | Neg -> false 
    | Zero -> false
    | NonNeg -> true
    | NonZero -> false
    | NonPos -> false)
  | NonZero -> (match s2 with
    | Bot -> false 
    | Top -> true 
    | Pos -> false 
    | Neg -> false 
    | Zero -> false
    | NonNeg -> false
    | NonZero -> true
    | NonPos -> false)
  | NonPos -> (match s2 with
    | Bot -> false 
    | Top -> true 
    | Pos -> false 
    | Neg -> false
    | Zero -> false
    | NonNeg -> false
    | NonZero -> true
    | NonPos -> true)

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun s1 s2 -> match s1 with
  | Bot -> (match s2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Pos 
    | Neg -> Neg 
    | Zero -> Zero
    | NonNeg -> NonNeg
    | NonZero -> NonZero
    | NonPos -> NonPos) 
  | Top -> (match s2 with
    | Bot -> Top
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top) 
  | Pos -> (match s2 with
    | Bot -> Pos 
    | Top -> Top 
    | Pos -> Pos 
    | Neg -> NonZero
    | Zero -> NonNeg
    | NonNeg -> NonNeg
    | NonZero -> NonZero
    | NonPos -> Top)
  | Neg -> (match s2 with
    | Bot -> Neg 
    | Top -> Top 
    | Pos -> NonZero 
    | Neg -> Neg 
    | Zero -> NonPos
    | NonNeg -> Top
    | NonZero -> NonZero
    | NonPos -> NonPos) 
  | Zero -> (match s2 with
    | Bot -> Zero 
    | Top -> Top 
    | Pos -> NonNeg 
    | Neg -> NonPos 
    | Zero -> Zero
    | NonNeg -> NonNeg
    | NonZero -> Top
    | NonPos -> NonPos)
  | NonNeg -> (match s2 with
    | Bot -> NonNeg 
    | Top -> Top 
    | Pos -> NonNeg 
    | Neg -> Top 
    | Zero -> NonNeg
    | NonNeg -> NonNeg
    | NonZero -> Top
    | NonPos -> Top)
  | NonZero -> (match s2 with
    | Bot -> NonZero 
    | Top -> Top 
    | Pos -> NonZero 
    | Neg -> NonZero 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> NonZero
    | NonPos -> Top)
  | NonPos -> (match s2 with
    | Bot -> NonPos 
    | Top -> Top
    | Pos -> Top 
    | Neg -> NonPos 
    | Zero -> NonPos
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> NonPos)
    
  (* abstract addition *)
  let plus : t -> t -> t 
  =fun a1 a2 -> match a1 with
  | Bot -> (match a2 with
    | Bot -> Bot 
    | Top -> Bot 
    | Pos -> Bot
    | Neg -> Bot 
    | Zero -> Bot
    | NonNeg -> Bot
    | NonZero -> Bot
    | NonPos -> Bot) 
  | Top -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top) 
  | Pos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Pos 
    | Neg -> Top 
    | Zero -> Pos
    | NonNeg -> Pos
    | NonZero -> Top
    | NonPos -> Top)
  | Neg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Neg 
    | Zero -> Neg
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Neg) 
  | Zero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Pos
    | Neg -> Neg
    | Zero -> Zero
    | NonNeg -> NonNeg
    | NonZero -> NonZero
    | NonPos -> NonPos)
  | NonNeg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Pos 
    | Neg -> Top 
    | Zero -> NonNeg
    | NonNeg -> NonNeg
    | NonZero -> Top
    | NonPos -> Top)
  | NonZero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> NonZero
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)
  | NonPos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top
    | Pos -> Top
    | Neg -> Neg 
    | Zero -> NonPos
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> NonPos)
    
     
  (* abstract multiplication *)
  let mult : t -> t -> t 
  =fun a1 a2 -> match a1 with
  | Bot -> (match a2 with
    | Bot -> Bot 
    | Top -> Bot 
    | Pos -> Bot 
    | Neg -> Bot 
    | Zero -> Bot
    | NonNeg -> Bot
    | NonZero -> Bot
    | NonPos -> Bot) 
  | Top -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Zero
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top) 
  | Pos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Pos 
    | Neg -> Neg
    | Zero -> Zero
    | NonNeg -> NonNeg
    | NonZero -> NonZero
    | NonPos -> NonPos)
  | Neg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Neg 
    | Neg -> Pos
    | Zero -> Zero
    | NonNeg -> NonPos
    | NonZero -> NonZero
    | NonPos -> NonNeg) 
  | Zero -> (match a2 with
    | Bot -> Bot 
    | Top -> Zero 
    | Pos -> Zero 
    | Neg -> Zero
    | Zero -> Zero
    | NonNeg -> Zero
    | NonZero -> Zero
    | NonPos -> Zero)
  | NonNeg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> NonNeg 
    | Neg -> NonPos 
    | Zero -> Zero
    | NonNeg -> NonNeg
    | NonZero -> Top
    | NonPos -> NonPos)
  | NonZero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> NonZero
    | Neg -> NonZero 
    | Zero -> Zero
    | NonNeg -> Top
    | NonZero -> NonZero
    | NonPos -> Top)
  | NonPos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> NonPos 
    | Neg -> NonNeg 
    | Zero -> Zero
    | NonNeg -> NonPos
    | NonZero -> Top
    | NonPos -> NonNeg)

  (* abstract subtraction *)
  let minus : t -> t -> t
  =fun a1 a2 -> match a1 with
  | Bot -> (match a2 with
    | Bot -> Bot 
    | Top -> Bot 
    | Pos -> Bot 
    | Neg -> Bot 
    | Zero -> Bot
    | NonNeg -> Bot
    | NonZero -> Bot
    | NonPos -> Bot) 
  | Top -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top) 
  | Pos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Pos 
    | Zero -> Pos
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Pos)
  | Neg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Neg 
    | Neg -> Top 
    | Zero -> Neg
    | NonNeg -> Neg
    | NonZero -> Top
    | NonPos -> Top) 
  | Zero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Neg 
    | Neg -> Pos
    | Zero -> Zero
    | NonNeg -> NonPos
    | NonZero -> NonZero
    | NonPos -> NonNeg)
  | NonNeg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Pos 
    | Zero -> NonNeg
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> NonNeg)
  | NonZero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> NonZero
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)
  | NonPos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Neg 
    | Neg -> Top 
    | Zero -> NonPos
    | NonNeg -> NonPos
    | NonZero -> Top
    | NonPos -> Top)

    
  let eq : t -> t -> ABool.t 
  =fun a1 a2 -> match a1 with
  | Bot -> (match a2 with
    | Bot -> Bot 
    | Top -> Bot 
    | Pos -> Bot 
    | Neg -> Bot 
    | Zero -> Bot
    | NonNeg -> Bot
    | NonZero -> Bot
    | NonPos -> Bot) 
  | Top -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top) 
  | Pos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> FF 
    | Zero -> FF
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> FF)
  | Neg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top
    | Pos -> FF 
    | Neg -> Top 
    | Zero -> FF
    | NonNeg -> FF
    | NonZero -> Top
    | NonPos -> Top) 
  | Zero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> FF 
    | Neg -> FF 
    | Zero -> TT
    | NonNeg -> Top
    | NonZero -> FF
    | NonPos -> Top)
  | NonNeg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> FF 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)
  | NonZero -> (match a2 with
    | Bot -> Bot
    | Top -> Top 
    | Pos -> Top
    | Neg -> Top 
    | Zero -> FF
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)
  | NonPos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> FF 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)

  let le : t -> t -> ABool.t 
  =fun a1 a2 -> match a1 with
  | Bot -> (match a2 with
    | Bot -> Bot 
    | Top -> Bot 
    | Pos -> Bot 
    | Neg -> Bot 
    | Zero -> Bot
    | NonNeg -> Bot
    | NonZero -> Bot
    | NonPos -> Bot) 
  | Top -> (match a2 with
    | Bot -> Top 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top) 
  | Pos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> FF 
    | Zero -> FF
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> FF)
  | Neg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> TT 
    | Neg -> Top 
    | Zero -> TT
    | NonNeg -> TT
    | NonZero -> Top
    | NonPos -> Top) 
  | Zero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> TT 
    | Neg -> FF 
    | Zero -> TT
    | NonNeg -> TT
    | NonZero -> Top
    | NonPos -> Top)
  | NonNeg -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> FF 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)
  | NonZero -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> Top 
    | Neg -> Top 
    | Zero -> Top
    | NonNeg -> Top
    | NonZero -> Top
    | NonPos -> Top)
  | NonPos -> (match a2 with
    | Bot -> Bot 
    | Top -> Top 
    | Pos -> TT 
    | Neg -> Top 
    | Zero -> TT
    | NonNeg -> TT
    | NonZero -> Top
    | NonPos -> Top)
end

module AState = struct
  module Map = Map.Make(struct type t = var let compare = compare end)
  type t = AValue.t Map.t (* var -> AValue.t map *)
  let bot = Map.empty
  let find x m = try Map.find x m with Not_found -> AValue.Bot
  let update x v m = Map.add x v m
  let update_join x v m = Map.add x (AValue.lub v (find x m)) m
  let order m1 m2 = Map.for_all (fun k v -> AValue.order v (find k m2)) m1
  let lub m1 m2 = Map.fold (fun k v m -> update_join k v m) m1 m2
  let print m = 
    Map.iter (fun k v -> 
   print_endline (k ^ " |-> " ^ AValue.to_string v)) m 
end

let rec aeval : aexp -> AState.t -> AValue.t
=fun a s ->
  match a with
  | Int n -> AValue.alpha n 
  | Var x -> AState.find x s 
  | Plus (a1, a2) -> AValue.plus (aeval a1 s) (aeval a2 s)
  | Mult (a1, a2) -> AValue.mult (aeval a1 s) (aeval a2 s)
  | Minus (a1, a2) -> AValue.minus (aeval a1 s) (aeval a2 s)

let rec beval : bexp -> AState.t -> ABool.t
=fun b s -> 
  match b with
  | True -> ABool.alpha true
  | False -> ABool.alpha false
  | Eq (a1, a2) -> AValue.eq (aeval a1 s) (aeval a2 s)
  | Le (a1, a2) -> AValue.le (aeval a1 s) (aeval a2 s)
  | Neg b -> ABool.neg (beval b s)
  | Conj (b1, b2) -> ABool.conj (beval b1 s) (beval b2 s)

let rec ceval : cmd -> AState.t -> AState.t
=fun c s -> 
  match c with
  | Assign (x, a) -> AState.update x (aeval a s) s
  | Skip -> s
  | Seq (c1,c2) -> ceval c2 (ceval c1 s)
  | If (b, c1, c2) -> 
      if beval b s = ABool.TT then (ceval c1 s)
      else if beval b s = ABool.FF then (ceval c2 s)
      else if beval b s = ABool.Bot then AState.bot
      else AState.lub (ceval c1 s) (ceval c2 s)

  | While (_, c) -> fix (ceval c) s

and fix f s0 = if AState.order (f s0) s0 then s0 else fix f (f s0)

let run : cmd -> AState.t
=fun c -> ceval c AState.bot

let tests = [test1; test2; test3]

let _ = List.iter (fun test -> AState.print(run test)) tests