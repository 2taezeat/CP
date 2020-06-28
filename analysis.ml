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
    match b1, b2 with
    | Bot, Top -> true
    | Bot, TT -> true
    | Bot, FF -> true
    | Bot, Bot -> true

    | Top, Top -> true
    | Top, TT -> false
    | Top, FF -> false
    | Top, Bot -> false

    | TT, Top -> true
    | TT, TT -> true
    | TT, FF -> false
    | TT, Bot -> false

    | FF, Top -> true
    | FF, TT -> false
    | FF, FF -> true
    | FF, Bot -> false 

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun b1 b2 -> 
      match b1, b2 with
    | Bot, Top -> Top
    | Bot, TT ->  TT
    | Bot, FF ->  FF
    | Bot, Bot -> Bot

    | Top, Top -> Top
    | Top, TT -> Top
    | Top, FF -> Top
    | Top, Bot -> Top

    | TT, Top -> Top
    | TT, TT -> TT
    | TT, FF -> Top
    | TT, Bot -> TT 

    | FF, Top -> Top
    | FF, TT -> Top
    | FF, FF -> FF
    | FF, Bot -> FF

  (* abstract negation *)
  let neg : t -> t 
  =fun b -> 
    match b with
    | Bot -> Bot
    | Top -> Top
    | TT -> FF
    | FF -> TT
    
  (* abstract conjunction *)
  let conj : t -> t -> t
  =fun b1 b2 -> 
  match b1, b2 with 
    | Bot, Top -> Bot
    | Bot, TT ->  Bot
    | Bot, FF ->  Bot
    | Bot, Bot -> Bot

    | Top, Top -> Top 
    | Top, TT -> Top
    | Top, FF -> FF
    | Top, Bot -> Bot

    | TT, Top -> Top
    | TT, TT -> TT
    | TT, FF -> FF
    | TT, Bot -> Bot

    | FF, Top -> FF
    | FF, TT -> FF
    | FF, FF -> FF
    | FF, Bot -> Bot
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
  =fun s1 s2 -> 
  match s1, s2 with
    | Bot, Bot -> true
    | Bot, Top-> true
    | Bot, Neg-> true
    | Bot, Zero-> true
    | Bot, Pos-> true
    | Bot, NonPos-> true
    | Bot, NonZero-> true
    | Bot, NonNeg-> true

    | Top, Bot -> false
    | Top, Top-> true
    | Top, Neg-> false
    | Top, Zero-> false
    | Top, Pos-> false
    | Top, NonPos-> false
    | Top, NonZero-> false
    | Top, NonNeg-> false

    | Neg, Bot -> false
    | Neg, Top-> true
    | Neg, Neg-> true
    | Neg, Zero-> false
    | Neg, Pos-> false
    | Neg, NonPos-> true
    | Neg, NonZero-> true
    | Neg, NonNeg-> false

    | Zero, Bot -> false
    | Zero, Top-> true
    | Zero, Neg-> false
    | Zero, Zero-> true
    | Zero, Pos-> false
    | Zero, NonPos-> true
    | Zero, NonZero-> false
    | Zero, NonNeg-> true

    | Pos, Bot -> false
    | Pos, Top-> true
    | Pos, Neg-> false
    | Pos, Zero-> false
    | Pos, Pos-> true
    | Pos, NonPos-> false
    | Pos, NonZero-> true
    | Pos, NonNeg-> true

    | NonPos, Bot -> false
    | NonPos, Top-> true
    | NonPos, Neg-> false
    | NonPos, Zero-> false
    | NonPos, Pos-> false
    | NonPos, NonPos-> true
    | NonPos, NonZero-> false
    | NonPos, NonNeg-> false

    | NonZero, Bot -> false
    | NonZero, Top-> true
    | NonZero, Neg-> false
    | NonZero, Zero-> false 
    | NonZero, Pos->  false
    | NonZero, NonPos-> false
    | NonZero, NonZero-> true
    | NonZero, NonNeg-> false

    | NonNeg, Bot -> false
    | NonNeg, Top-> true
    | NonNeg, Neg-> false
    | NonNeg, Zero-> false
    | NonNeg, Pos-> false
    | NonNeg, NonPos-> false
    | NonNeg, NonZero-> false
    | NonNeg, NonNeg-> true

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun s1 s2 -> 
  match s1, s2 with
    | Bot, Bot -> Bot 
    | Bot, Top-> Top
    | Bot, Neg-> Neg
    | Bot, Zero-> Zero
    | Bot, Pos-> Pos
    | Bot, NonPos-> NonPos
    | Bot, NonZero-> NonZero
    | Bot, NonNeg-> NonNeg

    | Top, Bot -> Top
    | Top, Top-> Top
    | Top, Neg-> Top
    | Top, Zero-> Top
    | Top, Pos-> Top
    | Top, NonPos-> Top
    | Top, NonZero-> Top
    | Top, NonNeg-> Top

    | Neg, Bot -> Neg 
    | Neg, Top-> Top
    | Neg, Neg-> Neg
    | Neg, Zero-> NonPos
    | Neg, Pos-> NonZero
    | Neg, NonPos-> NonPos
    | Neg, NonZero-> NonZero
    | Neg, NonNeg-> Top

    | Zero, Bot -> Zero
    | Zero, Top-> Top
    | Zero, Neg->  NonPos
    | Zero, Zero-> Zero
    | Zero, Pos-> NonNeg
    | Zero, NonPos-> NonPos
    | Zero, NonZero-> Top
    | Zero, NonNeg-> NonNeg

    | Pos, Bot -> Pos
    | Pos, Top-> Top
    | Pos, Neg-> NonZero
    | Pos, Zero-> NonNeg
    | Pos, Pos-> Pos
    | Pos, NonPos-> Top
    | Pos, NonZero-> NonZero
    | Pos, NonNeg-> NonNeg

    | NonPos, Bot -> NonPos
    | NonPos, Top-> Top
    | NonPos, Neg-> NonPos
    | NonPos, Zero-> NonPos
    | NonPos, Pos-> Top
    | NonPos, NonPos-> NonPos
    | NonPos, NonZero-> Top
    | NonPos, NonNeg-> Top

    | NonZero, Bot -> NonZero 
    | NonZero, Top-> Top
    | NonZero, Neg-> NonZero
    | NonZero, Zero-> Top
    | NonZero, Pos-> NonZero
    | NonZero, NonPos-> Top
    | NonZero, NonZero-> NonZero
    | NonZero, NonNeg-> Top

    | NonNeg, Bot -> NonNeg 
    | NonNeg, Top-> Top
    | NonNeg, Neg-> Top
    | NonNeg, Zero-> NonNeg
    | NonNeg, Pos->  NonNeg
    | NonNeg, NonPos-> Top
    | NonNeg, NonZero-> Top
    | NonNeg, NonNeg-> NonNeg
    
  (* abstract addition *)
  let plus : t -> t -> t 
  =fun a1 a2 -> 
  match a1, a2 with
    | Bot, Bot -> Bot
    | Bot, Top-> Bot
    | Bot, Neg-> Bot
    | Bot, Zero-> Bot
    | Bot, Pos-> Bot
    | Bot, NonPos-> Bot
    | Bot, NonZero-> Bot
    | Bot, NonNeg-> Bot

    | Top, Bot -> Bot
    | Top, Top-> Top
    | Top, Neg-> Top
    | Top, Zero-> Top
    | Top, Pos-> Top
    | Top, NonPos-> Top
    | Top, NonZero-> Top
    | Top, NonNeg-> Top

    | Neg, Bot -> Bot
    | Neg, Top-> Top
    | Neg, Neg-> Neg
    | Neg, Zero-> Neg
    | Neg, Pos-> Top
    | Neg, NonPos-> Neg
    | Neg, NonZero-> Top
    | Neg, NonNeg-> Top

    | Zero, Bot -> Bot
    | Zero, Top-> Top
    | Zero, Neg-> Neg
    | Zero, Zero-> Zero
    | Zero, Pos-> Pos
    | Zero, NonPos-> NonPos
    | Zero, NonZero-> NonZero
    | Zero, NonNeg-> NonNeg

    | Pos, Bot -> Bot
    | Pos, Top-> Top
    | Pos, Neg-> Top
    | Pos, Zero-> Pos
    | Pos, Pos-> Pos
    | Pos, NonPos-> Top
    | Pos, NonZero-> Top
    | Pos, NonNeg-> Pos

    | NonPos, Bot -> Bot
    | NonPos, Top-> Top
    | NonPos, Neg-> Neg
    | NonPos, Zero-> NonPos
    | NonPos, Pos-> Top
    | NonPos, NonPos-> NonPos
    | NonPos, NonZero-> Top
    | NonPos, NonNeg-> Top

    | NonZero, Bot -> Bot
    | NonZero, Top-> Top
    | NonZero, Neg-> Top
    | NonZero, Zero-> NonZero
    | NonZero, Pos-> Top
    | NonZero, NonPos-> Top
    | NonZero, NonZero-> Top
    | NonZero, NonNeg-> Top

    | NonNeg, Bot -> Bot
    | NonNeg, Top-> Top
    | NonNeg, Neg-> Top
    | NonNeg, Zero-> NonNeg
    | NonNeg, Pos-> Pos
    | NonNeg, NonPos-> Top
    | NonNeg, NonZero-> Top
    | NonNeg, NonNeg-> NonNeg
     
  (* abstract multiplication *)
  let mult : t -> t -> t 
  =fun a1 a2 -> 
  match a1, a2 with
    | Bot, Bot -> Bot
    | Bot, Top-> Bot
    | Bot, Neg-> Bot
    | Bot, Zero-> Bot
    | Bot, Pos-> Bot
    | Bot, NonPos-> Bot
    | Bot, NonZero-> Bot
    | Bot, NonNeg-> Bot

    | Top, Bot -> Bot
    | Top, Top-> Top
    | Top, Neg-> Top
    | Top, Zero-> Zero
    | Top, Pos-> Top
    | Top, NonPos-> Top
    | Top, NonZero-> Top
    | Top, NonNeg-> Top

    | Neg, Bot -> Bot
    | Neg, Top-> Top
    | Neg, Neg-> Pos
    | Neg, Zero-> Zero
    | Neg, Pos-> Neg
    | Neg, NonPos-> NonNeg
    | Neg, NonZero-> NonZero
    | Neg, NonNeg-> NonPos

    | Zero, Bot -> Bot
    | Zero, Top-> Zero
    | Zero, Neg-> Zero
    | Zero, Zero-> Zero
    | Zero, Pos-> Zero
    | Zero, NonPos-> Zero
    | Zero, NonZero-> Zero
    | Zero, NonNeg-> Zero

    | Pos, Bot -> Bot
    | Pos, Top-> Top
    | Pos, Neg-> Neg
    | Pos, Zero-> Zero
    | Pos, Pos-> Pos
    | Pos, NonPos-> NonPos
    | Pos, NonZero-> NonZero
    | Pos, NonNeg-> NonNeg

    | NonPos, Bot -> Bot
    | NonPos, Top-> Top
    | NonPos, Neg-> NonNeg
    | NonPos, Zero-> Zero
    | NonPos, Pos-> NonPos
    | NonPos, NonPos-> NonNeg
    | NonPos, NonZero-> Top
    | NonPos, NonNeg-> NonPos

    | NonZero, Bot -> Bot
    | NonZero, Top-> Top
    | NonZero, Neg-> NonZero
    | NonZero, Zero-> Zero
    | NonZero, Pos-> NonZero
    | NonZero, NonPos-> Top
    | NonZero, NonZero-> NonZero
    | NonZero, NonNeg-> Top

    | NonNeg, Bot -> Bot
    | NonNeg, Top-> Top
    | NonNeg, Neg-> NonPos
    | NonNeg, Zero-> Zero
    | NonNeg, Pos-> NonNeg
    | NonNeg, NonPos-> NonPos
    | NonNeg, NonZero-> Top
    | NonNeg, NonNeg-> NonNeg

  (* abstract subtraction *)
  let minus : t -> t -> t
  =fun a1 a2 -> 
  match a1, a2 with
    | Bot, Bot -> Bot
    | Bot, Top-> Bot
    | Bot, Neg-> Bot
    | Bot, Zero-> Bot
    | Bot, Pos-> Bot
    | Bot, NonPos-> Bot
    | Bot, NonZero-> Bot
    | Bot, NonNeg-> Bot

    | Top, Bot -> Bot
    | Top, Top-> Top
    | Top, Neg-> Top
    | Top, Zero-> Top
    | Top, Pos-> Top
    | Top, NonPos-> Top
    | Top, NonZero-> Top
    | Top, NonNeg-> Top

    | Neg, Bot -> Bot
    | Neg, Top-> Top
    | Neg, Neg-> Top
    | Neg, Zero-> Neg
    | Neg, Pos-> Neg
    | Neg, NonPos-> Top
    | Neg, NonZero-> Top
    | Neg, NonNeg-> Neg

    | Zero, Bot -> Bot
    | Zero, Top-> Top
    | Zero, Neg-> Pos
    | Zero, Zero-> Zero
    | Zero, Pos-> Neg
    | Zero, NonPos-> NonNeg
    | Zero, NonZero-> NonZero
    | Zero, NonNeg-> NonPos

    | Pos, Bot -> Bot
    | Pos, Top-> Top
    | Pos, Neg-> Pos
    | Pos, Zero-> Pos
    | Pos, Pos-> Top
    | Pos, NonPos-> Pos
    | Pos, NonZero-> Top
    | Pos, NonNeg-> Top

    | NonPos, Bot -> Bot
    | NonPos, Top-> Top
    | NonPos, Neg-> Top
    | NonPos, Zero-> NonPos
    | NonPos, Pos-> Neg
    | NonPos, NonPos-> Top
    | NonPos, NonZero-> Top
    | NonPos, NonNeg-> NonPos

    | NonZero, Bot -> Bot
    | NonZero, Top-> Top
    | NonZero, Neg-> Top
    | NonZero, Zero-> NonZero
    | NonZero, Pos-> Top
    | NonZero, NonPos-> Top
    | NonZero, NonZero-> Top
    | NonZero, NonNeg-> Top

    | NonNeg, Bot -> Bot
    | NonNeg, Top-> Top
    | NonNeg, Neg-> Pos
    | NonNeg, Zero-> NonNeg 
    | NonNeg, Pos-> Top
    | NonNeg, NonPos-> NonNeg
    | NonNeg, NonZero-> Top
    | NonNeg, NonNeg-> Top
    
  let eq : t -> t -> ABool.t 
  =fun a1 a2 -> 
    match a1, a2 with
    | Bot, Bot -> ABool.TT 
    | Bot, Top-> ABool.Top
    | Bot, Neg-> ABool.FF
    | Bot, Zero-> ABool.FF
    | Bot, Pos-> ABool.FF
    | Bot, NonPos-> ABool.FF
    | Bot, NonZero-> ABool.FF
    | Bot, NonNeg-> ABool.FF

    | Top, Bot -> ABool.Top
    | Top, Top-> ABool.Top
    | Top, Neg-> ABool.Top
    | Top, Zero-> ABool.Top
    | Top, Pos-> ABool.Top
    | Top, NonPos-> ABool.Top
    | Top, NonZero-> ABool.Top
    | Top, NonNeg-> ABool.Top

    | Neg, Bot -> ABool.FF
    | Neg, Top-> ABool.Top
    | Neg, Neg-> ABool.Top
    | Neg, Zero-> ABool.FF
    | Neg, Pos-> ABool.FF
    | Neg, NonPos-> ABool.Top
    | Neg, NonZero-> ABool.Top
    | Neg, NonNeg-> ABool.FF

    | Zero, Bot -> ABool.FF
    | Zero, Top-> ABool.Top
    | Zero, Neg-> ABool.FF
    | Zero, Zero-> ABool.TT
    | Zero, Pos-> ABool.FF
    | Zero, NonPos-> ABool.Top
    | Zero, NonZero-> ABool.FF
    | Zero, NonNeg-> ABool.Top

    | Pos, Bot -> ABool.FF
    | Pos, Top-> ABool.Top
    | Pos, Neg-> ABool.FF
    | Pos, Zero-> ABool.FF
    | Pos, Pos-> ABool.Top
    | Pos, NonPos-> ABool.FF
    | Pos, NonZero-> ABool.Top
    | Pos, NonNeg-> ABool.Top

    | NonPos, Bot -> ABool.FF
    | NonPos, Top-> ABool.Top
    | NonPos, Neg-> ABool.Top
    | NonPos, Zero-> ABool.Top
    | NonPos, Pos-> ABool.FF
    | NonPos, NonPos-> ABool.Top
    | NonPos, NonZero-> ABool.Top
    | NonPos, NonNeg-> ABool.Top

    | NonZero, Bot -> ABool.FF
    | NonZero, Top-> ABool.Top
    | NonZero, Neg-> ABool.Top
    | NonZero, Zero-> ABool.FF
    | NonZero, Pos-> ABool.Top
    | NonZero, NonPos-> ABool.Top
    | NonZero, NonZero-> ABool.Top
    | NonZero, NonNeg-> ABool.Top

    | NonNeg, Bot -> ABool.FF
    | NonNeg, Top-> ABool.Top
    | NonNeg, Neg-> ABool.FF
    | NonNeg, Zero-> ABool.Top
    | NonNeg, Pos-> ABool.Top
    | NonNeg, NonPos-> ABool.Top
    | NonNeg, NonZero-> ABool.Top
    | NonNeg, NonNeg-> ABool.Top

  let le : t -> t -> ABool.t 
  =fun a1 a2 ->  
    match a1, a2 with
    | Bot, Bot -> ABool.TT
    | Bot, Top-> ABool.Top
    | Bot, Neg-> ABool.FF
    | Bot, Zero-> ABool.FF
    | Bot, Pos-> ABool.FF
    | Bot, NonPos-> ABool.FF
    | Bot, NonZero-> ABool.FF
    | Bot, NonNeg-> ABool.FF

    | Top, Bot -> ABool.Top
    | Top, Top-> ABool.Top
    | Top, Neg-> ABool.Top
    | Top, Zero-> ABool.Top
    | Top, Pos-> ABool.Top
    | Top, NonPos-> ABool.Top
    | Top, NonZero-> ABool.Top
    | Top, NonNeg-> ABool.Top

    | Neg, Bot -> ABool.FF
    | Neg, Top-> ABool.Top
    | Neg, Neg-> ABool.Top
    | Neg, Zero-> ABool.TT
    | Neg, Pos-> ABool.TT
    | Neg, NonPos-> ABool.Top
    | Neg, NonZero-> ABool.Top
    | Neg, NonNeg-> ABool.TT

    | Zero, Bot -> ABool.FF
    | Zero, Top-> ABool.Top
    | Zero, Neg-> ABool.FF
    | Zero, Zero-> ABool.TT
    | Zero, Pos-> ABool.TT
    | Zero, NonPos-> ABool.Top
    | Zero, NonZero-> ABool.Top
    | Zero, NonNeg-> ABool.TT

    | Pos, Bot -> ABool.FF
    | Pos, Top-> ABool.Top
    | Pos, Neg-> ABool.FF
    | Pos, Zero-> ABool.FF
    | Pos, Pos-> ABool.Top
    | Pos, NonPos-> ABool.FF
    | Pos, NonZero-> ABool.Top
    | Pos, NonNeg-> ABool.Top

    | NonPos, Bot -> ABool.FF
    | NonPos, Top-> ABool.Top
    | NonPos, Neg-> ABool.Top
    | NonPos, Zero-> ABool.TT
    | NonPos, Pos-> ABool.TT
    | NonPos, NonPos-> ABool.Top
    | NonPos, NonZero-> ABool.Top
    | NonPos, NonNeg-> ABool.TT

    | NonZero, Bot -> ABool.FF
    | NonZero, Top-> ABool.Top
    | NonZero, Neg-> ABool.Top
    | NonZero, Zero-> ABool.Top
    | NonZero, Pos-> ABool.Top
    | NonZero, NonPos-> ABool.Top
    | NonZero, NonZero-> ABool.Top
    | NonZero, NonNeg-> ABool.Top

    | NonNeg, Bot -> ABool.FF
    | NonNeg, Top-> ABool.Top
    | NonNeg, Neg-> ABool.FF
    | NonNeg, Zero-> ABool.Top
    | NonNeg, Pos-> ABool.Top
    | NonNeg, NonPos-> ABool.Top
    | NonNeg, NonZero-> ABool.Top
    | NonNeg, NonNeg-> ABool.Top
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


