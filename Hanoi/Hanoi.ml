module L = List
         
open GT
open OCanren
open OCanren.Std
       
@type set    = int GT.list * int GT.list * int GT.list  with show
@type lset   = ocanren {int list * int list * int list} with show
@type pin    = A | B | C with show
@type lpin   = ocanren {pin} with show
@type move   = pin * pin with show
@type lmove  = ocanren {pin * pin} with show 
@type moves  = move GT.list with show
@type lmoves = ocanren {move list} with show

let a () = inj A
let b () = inj B
let c () = inj C

let prj_exn_pin : (pin ilogic, pin) Reifier.t =
  let open Env.Monad in 
  Reifier.compose Reifier.reify (
    let f = function
    | Value A -> A
    | Value B -> B
    | Value C -> C
    in return f
  )

let extra = function
| (A, B) | (B, A) -> C
| (A, C) | (C, A) -> B
| (B, C) | (C, B) -> A

let extrao move pin =
  ocanren {
    {move == (A, B) | move == (B, A)} & pin == C
  | {move == (A, C) | move == (C, A)} & pin == B
  | {move == (B, C) | move == (C, B)} & pin == A
  }
                   
let select (x, y, z) = function
| A -> x
| B -> y
| C -> z

let selecto set pin r =
  ocanren {
    fresh x, y, z in
    set == (x, y, z) & {
        pin == A & r == x
      | pin == B & r == y
      | pin == C & r == z
   }    
  }
     
let permut ((a, b) as move) set = (select set a, select set b, select set @@ extra move)

let permuto move set set' =
  ocanren {
    fresh e, a', b', c', a, b in
    move == (a, b) & 
    extrao move e &
    selecto set e c' &
    selecto set a a' &
    selecto set b b' &
    set' == (a', b', c')        
  }
  
let tumrep move (a, b, c) =
  match move with
  | (A, B) -> (a, b, c)
  | (B, A) -> (b, a, c)
  | (A, C) -> (a, c, b)
  | (C, A) -> (b, c, a)  
  | (B, C) -> (c, a, b)
  | (C, B) -> (c, b, a)

let tumrepo move set set' =
  ocanren {
    fresh a', b', c' in
    set == (a', b', c') &
    {
      move == (A, B) & set' == (a', b', c')
    | move == (B, A) & set' == (b', a', c')
    | move == (A, C) & set' == (a', c', b')
    | move == (C, A) & set' == (b', c', a')
    | move == (B, C) & set' == (c', a', b')
    | move == (C, B) & set' == (c', b', a')
    }
  }

let rec evalo p set set' = ocanren {
  p == [] & set == set'
| fresh a, b, p', set'' in
  p == (a, b) :: p' & {
    a == b & set'' == set
  | fresh coreA, coreB, coreC, set''' in
    permuto (a, b) set (coreA, coreB, coreC) & {
      fresh topA, restA in
      coreA == topA :: restA &
      set''' == (restA, topA :: coreB, coreC) & {
        coreB == []
      | fresh topB, restB, ineq in
        coreB == topB :: restB &
        Nat.leo topA topB ineq &
        ineq == true
      }
    } & tumrepo (a, b) set''' set''
  } & evalo p' set'' set'
}
  
let rec eval (p : moves) (set : set) = 
  match p with
  | []                     -> set
  | ((a, b) as move) :: p' ->
     eval p' @@
     if a = b
     then set
     else let (onA, onB, onC) = permut move set in
          tumrep move @@
          match onA with        
          | topA :: restA ->
            match onB with
              []                           -> (restA, [topA], onC)
            | topB :: _  when topB >= topA -> (restA, topA :: onB, onC)      

let _ = Printf.printf "%s\n" @@ show(set) @@
  eval [(A, B); (A, C); (B, C)] ([1; 2], [], [])

let _ =
  Printf.printf "%s\n" @@
  show(List.ground) (show(Pair.ground) (show(pin)) (show(pin))) @@
  L.hd @@
  Stream.take ~n:1 @@
  run q (fun q -> ocanren {evalo q ([1; 2; 3], [], []) ([], [], [1; 2; 3])}) 
        (fun r -> r#reify @@ List.prj_exn @@ Pair.prj_exn prj_exn_pin prj_exn_pin)
