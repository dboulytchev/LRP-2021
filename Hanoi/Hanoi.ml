1module L = List

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

let prj_pin : (pin ilogic, pin) Reifier.t =
  let open Env.Monad in
  let open Syntax in

  Reifier.compose Reifier.reify (
      let f = function
      | Var _ -> failwith "variable pin"
      | Value A -> A
      | Value B -> B
      | Value C -> C
      in

      return f
  )

let extra : pin * pin -> pin = function
| (A, B) | (B, A) -> C
| (A, C) | (C, A) -> B
| (B, C) | (C, B) -> A
(* | other -> invalid_arg @@ Printf.sprintf "%!" other *)

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
  | _ -> invalid_arg ""

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

let rec evalo p set set1 = ocanren
  {   p == []
    & set == set1
  | fresh move, p1, a, b, set2 in
      p == move :: p1
    & move == (a, b)
    & {   a == b
        & set2 == set
      | fresh onB, onC, topA, restA, set3 in
          permuto move set (topA :: restA, onB, onC)
        & {   onB == []
            & set3 == (restA, [topA], onC)
          | fresh topB, restB, ge in
              onB == topB :: restB
            & Nat.geo topB topA ge
            & ge == true
            & set3 == (restA, topA :: onB, onC)
          }
        & tumrepo move set3 set2
      }
    & evalo p1 set2 set1
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
        (fun x -> x#reify @@ List.prj_exn @@ Pair.prj_exn prj_pin prj_pin)
