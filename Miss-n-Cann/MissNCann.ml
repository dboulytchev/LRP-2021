module L = List

open GT
open OCanren
open OCanren.Std

(* The boat can be docked on the Left or on the Right shore*)
@type boat  = Left | Right with show
@type lboat = ocanren {boat} with show


(* The current state is defined by a triple: Miss, Cann, and Boat
   where Miss - number of Mission on the _current_ bank (where the boat is located)
         Cann - same for Cannibals
         Boat - the position of the boat
*)
@type state = int * int * boat with show
@type lstate = ocanren {int * int * boat} with show

(* The move is a pair DMiss and DCann
   where DMiss - the number of Missioners embarking on the boat
         DCann - same for Cannibals
*)
@type move = L2R of int * int | R2L of int * int with show
@type lmove = ocanren {move}

@type moves  = move GT.list with show
@type lmoves = ocanren {move list} with show

let left () = inj @@ lift Left
let right () = inj @@ lift Right


(* Initially, there are n Missioners and n Cannibals on the Left bank *)

(* The boat can fit one or two people
   The people embarked must exist
*)
let sound move state =
  Nat.(ocanren {
    fresh dMiss, dCann, miss, cann, boat in
    move == (dMiss, dCann) &
    state == (miss, cann, boat) &
    fresh tot in (+) dMiss dCann tot & tot <= 2 & tot > 0 &
    dMiss <= miss & dCann <= cann }
  )

(* The number of Cannibals must not exceed the number of Missioners on the either bank *)
let safe state =
  Nat.(ocanren {
    fresh miss, cann,boat in
    state == (miss, cann, boat) &
    {
      miss == 0
    | miss >= cann
    } &
    {
      miss == 2
    | miss <= cann
    }
  })

(* Perform one step *)
let step move state state' =
  let step = Tabling.tabledrec Tabling.three (fun step move state state' ->
  Nat.(ocanren {
    fresh dMiss, dCann in
    fresh miss, cann, boat in
    fresh miss', cann', boat' in
    move == (dMiss, dCann) &
    state == (miss, cann, boat) &
    state' == (miss', cann', boat') &

    sound move state &
    safe state' &
    {
      boat == Left & boat' == Right
    | boat == Right & boat' == Left
    } &
    (* miss' == n - miss + dMiss *)
    fresh m1, m2 in
    (+) miss miss' m1 &
    (+) 2 dMiss m2 &
    m1 == m2 &

    (* cann' == n - cann + dCann *)
    fresh c1, c2 in
    (+) cann cann' c1 &
    (+) 2 dCann c2 &
    c1 == c2
  }))

in step move state state'


let eval p state state' =
  let eval = Tabling.tabledrec Tabling.three (fun eval p state state' -> 
  ocanren {
    {p == [] & state == state'}
  | {fresh move, p', stateStep in
     p == move :: p' &
     step move state stateStep &
     eval p' stateStep state'}
  }) in eval p state state'

let _ =
  Printf.printf "%s\n" @@
  show(List.ground) (show(Pair.ground) (show(OCanren.Std.Nat.ground)) (show(OCanren.Std.Nat.ground)))  @@
  L.hd @@
  Stream.take ~n:1 @@
  run q (fun q -> ocanren {eval q (2, 2, Left) (2, 2, Right)}) project
