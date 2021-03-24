module L = List

open GT
open OCanren
open OCanren.Std

(* The boat can be docked on the Left or on the Right shore*)
@type boat  = Left | Right with show
@type lboat = ocanren {boat} with show

(*
   The state of the rivebank is defined by a tuple: Miss, Cann
   where Miss - number of Missioners on the bank
         Cann - number of Cannibals on the bank
*)
@type bank = int * int with show
@type lbank = ocanren {int * int} with show


(* The current state is defined by a triple: LBank, RBank, and Boat
   where LBank - the state of the Left bank
         RBank - the state of the Right bank
         Boat - the position of the boat
*)
@type state = bank * bank * boat with show
@type lstate = ocanren {bank * bank * boat} with show

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
    fresh dMiss, dCann, missL, cannL, missR, cannR, boat in
    move == (dMiss, dCann) &
    state == ((missL, cannL), (missR, cannR), boat) &
    fresh tot in (+) dMiss dCann tot & tot <= 2 & tot > 0 &
    {
      {boat == Left  & dMiss <= missL & dCann <= cannL}
    | {boat == Right & dMiss <= missR & dCann <= cannR}
    }
  })

(* The number of Cannibals must not exceed the number of Missioners on the either bank *)
let safe state =
  Nat.(ocanren {
    fresh missL, cannL, missR, cannR, boat in
    state == ((missL, cannL), (missR, cannR), boat) &
    {
      missL == 0
    | missL >= cannL
    } &
    {
      missR == 0
    | missR >= cannR
    }
  })

(* Perform one step *)
let step move state state' =
  let step = Tabling.tabledrec Tabling.three (fun step move state state' -> 
  Nat.(ocanren {
    fresh dMiss, dCann in
    fresh missL, cannL, missR, cannR, boat in
    fresh missL', cannL', missR', cannR', boat' in

    move == (dMiss, dCann) &
    state == ((missL, cannL), (missR, cannR), boat) &
    state' == ((missL', cannL'), (missR', cannR'), boat') &

    sound move state &
    safe state' &
    { {boat == Left & boat' == Right &
       fresh sM1 in (+) missR dMiss sM1 & sM1 == missR' &
       fresh sM2 in (+) missL' dMiss sM2 & sM2 == missL &

       fresh sC1 in (+) cannR dCann sC1 & sC1 == cannR' &
       fresh sC2 in (+) cannL' dCann sC2 & sC2 == cannL}
    | {boat == Right & boat' == Left &
       fresh sM1 in (+) missR' dMiss sM1 & sM1 == missR &
       fresh sM2 in (+) missL dMiss sM2 & sM2 == missL' &

       fresh sC1 in (+) cannR' dCann sC1 & sC1 == cannR &
       fresh sC2 in (+) cannL dCann sC2 & sC2 == cannL'}
    }
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
  run q (fun q -> ocanren {eval q ((2, 2), (0, 0), Left) ((0, 0), (2, 2), Right)}) project
