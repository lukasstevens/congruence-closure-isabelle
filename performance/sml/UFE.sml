signature UFE_SIG =
sig

type nat 
type ufe

val nat_of_int : int -> nat

val init : nat -> ufe

val find : (ufe * nat) -> nat
val union : (ufe * nat * nat) -> ufe
val explain : (ufe * nat * nat) -> unit

end

signature UFE_MORE =
sig

include UFE_SIG

val mk_finds : int list -> nat list
val finds : ufe -> nat list -> ufe 

val mk_unions : (int * int) list -> (nat * nat) list
val unions : ufe -> (nat * nat) list -> ufe

val mk_explains : (int * int) list -> (nat * nat) list
val explains : ufe -> (nat * nat) list -> ufe

end

functor Ufe_More(structure Ufe : UFE_SIG) :> UFE_MORE =
struct
open Ufe

val mk_finds = map nat_of_int

fun finds ufe [] = ufe 
  | finds ufe (x :: fs) = (find (ufe, x); finds ufe fs)

val mk_unions = map (fn (x, y) => (nat_of_int x, nat_of_int y))

fun unions ufe [] = ufe
  | unions ufe ((x, y) :: us) = unions (union (ufe, x, y)) us

val mk_explains = map (fn (x, y) => (nat_of_int x, nat_of_int y))

fun explains ufe [] = ufe 
  | explains ufe ((x, y) :: es) = (explain (ufe, x, y); explains ufe es) 

end