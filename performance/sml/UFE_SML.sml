structure Ufe_Sml :> UFE_SIG =
struct

type nat = UFE.nat 
type ufe = unit UFE.ufe_c_imp_ext 

val nat_of_int = UFE.nat_of_integer o IntInf.fromInt

fun init n = UFE.ufe_c_imp_init n () 

fun find (ufe, x) = UFE.ufe_c_imp_rep_of ufe x ()
fun union (ufe, x, y) = UFE.ufe_c_imp_union_size ufe x y ()
fun explain (ufe, x, y) = (UFE.explain_partial_imp ufe x y (); ())

end