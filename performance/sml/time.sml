structure Ufe_Bench_Base =
struct

fun upt n = 
  let
    fun go 0 acc = acc
      | go n acc = go (n - 1) ((n - 1) :: acc)
  in
    go n [] 
  end

fun pow 0 0 = 1
  | pow b 0 = 1
  | pow b e = b * pow b (e - 1)

fun wide_tree n = map (fn x => (x, x + 1)) (upt (pow 2 n - 1))

fun balanced_tree_tr 0 k = k [] 
  | balanced_tree_tr n k =
      balanced_tree_tr (n - 1) 
        (fn xs' => k (
          map (fn x => (2 * x, 2 * x + 1)) (upt (pow 2 (n - 1))) @
          map (fn (x, y) => (2 * x, 2 * y)) xs')
        )
fun balanced_tree n = balanced_tree_tr n (fn xs => xs)

val _ = MLton.Random.srand (Word.fromInt 1337)

local
   val r: word ref = ref 0w0
   val max: word ref = ref 0w0
in
   fun wordLessThan (w: word): word =
         let
            val () =
               if w - 0w1 <= !max
                  then ()
               else (r := MLton.Random.rand ()
                     ; max := Word.notb 0wx0)
            val w' = !r
            val () = r := Word.div (w', w)
            val () = max := Word.div (!max, w)
         in
            Word.mod (w', w)
         end
end

fun natLessThan (n: int): int = Word.toInt (wordLessThan (Word.fromInt n))

fun gen_explain n = (natLessThan (pow 2 n), natLessThan (pow 2 n)) 

fun gen_explains c n = map (fn _ => gen_explain n) (upt c)

end

functor Ufe_Bench(structure Ufe : UFE_MORE) =
struct 

open Ufe_Bench_Base

fun bench_unions ufe gen_unions n =
  let
    val us = Ufe.mk_unions (gen_unions n)
    val timer = Timer.startRealTimer ()
    val ufe = Ufe.unions ufe us 
    val time = Timer.checkRealTimer timer
  in
    (ufe, time)
  end


fun bench_explains ufe gen_explains n =
  let
    val es = Ufe.mk_explains (gen_explains n) 
    val timer = Timer.startRealTimer ()
    val ufe = Ufe.explains ufe es
    val time = Timer.checkRealTimer timer
  in
    (ufe, time) 
  end

fun bench gen_unions gen_explains n =
  let
    val ufe = Ufe.init (Ufe.nat_of_int (pow 2 n))
    val (ufe, time_unions) = bench_unions ufe gen_unions n
    val (_, time_explains) = bench_explains ufe gen_explains n
  in
    (time_unions, time_explains) 
  end

end

structure Ufe_Sml_Bench = Ufe_Bench(structure Ufe = Ufe_More(structure Ufe = Ufe_Sml));
structure Ufe_C_Bench = Ufe_Bench(structure Ufe = Ufe_More(structure Ufe = Ufe_C));

let
  open Ufe_Bench_Base

  fun pair_toString toString (x, y) = "(" ^ toString x ^ ", " ^ toString y ^ ")"
  val int_pair_toString = pair_toString Int.toString

  val _ =
    if false 
      then (print (String.concatWith ", " (map int_pair_toString (wide_tree 4)) ^ "\n");
        print (String.concatWith ", " (map int_pair_toString (balanced_tree 4)) ^ "\n"))
      else ()

  val [lang, gen_tree, n_low, n_high] = CommandLine.arguments ()
  val bench =
    if lang = "C" then Ufe_C_Bench.bench else if lang = "SML" then Ufe_Sml_Bench.bench else raise Fail "unknown language" 
  val (gen_tree, gen_explains) = if gen_tree = "wide" then (wide_tree,
  gen_explains 1000) else if gen_tree = "balanced" then (balanced_tree,
  gen_explains 100000) else raise Fail "unkown tree generator"

  val n_low = Option.valOf (Int.fromString n_low)
  val n_high = Option.valOf (Int.fromString n_high)

  fun go n =
    if n > n_high then print "\n" 
    else
      let
        val (time_unions, time_explains) = bench gen_tree gen_explains n
        fun time_toString time = Time.fmt 3 time
        val _ = print ((if n > n_low then " & " else "") ^ time_toString time_unions ^ "/"  ^ time_toString time_explains)
      in 
        go (n + 1)
      end
in
  go n_low
end;
