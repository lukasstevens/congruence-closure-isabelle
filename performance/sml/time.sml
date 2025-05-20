datatype operation =
  Union of (int * int) |
  Find  of int |
  Explain of (int * int) 

fun nat_of_int x = UFE.nat_of_integer (IntInf.fromInt x)

fun readFile filename : (int * operation list) =
  let
    val ins = TextIO.openIn filename

    fun readline () = Option.valOf (TextIO.inputLine ins)

    fun parseInt s = Option.valOf (Int.fromString s)

    fun processLineInit line =
      let
        val ["init", nStr] = String.tokens (Char.isSpace) line
      in 
        parseInt nStr
      end

    fun processLine line =
      case String.tokens (fn c => Char.isSpace c) line of
          ["union", xStr, yStr] =>
            let
              val x = parseInt xStr
              val y = parseInt yStr
            in
              Union (x, y)
            end
        | ["find", xStr] =>
            let
              val x = parseInt xStr
            in
              Find x 
            end
        | ["explain", xStr, yStr] =>
            let
              val x = parseInt xStr
              val y = parseInt yStr
            in
              Explain (x, y) 
            end
    val n = processLineInit (readline ())
    val c = parseInt (readline ())
    fun go 0 acc : operation list = List.rev acc 
      | go i acc = go (i - 1) (processLine (readline ()) :: acc)
  in 
    (n, go c [])
  end

fun main ()  =
  let
    fun execute ([] : operation list) _ : unit = () 
      | execute (Union (x, y) :: os) ufe =
          execute os (UFE.ufe_c_imp_union_size ufe (nat_of_int x) (nat_of_int y) ())
      | execute (Find x :: os) ufe = execute os (UFE.ufe_c_imp_rep_of ufe (nat_of_int x) (); ufe)
      | execute (Explain (x, y) :: os) ufe =
        execute os (UFE.explain_partial_imp ufe (nat_of_int x) (nat_of_int y) (); ufe)

    val (n, ops) = readFile (List.hd (CommandLine.arguments ()))
    val timer = Timer.startCPUTimer () 
    val _ = execute ops (UFE.ufe_c_imp_init (nat_of_int n) ())
    val {usr = usr, sys = sys} = Timer.checkCPUTimer timer

    fun execute_C ([] : operation list) _ : unit = () 
      | execute_C (Union (x, y) :: os) ufe = execute_C os (Ufe_C.union (ufe, x, y); ufe)
      | execute_C (Find x :: os) ufe = execute_C os (Ufe_C.find (ufe, x); ufe)
      | execute_C (Explain (x, y) :: os) ufe = execute_C os (Ufe_C.explain (ufe, x, y); ufe)
    val timer_C = Timer.startCPUTimer () 
    val _ = execute_C ops (Ufe_C.new n)
    val {usr = usr_C, sys = sys_C} = Timer.checkCPUTimer timer_C
  in
    (print ("usr: " ^ Time.toString usr ^ "\t" ^ "sys: " ^ Time.toString sys ^ "\n");
    print ("usr: " ^ Time.toString usr_C ^ "\t" ^ "sys: " ^ Time.toString sys_C ^ "\n"))
  end;
main ()
