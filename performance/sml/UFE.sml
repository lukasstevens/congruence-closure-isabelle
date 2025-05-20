structure IntInf = Int

   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()



structure UFE : sig
  type int
  type nat
  datatype 'a eq_prf = AssmP of nat | ReflP of 'a |
    TransP of 'a eq_prf * 'a eq_prf | SymP of 'a eq_prf
  type 'a ufe_imp_ext
  type 'a ufe_c_imp_ext
  val nat_of_integer : IntInf.int -> nat
  val ufe_c_imp_init : nat -> (unit -> unit ufe_c_imp_ext)
  val ufe_c_imp_rep_of : unit ufe_c_imp_ext -> nat -> (unit -> nat)
  val explain_partial_imp :
    unit ufe_c_imp_ext -> nat -> nat -> (unit -> (nat eq_prf option))
  val ufe_c_imp_union_size :
    unit ufe_c_imp_ext -> nat -> nat -> (unit -> unit ufe_c_imp_ext)
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype int = Int_of_integer of IntInf.int;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : int countable;

val typerep_int = {typerep = typerep_inta} : int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  int heap;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

val default_nata : nat = zero_nata;

type 'a default = {default : 'a};
val default = #default : 'a default -> 'a;

val default_nat = {default = default_nata} : nat default;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun minus_nata m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

fun less_eq_option A_ (SOME x) (SOME y) = less_eq (ord_preorder A_) x y
  | less_eq_option A_ (SOME x) NONE = false
  | less_eq_option A_ NONE x = true;

fun less_option A_ (SOME x) (SOME y) = less (ord_preorder A_) x y
  | less_option A_ NONE (SOME x) = true
  | less_option A_ x NONE = false;

fun ord_option A_ = {less_eq = less_eq_option A_, less = less_option A_} :
  ('a option) ord;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

fun default_proda A_ B_ = (default A_, default B_);

fun default_prod A_ B_ = {default = default_proda A_ B_} : ('a * 'b) default;

datatype 'a eq_prf = AssmP of nat | ReflP of 'a |
  TransP of 'a eq_prf * 'a eq_prf | SymP of 'a eq_prf;

datatype 'a ufe_imp_ext =
  Ufe_imp_ext of
    int array * (nat option) array * ((nat * nat) array * nat) * 'a;

datatype 'a ufe_c_imp_ext = Ufe_c_imp_ext of unit ufe_imp_ext * int array * 'a;

fun eq A_ a b = equal A_ a b;

fun integer_of_int (Int_of_integer k) = k;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun nat x = (nat_of_integer o integer_of_int) x;

fun len A_ a =
  (fn () => let
              val i = (fn () => IntInf.fromInt (Array.length a)) ();
            in
              nat_of_integer i
            end);

fun new A_ =
  (fn a => fn b => (fn () => Array.array (IntInf.toInt a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update (a, IntInf.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun the (SOME x2) = x2;

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun ufsi_imp_parent_of ufsi_imp i =
  (fn () => let
              val n = nth heap_int ufsi_imp i ();
            in
              (if less_int n zero_int then i else nat n)
            end);

fun uf_ds_i (Ufe_imp_ext (uf_ds_i, au_ds_i, unions_i, more)) = uf_ds_i;

fun au_ds_i (Ufe_imp_ext (uf_ds_i, au_ds_i, unions_i, more)) = au_ds_i;

fun find_newest_on_path_acc_imp ufe_imp y x acc =
  (if equal_nata y x then (fn () => acc)
    else (fn () =>
           let
             val au_x = nth (heap_option heap_nat) (au_ds_i ufe_imp) x ();
             val px = ufsi_imp_parent_of (uf_ds_i ufe_imp) x ();
           in
             find_newest_on_path_acc_imp ufe_imp y px
               (max (ord_option preorder_nat) au_x acc) ()
           end));

fun find_newest_on_path_imp ufe_imp y x =
  find_newest_on_path_acc_imp ufe_imp y x NONE;

fun unions_i (Ufe_imp_ext (uf_ds_i, au_ds_i, unions_i, more)) = unions_i;

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun arl_append (A1_, A2_) =
  (fn (a, n) => fn x => fn () =>
    let
      val lena = len A2_ a ();
    in
      (if less_nat n lena
        then (fn f_ => fn () => f_ ((upd A2_ n x a) ()) ())
               (fn aa => (fn () => (aa, plus_nat n one_nata)))
        else let
               val newcap = times_nat (nat_of_integer (2 : IntInf.int)) lena;
             in
               (fn f_ => fn () => f_ ((array_grow A2_ a newcap (default A1_))
                 ()) ())
                 (fn aa =>
                   (fn f_ => fn () => f_ ((upd A2_ n x aa) ()) ())
                     (fn ab => (fn () => (ab, plus_nat n one_nata))))
             end)
        ()
    end);

fun ufsi_imp_awalk_verts_from_rep_acc ufsi x vs =
  (fn () =>
    let
      val px = ufsi_imp_parent_of ufsi x ();
    in
      (if equal_nata px x then arl_append (default_nat, heap_nat) vs x
        else (fn f_ => fn () => f_ ((arl_append (default_nat, heap_nat) vs x)
               ()) ())
               (ufsi_imp_awalk_verts_from_rep_acc ufsi px))
        ()
    end);

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

fun ufsi_imp_awalk_verts_from_rep ufsi x =
  (fn () => let
              val xa = arl_empty (default_nat, heap_nat) zero_nat ();
            in
              ufsi_imp_awalk_verts_from_rep_acc ufsi x xa ()
            end);

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nata n zero_nata)));

fun arl_last A_ = (fn (a, n) => nth A_ a (minus_nata n one_nata));

fun arl_butlast (B1_, B2_) =
  (fn (a, n) => (fn () => (a, minus B1_ n (one B2_))));

fun hd_longest_common_suffix_aux (A1_, A2_) vsx vsy x =
  (fn () =>
    let
      val evsx = arl_is_empty A2_ vsx ();
      val evsy = arl_is_empty A2_ vsy ();
    in
      (if evsx orelse evsy then (fn () => x)
        else (fn f_ => fn () => f_ ((arl_last A2_ vsx) ()) ())
               (fn lx =>
                 (fn f_ => fn () => f_ ((arl_last A2_ vsy) ()) ())
                   (fn ly =>
                     (if not (eq A1_ lx ly) then (fn () => x)
                       else (fn f_ => fn () => f_
                              ((arl_butlast (minus_nat, one_nat) vsx) ()) ())
                              (fn vsxa =>
                                (fn f_ => fn () => f_
                                  ((arl_butlast (minus_nat, one_nat) vsy) ())
                                  ())
                                  (fn vsya =>
                                    hd_longest_common_suffix_aux (A1_, A2_) vsxa
                                      vsya lx))))))
        ()
    end);

fun ufsi_imp_lca ufsi_imp x y =
  (fn () =>
    let
      val vx = ufsi_imp_awalk_verts_from_rep ufsi_imp x ();
      val vy = ufsi_imp_awalk_verts_from_rep ufsi_imp y ();
    in
      hd_longest_common_suffix_aux (equal_nat, heap_nat) vx vy zero_nata ()
    end);

fun arl_get A_ = (fn (a, _) => nth A_ a);

fun explain_imp ufe_imp x y =
  (if equal_nata x y then (fn () => (ReflP x))
    else (fn () =>
           let
             val lca = ufsi_imp_lca (uf_ds_i ufe_imp) x y ();
             val newest_x = find_newest_on_path_imp ufe_imp lca x ();
             val newest_y = find_newest_on_path_imp ufe_imp lca y ();
           in
             (if less_eq_option preorder_nat newest_y newest_x
               then (fn f_ => fn () => f_
                      ((arl_get (heap_prod heap_nat heap_nat) (unions_i ufe_imp)
                         (the newest_x))
                      ()) ())
                      (fn (ax, bx) =>
                        (fn f_ => fn () => f_ ((explain_imp ufe_imp x ax) ())
                          ())
                          (fn pxax =>
                            (fn f_ => fn () => f_ ((explain_imp ufe_imp bx y)
                              ()) ())
                              (fn pbxy =>
                                (fn () =>
                                  (TransP
                                    (TransP (pxax, AssmP (the newest_x)),
                                      pbxy))))))
               else (fn f_ => fn () => f_
                      ((arl_get (heap_prod heap_nat heap_nat) (unions_i ufe_imp)
                         (the newest_y))
                      ()) ())
                      (fn (ay, by) =>
                        (fn f_ => fn () => f_ ((explain_imp ufe_imp x by) ())
                          ())
                          (fn pxby =>
                            (fn f_ => fn () => f_ ((explain_imp ufe_imp ay y)
                              ()) ())
                              (fn payy =>
                                (fn () =>
                                  (TransP
                                    (TransP (pxby, SymP (AssmP (the newest_y))),
                                      payy)))))))
               ()
           end));

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

val one_int : int = Int_of_integer (1 : IntInf.int);

fun ufsi_imp_init n = new heap_int n (uminus_int one_int);

fun ufe_imp_init n =
  (fn () =>
    let
      val uf = ufsi_imp_init n ();
      val au = new (heap_option heap_nat) n NONE ();
      val us =
        arl_empty
          (default_prod default_nat default_nat, heap_prod heap_nat heap_nat)
          zero_nat ();
    in
      Ufe_imp_ext (uf, au, us, ())
    end);

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun ufsi_imp_link ufsi_imp rep_x rep_y sz =
  (fn () => let
              val _ = upd heap_int rep_x (int_of_nat rep_y) ufsi_imp ();
            in
              upd heap_int rep_y (uminus_int (int_of_nat sz)) ufsi_imp ()
            end);

fun arl_length A_ = (fn (_, a) => (fn () => a));

fun ufe_imp_link ufe_imp x y rep_x rep_y sz =
  (fn () =>
    let
      val len = arl_length (heap_prod heap_nat heap_nat) (unions_i ufe_imp) ();
      val uf = ufsi_imp_link (uf_ds_i ufe_imp) rep_x rep_y sz ();
      val au = upd (heap_option heap_nat) rep_x (SOME len) (au_ds_i ufe_imp) ();
      val us =
        arl_append
          (default_prod default_nat default_nat, heap_prod heap_nat heap_nat)
          (unions_i ufe_imp) (x, y) ();
    in
      Ufe_imp_ext (uf, au, us, ())
    end);

fun ufe_c_imp_init n = (fn () => let
                                   val ufe = ufe_imp_init n ();
                                   val ufsi = ufsi_imp_init n ();
                                 in
                                   Ufe_c_imp_ext (ufe, ufsi, ())
                                 end);

fun uf_c_ds_i (Ufe_c_imp_ext (ufe_i, uf_c_ds_i, more)) = uf_c_ds_i;

fun ufe_i (Ufe_c_imp_ext (ufe_i, uf_c_ds_i, more)) = ufe_i;

fun ufe_c_imp_link ufe_c_imp x y rep_x rep_y sz =
  (fn () =>
    let
      val ufe_imp = ufe_imp_link (ufe_i ufe_c_imp) x y rep_x rep_y sz ();
      val ufsi_imp = ufsi_imp_link (uf_c_ds_i ufe_c_imp) rep_x rep_y sz ();
    in
      Ufe_c_imp_ext (ufe_imp, ufsi_imp, ())
    end);

fun ufsi_imp_size ufsi_imp x =
  (fn () =>
    let
      val sz = nth heap_int ufsi_imp x ();
    in
      (if less_int sz zero_int then (fn () => (nat (uminus_int sz)))
        else (fn () => zero_nata))
        ()
    end);

fun ufe_c_imp_size ufe_c_imp = ufsi_imp_size (uf_c_ds_i ufe_c_imp);

fun ufsi_imp_compress ufsi_imp i rep_i =
  (if equal_nata rep_i i then (fn () => ufsi_imp)
    else upd heap_int i (int_of_nat rep_i) ufsi_imp);

fun ufsi_imp_rep_of_c ufsi_imp i =
  (fn () =>
    let
      val pi = ufsi_imp_parent_of ufsi_imp i ();
    in
      (if equal_nata pi i then (fn () => i)
        else (fn f_ => fn () => f_ ((ufsi_imp_rep_of_c ufsi_imp pi) ()) ())
               (fn rep_i =>
                 (fn f_ => fn () => f_ ((ufsi_imp_compress ufsi_imp i rep_i) ())
                   ())
                   (fn _ => (fn () => rep_i))))
        ()
    end);

fun ufe_c_imp_rep_of ufe_c_imp = ufsi_imp_rep_of_c (uf_c_ds_i ufe_c_imp);

fun explain_partial_imp ufe_c_imp x y =
  (if equal_nata x y then (fn () => (SOME (ReflP x)))
    else (fn () =>
           let
             val n = len heap_int (uf_ds_i (ufe_i ufe_c_imp)) ();
           in
             (if less_nat x n andalso less_nat y n
               then (fn f_ => fn () => f_ ((ufe_c_imp_rep_of ufe_c_imp x) ())
                      ())
                      (fn rep_x =>
                        (fn f_ => fn () => f_ ((ufe_c_imp_rep_of ufe_c_imp y)
                          ()) ())
                          (fn rep_y =>
                            (if equal_nata rep_x rep_y
                              then (fn f_ => fn () => f_
                                     ((explain_imp (ufe_i ufe_c_imp) x y) ())
                                     ())
                                     (fn p => (fn () => (SOME p)))
                              else (fn () => NONE))))
               else (fn () => NONE))
               ()
           end));

fun ufe_c_imp_union_size ufe_c_imp x y =
  (fn () =>
    let
      val rep_x = ufe_c_imp_rep_of ufe_c_imp x ();
      val rep_y = ufe_c_imp_rep_of ufe_c_imp y ();
    in
      (if equal_nata rep_x rep_y then (fn () => ufe_c_imp)
        else (fn f_ => fn () => f_ ((ufe_c_imp_size ufe_c_imp rep_x) ()) ())
               (fn sz_rep_x =>
                 (fn f_ => fn () => f_ ((ufe_c_imp_size ufe_c_imp rep_y) ()) ())
                   (fn sz_rep_y =>
                     (if less_nat sz_rep_x sz_rep_y
                       then ufe_c_imp_link ufe_c_imp x y rep_x rep_y
                              (plus_nat sz_rep_x sz_rep_y)
                       else ufe_c_imp_link ufe_c_imp y x rep_y rep_x
                              (plus_nat sz_rep_y sz_rep_x)))))
        ()
    end);

end; (*struct UFE*)
