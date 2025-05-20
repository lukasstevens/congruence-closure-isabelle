signature DYN_LINK =
sig
   type hndl
   type mode
   type fptr

   val dlopen : string * mode -> hndl
   val dlsym : hndl * string -> fptr
   val dlclose : hndl -> unit

   val RTLD_LAZY : mode
   val RTLD_NOW : mode
end

structure DynLink :> DYN_LINK =
struct
   type hndl = MLton.Pointer.t
   type mode = Word32.word
   type fptr = MLton.Pointer.t

   (* These symbols come from a system libray, so the default import scope
    * of external is correct.
    *)
   val dlopen =
      _import "dlopen" : string * mode -> hndl;
   val dlerror =
      _import "dlerror": unit -> MLton.Pointer.t;
   val dlsym =
      _import "dlsym" : hndl * string -> fptr;
   val dlclose =
      _import "dlclose" : hndl -> Int32.int;

   val RTLD_LAZY = 0wx00001 (* Lazy function call binding.  *)
   val RTLD_NOW  = 0wx00002 (* Immediate function call binding.  *)

   val dlerror = fn () =>
      let
         val addr = dlerror ()
      in
         if addr = MLton.Pointer.null
            then NONE
            else let
                    fun loop (index, cs) =
                       let
                          val w = MLton.Pointer.getWord8 (addr, index)
                          val c = Byte.byteToChar w
                       in
                          if c = #"\000"
                             then SOME (implode (rev cs))
                             else loop (index + 1, c::cs)
                       end
                 in
                    loop (0, [])
                 end
      end

   val dlopen = fn (filename, mode) =>
      let
         val filename = filename ^ "\000"
         val hndl = dlopen (filename, mode)
      in
         if hndl = MLton.Pointer.null
            then raise Fail (case dlerror () of
                                NONE => "???"
                              | SOME s => s)
            else hndl
      end

   val dlsym = fn (hndl, symbol) =>
      let
         val symbol = symbol ^ "\000"
         val fptr = dlsym (hndl, symbol)
      in
         case dlerror () of
            NONE => fptr
          | SOME s => raise Fail s
      end

   val dlclose = fn hndl =>
      if MLton.Platform.OS.host = MLton.Platform.OS.Darwin
         then ()  (* Darwin reports the following error message if you
                   * try to close a dynamic library.
                   *   "dynamic libraries cannot be closed"
                   * So, we disable dlclose on Darwin.
                   *)
      else
         let
            val res = dlclose hndl
         in
            if res = 0
               then ()
            else raise Fail (case dlerror () of
                                NONE => "???"
                              | SOME s => s)
         end
end

signature UFE_C =
sig

val new : int -> MLton.Pointer.t
val delete : MLton.Pointer.t -> unit

val find : (MLton.Pointer.t * int) -> int
val union : (MLton.Pointer.t * int * int) -> unit
val explain : (MLton.Pointer.t * int * int) -> unit

end

structure Ufe_C :> UFE_C =
struct

val dll = "./UFE.so"
val hndl = DynLink.dlopen (dll, DynLink.RTLD_NOW)

local
   val call = _import * : DynLink.fptr -> int -> MLton.Pointer.t;
   val UFE_New_fptr = DynLink.dlsym (hndl, "UFE_New")
in
   val new = call UFE_New_fptr 
end

local
   val call = _import * : DynLink.fptr -> MLton.Pointer.t -> unit;
   val UFE_Delete_fptr = DynLink.dlsym (hndl, "UFE_Delete")
in
   val delete = call UFE_Delete_fptr 
end

local
   val call = _import * : DynLink.fptr -> (MLton.Pointer.t * int) -> int;
   val UFE_find_fptr = DynLink.dlsym (hndl, "UFE_find")
in
   val find = call UFE_find_fptr 
end

local
   val call = _import * : DynLink.fptr -> (MLton.Pointer.t * int * int) -> unit;
   val UFE_union_fptr = DynLink.dlsym (hndl, "UFE_union")
in
   val union = call UFE_union_fptr 
end

local
   val call = _import * : DynLink.fptr -> (MLton.Pointer.t * int * int) -> unit;
   val UFE_explain_fptr = DynLink.dlsym (hndl, "UFE_explain")
in
   val explain = call UFE_explain_fptr 
end

end
