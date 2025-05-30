(*  Title:      HOL/Library/LaTeXsugar.thy
    Author:     Gerwin Klein, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(*<*)
theory LaTeXsugar
imports Main
begin

definition mbox :: "'a \<Rightarrow> 'a" where
  [simp]: "mbox x = x"
definition mbox0 :: "'a \<Rightarrow> 'a" where
  [simp]: "mbox0 x = x"

notation (latex) mbox ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>" [999] 999)
notation (latex) mbox0 ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>" [0] 999)


(* DUMMY *)
consts DUMMY :: 'a (\<open>\<^latex>\<open>\_\<close>\<close>)

(* THEOREMS *)
notation (Rule output)
  Pure.imp  (\<open>\<^latex>\<open>\mbox{}\inferrule{\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\mbox{\<close>_\<^latex>\<open>}}\<close>\<close>)

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>\mbox{}\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\mbox{\<close>_\<^latex>\<open>}}\<close>\<close>)

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\\\<close>/ _\<close>)

  "_asm" :: "prop \<Rightarrow> asms" (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close>\<close>)

notation (Axiom output)
  "Trueprop"  (\<open>\<^latex>\<open>\mbox{}\inferrule{\mbox{}}{\mbox{\<close>_\<^latex>\<open>}}\<close>\<close>)

notation (IfThen output)
  Pure.imp  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _/ \<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)
syntax (IfThen output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _ /\<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close> /\<^latex>\<open>{\normalsize \,\<close>and\<^latex>\<open>\,}\<close>/ _\<close>)
  "_asm" :: "prop \<Rightarrow> asms" (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close>\<close>)

notation (IfThenNoBox output)
  Pure.imp  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _/ \<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)
syntax (IfThenNoBox output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _ /\<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" (\<open>_ /\<^latex>\<open>{\normalsize \,\<close>and\<^latex>\<open>\,}\<close>/ _\<close>)
  "_asm" :: "prop \<Rightarrow> asms" (\<open>_\<close>)

setup \<open>
  Document_Output.antiquotation_pretty_source \<^binding>\<open>const_typ\<close>
    (Scan.lift Parse.embedded_inner_syntax)
    (fn ctxt => fn c =>
      let val tc = Proof_Context.read_const {proper = false, strict = false} ctxt c in
        Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
          Pretty.brk 1, Syntax.pretty_typ ctxt (fastype_of tc)]
      end)
\<close>
(* Parenthesize conjunctions to the left; otherwise, if a larger conjunction needs a line break,
the pretty printer will put the first few conjuncts on separate lines until the rest fits. *)
syntax (output)
  "_conjL" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "\<and>" 35)
syntax (latex output)
  "_conjL" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "\<and>" 35)
translations
  "_conjL P Q" <= "P \<and> Q" 
  "_conjL (_conjL P Q) R" <= "_conjL P (_conjL Q R)"
(* The above regrouping of conjunctions may have the opposite effect, the last few conjuncts ending up
on separate lines. However, it appears beneficial in the majority of cases *)

(* For manual regrouping with invisible blocks: *)
definition BLOCK where [simp]: "BLOCK x = x"
notation (output) BLOCK ("_")

(* set comprehension *)
syntax (output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ | _})")
  "_CollectIn" :: "pttrn => 'a set => bool => 'a set"   ("(1{_ \<in> _ | _})")
syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ | _})")
  "_CollectIn" :: "pttrn => 'a set => bool => 'a set"   ("(1{_ \<in> _ | _})")
translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"
  "_CollectIn p A P"  <= "{p : A. P}"

notation (latex output)
  size  ("|_|")

notation (latex output)
  length  ("|_|")

notation (latex output)
  card ("|_|")


(* Forced parentheses *)
definition parens where
  [simp]: "parens x = x"

notation (output) parens ("\<^bold>'(_\<^bold>')")

notation (latex output) parens
  ("'(_')")

definition BREAK where
  [simp]: "BREAK x = x"

notation (latex output) BREAK ("\<^latex>\<open>\\\\\<close>(_)")


(* controlling breaks after +/=/\<Longrightarrow> *)
definition plus_break (infixl "+\<^sub>b" 65) where [simp]: "plus_break = (+)"
notation (output) plus_break ("_ +//_" [65, 66] 65)

definition plus_nobreak (infixl "+\<^sub>n\<^sub>b" 65) where [simp]: "plus_nobreak = (+)"
notation (output) plus_nobreak ("_ + _" [65, 66] 65)

definition eq_break (infixl "=\<^sub>b" 65) where [simp]: "eq_break = (=)"
notation (output) eq_break ("_//= _" [50, 51] 50)

definition implies_break (infixr "\<longrightarrow>\<^sub>b" 25) where [simp]: "implies_break = (\<longrightarrow>)"
notation (output) implies_break ("_ \<longrightarrow>//_" [26, 25] 25)

definition defeq
  where [simp]: "defeq = (=)"

notation (output) defeq (infixl ":=" 50)

syntax (latex output)
  "_UNION"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set" 
  ("(3\<^latex>\<open>\\bigop{\\bigcup}{\\altin}{\<close>_\<^latex>\<open>}{\<close>_\<^latex>\<open>}\<close>/ _)" [0, 51, 10] 10)

syntax (latex output)
  "_INTER"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set" 
  ("(3\<^latex>\<open>\\bigop{\\bigcap}{\\altin}{\<close>_\<^latex>\<open>}{\<close>_\<^latex>\<open>}\<close>/ _)" [0, 51, 10] 10)


notation (latex output)
  If  ("(\<^latex>\<open>\\isakeywordONE{\<close>if\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\isakeywordONE{\<close>then\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\isakeywordONE{\<close>else\<^latex>\<open>}\<close> (_))" 10)

syntax (latex output)
  "_Let"        :: "[letbinds, 'a] => 'a"
  ("(\<^latex>\<open>\\isakeywordONE{\<close>let\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\isakeywordONE{\<close>in\<^latex>\<open>}\<close> (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^latex>\<open>\\isakeywordONE{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\\isakeywordONE{\<close>of\<^latex>\<open>}\<close>/ _)" 10)

syntax (let_break output)
  "_binds" :: "[letbind, letbinds] \<Rightarrow> letbinds"  ("_;//_")

syntax (case_break output)
  "_case2" :: "[case_syn, cases_syn] \<Rightarrow> cases_syn"  ("_ |//_")

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^latex>\<open>\\isakeywordONE{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\\isakeywordONE{\<close>of\<^latex>\<open>}\<close>//_)" 10)

abbreviation (iffSpace)
  iffSpace :: "[bool, bool] => bool"  (infixr "\<^latex>\<open>\\ \<close>\<longleftrightarrow>\<^latex>\<open>\\ \<close>" 25)
where
  "iffSpace A B == A = B"

abbreviation (iffText)
  iffText :: "[bool, bool] => bool"  (infixr "\<^latex>\<open>\\emph{iff}\<close>" 25)
where
  "iffText A B == A = B"

setup \<open>
  Document_Output.antiquotation_pretty_source \<^binding>\<open>typ_of_const\<close>
    (Scan.lift Parse.embedded_inner_syntax)
    (fn ctxt => fn c =>
      let val tc = Proof_Context.read_const {proper = false, strict = false} ctxt c in
        Syntax.pretty_typ ctxt (fastype_of tc)
      end)
\<close>

ML \<open>
fun dummy_pats_style (wrap $ (eq $ lhs $ rhs)) =
  let
    val rhs_vars = Term.add_vars rhs [];
    fun dummy (t as Var (v as (_, T))) =
          if member ((=) ) rhs_vars v then t else Const (@{const_name DUMMY}, T)
      | dummy (t $ u) = dummy t $ dummy u
      | dummy (Abs (n, T, b)) = Abs (n, T, dummy b)
      | dummy t = t;
  in wrap $ (eq $ dummy lhs $ rhs) end
\<close>

setup\<open>
Term_Style.setup @{binding dummy_pats} (Scan.succeed (K dummy_pats_style))
\<close>

(* Dummy vars on lhs in case expressions: *)
syntax (output)
  "_case1'" :: "['a, 'b] \<Rightarrow> case_syn"  ("(2_ \<Rightarrow>/ _)" 10)

print_ast_translation \<open>
  let
    fun vars (Ast.Constant _) = []
      | vars (Ast.Variable x) = [x]
      | vars (Ast.Appl ts) = flat(map vars ts);
    fun dummy vs (Ast.Appl ts) = Ast.Appl(map (dummy vs) ts)
      | dummy vs (Ast.Variable x) = Ast.Variable (if member (op =) vs x then x else "_")
      | dummy _ c = c
    fun case1_tr' [l,r] =
          Ast.Appl [Ast.Constant @{syntax_const "_case1'"}, dummy (vars r) l, r]
  in [(\<^syntax_const>\<open>_case1\<close>, K case1_tr')] end
\<close>

setup \<open>
let

fun eta_expand Ts t xs = case t of
    Abs(x,T,t) =>
      let val (t', xs') = eta_expand (T::Ts) t xs
      in (Abs (x, T, t'), xs') end
  | _ =>
      let
        val (a,ts) = strip_comb t (* assume a atomic *)
        val (ts',xs') = fold_map (eta_expand Ts) ts xs
        val Bs = binder_types (fastype_of1 (Ts,t));
        val n = Int.min (length Bs, length xs');
        val bs = map Bound ((n - 1) downto 0);
        val xBs = ListPair.zip (xs',Bs);
        val xs'' = drop n xs';
        val t' = incr_boundvars n (list_comb (a, ts'));
        val t'' = fold_rev Term.abs xBs (list_comb(t', bs))
      in (t'', xs'') end

val style_eta_expand =
  (Scan.repeat Args.name) >> (fn xs => fn ctxt => fn t => fst (eta_expand [] t xs))

in Term_Style.setup @{binding eta_expand} style_eta_expand end
\<close>

setup \<open>
  Document_Output.antiquotation_pretty_embedded \<^binding>\<open>const_name\<close>
    (Args.const {proper = true, strict = false})
    (fn ctxt => fn c => Pretty.mark_str (Markup.const, Proof_Context.extern_const ctxt c))
\<close>

ML \<open>
fun pretty_const_typ ctxt (c, maybe_typ) : Pretty.T =
  (*taken from Prog_Prove/LaTeXsugar.thy*)
  let
    val tc = Proof_Context.read_const {proper = true, strict = false} ctxt c
    val pretty_typ =
      (case maybe_typ of
        NONE => Syntax.pretty_typ ctxt (fastype_of tc)
      | SOME typ =>
        let val typ_instance = Type.typ_instance o Proof_Context.tsig_of in
          if typ_instance ctxt (Syntax.check_typ ctxt typ, fastype_of tc) then Syntax.pretty_typ ctxt typ
          else error ("constant " ^ quote (Proof_Context.markup_const ctxt c) ^ " is not of type " ^
            quote (Syntax.string_of_typ ctxt typ))
        end)
  in
    Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
    Pretty.brk 1, pretty_typ]
  end

fun pretty_eqs_style (f:Proof.context -> string -> term list) ctxt (style, (name, maybe_thms)) : Pretty.T =
  let
    fun pretty_eq t1 t2 =
      Pretty.block [
        Document_Output.pretty_term ctxt t1,
        Pretty.str " =", Pretty.brk_indent 1 1,
        Document_Output.pretty_term ctxt t2]
    fun eq \<^Const>\<open>Pure.eq _ for t1 t2\<close> = pretty_eq t1 t2
      | eq \<^Const>\<open>Trueprop for \<^Const>\<open>HOL.eq _ for t1 t2\<close>\<close> = pretty_eq t1 t2
    val eq = eq o style
  in
    (case maybe_thms of
      SOME thms => map eq thms |> Pretty.chunks
    | NONE =>
      f ctxt name
      |> map eq
      |> Pretty.chunks)
  end

fun separate_texts (sep: Latex.text) (texts: Latex.text list) : Latex.text =
  separate sep texts |> List.concat

fun gen_pretty_funs_style_generic print_header f ctxt (style, names) : Latex.text =
  names
  |> map (fn ((name, typ), eqs) =>
    let
      val thy_output = Document_Output.pretty ctxt
      val equations = pretty_eqs_style f ctxt (style, (name, eqs)) |> thy_output
      val header = pretty_const_typ ctxt (name, typ) |> thy_output
    in if print_header then separate_texts (Latex.string "\\\\[\\funheadersep]" ) [header, equations] else equations end)
  |> separate_texts (Latex.string "\\\\\\\\")
  |> XML.enclose "{\\parindent0pt" "}"

val pretty_funs_style_generic = gen_pretty_funs_style_generic true
\<close>

setup \<open>
let
 val parse =
  Args.const {proper = true, strict = false} --
  Scan.option (Scan.lift (Args.$$$ "::") |-- Args.typ_abbrev) --
  Scan.option (Scan.lift (Args.$$$ "[") |-- (Attrib.thms >> map Thm.full_prop_of) --| Scan.lift (Args.$$$ "]"))
 fun eqns suf ctxt n = map Thm.full_prop_of (Proof_Context.get_thms ctxt (n ^ suf))
 fun input_eqns ctxt n = #input_eqns (Function.get_info ctxt (Syntax.read_term ctxt n))
in
  Document_Output.antiquotation_raw \<^binding>\<open>def\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic (eqns "_def"))
  #> Document_Output.antiquotation_raw \<^binding>\<open>def_no_typ\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> gen_pretty_funs_style_generic false (eqns "_def"))
  #> Document_Output.antiquotation_raw \<^binding>\<open>fun\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic (eqns ".simps"))
  #> Document_Output.antiquotation_raw \<^binding>\<open>fun_input\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic input_eqns)
end
\<close>

end
(*>*)
