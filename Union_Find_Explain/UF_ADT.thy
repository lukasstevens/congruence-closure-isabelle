theory UF_ADT
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
    "HOL-Statespace.StateSpaceSyntax"
begin

datatype ('uf, 'a) union_find_adt = Union_Find_ADT
  (init: 'uf)
  (rep_of: "'uf \<Rightarrow> 'a \<Rightarrow> 'a")
  (union: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'uf")
  (invar: "'uf \<Rightarrow> bool")
  (\<alpha>: "'uf \<Rightarrow> 'a rel")

hide_const (open) init rep_of union invar \<alpha>

datatype ('uf, 'a) union_find_parent_adt = Union_Find_Parent_ADT
  (init: 'uf)
  (rep_of: "'uf \<Rightarrow> 'a \<Rightarrow> 'a")
  (union: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'uf")
  (invar: "'uf \<Rightarrow> bool")
  (\<alpha>: "'uf \<Rightarrow> 'a rel")
  (parent_of: "'uf \<Rightarrow> 'a \<Rightarrow> 'a")

hide_const (open) init rep_of union invar \<alpha> parent_of

datatype ('uf, 'a) union_find_explain_adt = Union_Find_Explain_ADT
  (init: 'uf)
  (rep_of: "'uf \<Rightarrow> 'a \<Rightarrow> 'a")
  (union: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'uf")
  (invar: "'uf \<Rightarrow> bool")
  (\<alpha>: "'uf \<Rightarrow> 'a rel")
  (explain: "'uf \<Rightarrow> 'a \<Rightarrow> 'a")

hide_const (open) init rep_of union invar \<alpha> explain

consts
  init :: "'uf \<Rightarrow> 'a" ("init\<index>")
  rep_of :: "'uf \<Rightarrow> 'a" ("rep'_of\<index>")
  union :: "'uf \<Rightarrow> 'a" ("union\<index>")
  invar :: "'uf \<Rightarrow> 'a" ("invar\<index>")
  \<alpha> :: "'uf \<Rightarrow> 'a" ("\<alpha>\<index>")
  parent_of :: "'uf \<Rightarrow> 'a" ("parent'_of\<index>")
  explain :: "'uf \<Rightarrow> 'a" ("explain\<index>")


definition
  "union_find_adt_of_union_find_explain_adt (u :: ('uf, 'a) union_find_explain_adt) \<equiv>
  Union_Find_ADT (init\<^bsub>u\<^esub>) (rep_of\<^bsub>u\<^esub>) (union\<^bsub>u\<^esub>) (invar\<^bsub>u\<^esub>) (\<alpha>\<^bsub>u\<^esub>)"

declare [[coercion union_find_adt_of_union_find_explain_adt]]

adhoc_overloading init union_find_adt.init union_find_parent_adt.init
adhoc_overloading rep_of union_find_adt.rep_of union_find_parent_adt.rep_of
adhoc_overloading union union_find_adt.union union_find_parent_adt.union
adhoc_overloading invar union_find_adt.invar union_find_parent_adt.invar
adhoc_overloading \<alpha> union_find_adt.\<alpha> union_find_parent_adt.\<alpha>
adhoc_overloading parent_of union_find_parent_adt.parent_of
adhoc_overloading explain union_find_explain_adt.explain


locale union_find =
  fixes uf_adt :: "('uf, 'a) union_find_adt"  (structure)
  assumes invar_init: "invar init"
      and \<alpha>_init: "\<alpha> init \<subseteq> Id" 
      and \<alpha>_rep_of:
        "\<lbrakk> invar uf; x \<in> Field (\<alpha> uf); y \<in> Field (\<alpha> uf) \<rbrakk>
        \<Longrightarrow> rep_of uf x = rep_of uf y \<longleftrightarrow> (x, y) \<in> \<alpha> uf"
      and invar_union:
        "\<lbrakk> invar uf; x \<in> Field (\<alpha> uf); y \<in> Field (\<alpha> uf) \<rbrakk>
        \<Longrightarrow> invar (union uf x y)"
      and \<alpha>_union:
        "\<lbrakk> invar uf; x \<in> Field (\<alpha> uf); y \<in> Field (\<alpha> uf) \<rbrakk>
        \<Longrightarrow> \<alpha> (union uf x y) = per_union (\<alpha> uf) x y"

(*
lemma union_find_ufa:
  "union_find [0..<n] rep_of ufa_union ufa_invar ufa_\<alpha>"
proof -
  note [simp] = ufa_init_invar ufa_init_correct
    ufa_find_correct ufa_union_invar ufa_union_correct
  show ?thesis
    by unfold_locales (auto simp: Field_iff ufa_\<alpha>_lenD)
qed *)

locale union_find_explain =
  fixes ufe_adt :: "('uf, 'a) union_find_explain_adt" (structure)

  assumes \<alpha>_explain:
    "\<lbrakk> invar\<^bsub>ufe_adt\<^esub> uf; x \<in> Field (\<alpha> uf); y \<in> Field (\<alpha> uf); (x, y) \<in> \<alpha> uf \<rbrakk>
    \<Longrightarrow> (x, y) \<in> (explain uf x y)\<^sup>*"

end