theory Map_ADT
  imports "HOL-Statespace.StateSpaceSyntax"
begin

record ('m, 'dom, 'ran) map_mono_adt =
  empty :: 'm ("mm'_empty\<index>")
  update :: "'m \<Rightarrow> 'dom \<Rightarrow> 'ran \<Rightarrow> 'm" ("mm'_update\<index>")
  lookup :: "'m \<Rightarrow> 'dom \<Rightarrow> 'ran option" ("mm'_lookup\<index>")
  invar :: "'m \<Rightarrow> bool" ("mm'_invar\<index>")
  \<alpha> :: "'m \<Rightarrow> ('dom \<rightharpoonup> 'ran)" ("mm'_\<alpha>\<index>")

locale map_mono_adt =
  fixes mm_adt (structure)

locale map_mono = map_mono_adt +
  assumes \<alpha>_empty:
    "mm_\<alpha> mm_empty = Map.empty"
  assumes \<alpha>_update:
    "mm_invar m \<Longrightarrow> mm_\<alpha> (mm_update m a b) = (mm_\<alpha> m)(a \<mapsto> b)"
  assumes \<alpha>_lookup:
    "mm_invar m \<Longrightarrow> mm_lookup m = mm_\<alpha> m"
  assumes invar_empty[simp]:
    "mm_invar mm_empty"
  assumes invar_update[simp]:
    "mm_invar m \<Longrightarrow> mm_invar (mm_update m a b)"
begin

definition "mm_rel ma m \<equiv> BNF_Def.Grp {m. mm_invar m} mm_\<alpha> m ma"

lemmas mm_rel_defs = mm_rel_def BNF_Def.Grp_def

lemma mm_relI:
  assumes "mm_invar m"
  shows "mm_rel (mm_\<alpha> m) m"
  using assms unfolding mm_rel_defs
  by simp

context includes lifting_syntax
begin

lemma mm_empty_transfer[transfer_rule]:
  "mm_rel Map.empty mm_empty"
  using \<alpha>_empty unfolding mm_rel_defs
  by simp

lemma mm_update_transfer[transfer_rule]:
  "(mm_rel ===> (=) ===> (=) ===> mm_rel) (\<lambda>m a b. m(a \<mapsto> b)) mm_update"
  using \<alpha>_update unfolding mm_rel_defs rel_fun_def
  by auto

lemma mm_lookup_transfer[transfer_rule]:
  "(mm_rel ===> (=) ===> (=)) id mm_lookup"
  using \<alpha>_lookup unfolding mm_rel_defs rel_fun_def
  by auto

definition "eq_mm_\<alpha> x y \<equiv> mm_\<alpha> x = mm_\<alpha> y"

lemma eq_mm_\<alpha>_transfer[transfer_rule]:
  shows "(mm_rel ===> mm_rel ===> (=)) (=) eq_mm_\<alpha>"
  unfolding eq_mm_\<alpha>_def mm_rel_def BNF_Def.Grp_def by auto
  
end

lemma
  includes lifting_syntax
  assumes "mm_invar m"
  assumes "a \<noteq> c"
  shows "mm_\<alpha> (mm_update (mm_update m a b) c d)
    = mm_\<alpha> (mm_update (mm_update m c d) a b)"
proof -
  have [transfer_rule]: "mm_rel (mm_\<alpha> m) m"
    using assms mm_relI by blast
  show ?thesis
    using \<open>a \<noteq> c\<close>

    unfolding eq_mm_\<alpha>_def[symmetric]
    apply transfer
    by auto
qed


end

locale map_mono_invar = map_mono +
  fixes m
  assumes invar_m: "mm_invar m"
begin

lemmas
  \<alpha>_update = \<alpha>_update[OF invar_m] and
  \<alpha>_lookup = \<alpha>_lookup[OF invar_m] and
  invar_update = invar_update[OF invar_m]

end

end