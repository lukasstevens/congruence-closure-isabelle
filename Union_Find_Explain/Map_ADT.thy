theory Map_ADT
  imports "HOL-Statespace.StateSpaceSyntax"
begin

statespace ('m, 'dom, 'ran) map_mono_adt =
  empty :: 'm
  update :: "'m \<Rightarrow> 'dom \<Rightarrow> 'ran \<Rightarrow> 'm"
  lookup :: "'m \<Rightarrow> 'dom \<Rightarrow> 'ran option"
  invar :: "'m \<Rightarrow> bool"
  \<alpha> :: "'m \<Rightarrow> ('dom \<rightharpoonup> 'ran)"

context map_mono_adt
begin

abbreviation mm_empty_1 ("mm'_empty\<index>") where "mm_empty_1 mm_adt \<equiv> mm_adt \<cdot> empty"
abbreviation mm_update_1 ("mm'_update\<index>") where "mm_update_1 mm_adt \<equiv> mm_adt \<cdot> update"
abbreviation mm_lookup_1 ("mm'_lookup\<index>") where "mm_lookup_1 mm_adt \<equiv> mm_adt \<cdot> lookup"
abbreviation mm_invar_1 ("mm'_invar\<index>") where "mm_invar_1 mm_adt \<equiv> mm_adt \<cdot> invar"
abbreviation mm_\<alpha>_1 ("mm'_\<alpha>\<index>") where "mm_\<alpha>_1 mm_adt \<equiv> mm_adt \<cdot> \<alpha>"

end

locale map_mono_adt' = map_mono_adt where
  project_'ran_Option_option_'dom_fun_'m_fun =
  project_'ran_Option_option_'dom_fun_'m_fun
  for project_'ran_Option_option_'dom_fun_'m_fun :: "_ \<Rightarrow> 'm \<Rightarrow> 'dom \<Rightarrow> 'ran option" +

fixes m_ty :: "'m itself"
fixes dom_ty :: "'dom itself"
fixes ran_ty :: "'ran itself"


locale map_mono = map_mono_adt' +
  fixes mm_adt (structure)
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

end

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