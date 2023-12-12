theory UF_ADT
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
    "HOL-Statespace.StateSpaceSyntax"
begin

statespace ('uf, 'a) union_find_adt =
  init :: 'uf
  rep_of :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a"
  union :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'uf"
  invar :: "'uf \<Rightarrow> bool"
  \<alpha> :: "'uf \<Rightarrow> 'a rel"

statespace ('uf, 'a) union_find_parent_adt =
  ('uf, 'a) union_find_adt +
  parent_of :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a"
  
statespace ('uf, 'a) union_find_explain_adt =
  ('uf, 'a) union_find_adt +
  explain :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a rel"

context union_find_adt
begin

abbreviation uf_init_1 ("uf'_init\<index>") where "uf_init_1 uf_adt \<equiv> uf_adt \<cdot> init" 
abbreviation uf_rep_of_1 ("uf'_rep'_of\<index>") where "uf_rep_of_1 uf_adt \<equiv> uf_adt \<cdot> rep_of" 
abbreviation uf_union_1 ("uf'_union\<index>") where "uf_union_1 uf_adt \<equiv> uf_adt \<cdot> union" 
abbreviation uf_invar_1 ("uf'_invar\<index>") where "uf_invar_1 uf_adt \<equiv> uf_adt \<cdot> invar" 
abbreviation uf_\<alpha>_1 ("uf'_\<alpha>\<index>") where "uf_\<alpha>_1 uf_adt \<equiv> uf_adt \<cdot> \<alpha>"

end

abbreviation (in union_find_parent_adt) uf_parent_of_1 ("uf'_parent'_of\<index>") where
  "uf_parent_of_1 uf_adt \<equiv> uf_adt \<cdot> parent_of"

abbreviation (in union_find_explain_adt) uf_explain_1 ("uf'_explain\<index>") where
  "uf_explain_1 uf_adt \<equiv> uf_adt \<cdot> explain"

locale union_find = union_find_adt +
  fixes uf_adt (structure)
  assumes part_equiv_\<alpha>[simp, intro]:
        "uf_invar uf \<Longrightarrow> part_equiv (uf_\<alpha> uf)"
      and invar_init[simp, intro]: "uf_invar uf_init"
      and \<alpha>_init: "uf_\<alpha> uf_init \<subseteq> Id" 
      and \<alpha>_rep_of[simp]:
        "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
        \<Longrightarrow> uf_rep_of uf x = uf_rep_of uf y \<longleftrightarrow> (x, y) \<in> uf_\<alpha> uf"
      and invar_union[simp, intro]:
        "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
        \<Longrightarrow> uf_invar (uf_union uf x y)"
      and \<alpha>_union[simp]:
        "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
        \<Longrightarrow> uf_\<alpha> (uf_union uf x y) = per_union (uf_\<alpha> uf) x y"

locale union_find_parent = union_find_parent_adt + union_find +
  assumes wf_parent_of:
    "uf_invar uf \<Longrightarrow> wf {(uf_parent_of uf x, x) |x. x \<in> Field (uf_\<alpha> uf)}"
  assumes parent_of_in_\<alpha>:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk> \<Longrightarrow> (uf_parent_of uf x, x) \<in> uf_\<alpha> uf"
  assumes parent_of_refl_iff_rep_of_refl[simp]:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_parent_of uf x = x \<longleftrightarrow> uf_rep_of uf x = x"
  assumes rep_of_parent_of[simp]:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_rep_of uf (uf_parent_of uf x) = uf_rep_of uf x"
begin

lemma uf_parent_in_Field_\<alpha>I[simp, intro]:
  "uf_invar uf \<Longrightarrow> x \<in> Field (uf_\<alpha> uf) \<Longrightarrow> uf_parent_of uf x \<in> Field (uf_\<alpha> uf)"
  using parent_of_in_\<alpha> by (meson FieldI1)

lemma parent_of_in_\<alpha>_sym:
  "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk> \<Longrightarrow> (x, uf_parent_of uf x) \<in> uf_\<alpha> uf"
  using part_equiv_\<alpha> parent_of_in_\<alpha> part_equiv_sym by fast

end

locale union_find_explain = union_find_explain_adt + union_find +
  assumes \<alpha>_explain:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf); (x, y) \<in> uf_\<alpha> uf \<rbrakk>
    \<Longrightarrow> (x, y) \<in> (uf_explain uf x y)\<^sup>*"

end