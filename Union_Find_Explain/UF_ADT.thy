theory UF_ADT
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
    "HOL-Statespace.StateSpaceSyntax"
begin

lemma Field_per_union[simp]: "Field (per_union R a b) = Field R"
  unfolding per_union_def Field_def
  by auto

lemma finite_eq_class_per_union_if_finite_eq_class:
  assumes "part_equiv R"
  assumes "\<And>a. finite (R `` {a})"
  shows "finite (per_union R b c `` {a})"
proof -
  from \<open>part_equiv R\<close>[THEN part_equiv_sym] have "{d. (d, c) \<in> R} = (R `` {c})" for c
    unfolding Image_singleton by blast
  with assms have "finite {d. (d, c) \<in> R}" for c
    by simp
  then have "finite {d. (a, b) \<in> R \<and> (d, c) \<in> R}" "finite {d. (d, b) \<in> R \<and> (a, c) \<in> R}"
    using finite_subset by simp_all
  with assms show ?thesis
    unfolding per_union_def
    by (auto simp: Image_singleton)
qed

lemma in_per_union_if_in_rel[simp]:
  "(x, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b"
  unfolding per_union_def by auto

lemma per_union_eq_if_not_in_Field:
  assumes "x \<notin> Field R"
  shows "per_union R x y = R" "per_union R y x = R"
  using assms unfolding Field_def per_union_def
  by auto

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
  assumes part_equiv_\<alpha>:
        "uf_invar uf \<Longrightarrow> part_equiv (uf_\<alpha> uf)"
      and invar_init: "uf_invar uf_init"
      and \<alpha>_init: "uf_\<alpha> uf_init \<subseteq> Id" 
      and \<alpha>_rep_of:
        "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
        \<Longrightarrow> uf_rep_of uf x = uf_rep_of uf y \<longleftrightarrow> (x, y) \<in> uf_\<alpha> uf"
      and invar_union:
        "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
        \<Longrightarrow> uf_invar (uf_union uf x y)"
      and \<alpha>_union:
        "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
        \<Longrightarrow> uf_\<alpha> (uf_union uf x y) = per_union (uf_\<alpha> uf) x y"

locale union_find_parent = union_find_parent_adt + union_find +
  assumes wf_parent_of:
    "uf_invar uf \<Longrightarrow> wf {(uf_parent_of uf x, x) |x. x \<in> Field (uf_\<alpha> uf)}"
  assumes parent_of_in_\<alpha>:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk> \<Longrightarrow> (uf_parent_of uf x, x) \<in> uf_\<alpha> uf"
  assumes parent_of_refl_iff_rep_of_refl:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_parent_of uf x = x \<longleftrightarrow> uf_rep_of uf x = x"
  assumes rep_of_parent_of:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_rep_of uf (uf_parent_of uf x) = uf_rep_of uf x"

locale union_find_explain = union_find_explain_adt + union_find +
  assumes \<alpha>_explain:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf); (x, y) \<in> uf_\<alpha> uf \<rbrakk>
    \<Longrightarrow> (x, y) \<in> (uf_explain uf x y)\<^sup>*"


locale union_find_invar = union_find +
  fixes uf
  assumes invar_uf: "uf_invar uf"
begin

lemmas
  part_equiv_\<alpha>[simp, intro] = part_equiv_\<alpha>[OF invar_uf] and
  \<alpha>_rep_of = \<alpha>_rep_of[OF invar_uf] and
  invar_union[simp, intro] = invar_union[OF invar_uf] and
  \<alpha>_union[simp] = \<alpha>_union[OF invar_uf]

lemma Field_\<alpha>_union[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "Field (uf_\<alpha> (uf_union uf x y)) = Field (uf_\<alpha> uf)"
  using assms by auto

end

locale union_find_parent_invar = union_find_parent +
  fixes uf
  assumes invar_uf: "uf_invar uf"
begin

sublocale union_find_invar where uf = uf
  using invar_uf by unfold_locales

lemmas
  wf_parent_of = wf_parent_of[OF invar_uf] and
  parent_of_in_\<alpha>[intro] = parent_of_in_\<alpha>[OF invar_uf] and
  parent_of_refl_iff_rep_of_refl = parent_of_refl_iff_rep_of_refl[OF invar_uf] and
  rep_of_parent_of[simp] = rep_of_parent_of[OF invar_uf]

lemma parent_of_in_Field_\<alpha>I[intro]:
  "x \<in> Field (uf_\<alpha> uf) \<Longrightarrow> uf_parent_of uf x \<in> Field (uf_\<alpha> uf)"
  using parent_of_in_\<alpha> by (meson FieldI1)

lemma parent_of_in_\<alpha>_sym:
  "\<lbrakk> x \<in> Field (uf_\<alpha> uf) \<rbrakk> \<Longrightarrow> (x, uf_parent_of uf x) \<in> uf_\<alpha> uf"
  using part_equiv_\<alpha> parent_of_in_\<alpha> part_equiv_sym by metis

end

end