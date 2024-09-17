theory Union_Find_Size_Int_Imp
  imports Union_Find_Size_Int_Quotient "Separation_Logic_Imperative_HOL.Sep_Main"
begin

type_synonym ufsi_imp = "int array"

definition is_ufsi :: "ufsi \<Rightarrow> ufsi_imp \<Rightarrow> assn" where
  "is_ufsi ufsi ufsi_imp \<equiv> \<exists>\<^sub>Aufsi_list. ufsi_imp \<mapsto>\<^sub>a ufsi_list * 
    \<up>(ufsi_invar ufsi_list \<and> ufsi = Abs_ufsi ufsi_list)"

lemma is_ufsi_def':
  "is_ufsi ufsi ufsi_imp = (\<exists>\<^sub>Aufsi_list. ufsi_imp \<mapsto>\<^sub>a ufsi_list * 
    \<up>(Rep_ufsi ufsi = ufsi_list))"
proof -
  have "Rep_ufsi ufsi = ufsi_list \<longleftrightarrow>
    ufsi_invar ufsi_list \<and> Abs_ufsi ufsi_list = ufsi" for ufsi_list
    using Abs_ufsi_inverse Rep_ufsi_inverse Rep_ufsi[simplified] by force
  then show ?thesis
    unfolding is_ufsi_def
    by (intro ent_iffI; sep_auto)
qed

lemma snga_entails_is_ufsi_Abs_ufsi:
  assumes "ufsi_invar ufsi_list"
  shows "ufsi_imp \<mapsto>\<^sub>a ufsi_list \<Longrightarrow>\<^sub>A is_ufsi (Abs_ufsi ufsi_list) ufsi_imp"
  using assms unfolding is_ufsi_def
  by (intro entailsI) auto

lemma is_ufsi_Abs_ufsi_entails_snga:
  assumes "ufsi_invar ufsi_list"
  shows "is_ufsi (Abs_ufsi ufsi_list) ufsi_imp \<Longrightarrow>\<^sub>A ufsi_imp \<mapsto>\<^sub>a ufsi_list"
  using assms unfolding is_ufsi_def
  by (intro entailsI) (use Abs_ufsi_inject in auto)

definition ufsi_imp_init :: "nat \<Rightarrow> ufsi_imp Heap" where
  "ufsi_imp_init n \<equiv> Array.new n (-1)"

lemma ufsi_imp_init_rule[sep_heap_rules]:
  "<emp> ufsi_imp_init n <is_ufsi (ufsi_init n)>"
  unfolding ufsi_imp_init_def is_ufsi_def[abs_def]
  using ufsi_invar_replicate_neg_1  
  by (sep_auto simp: Abs_ufsi_replicate_neg_1_eq_ufsi_init)
  
definition "ufsi_imp_parent_of ufsi_imp i \<equiv>
  do {
    n \<leftarrow> Array.nth ufsi_imp i;
    return (if n < 0 then i else nat n)
  }"

lemma ufsi_parent_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_parent_of ufsi_imp i
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufsi_parent_of ufsi i)>"
  using assms lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi
  unfolding ufsi_imp_parent_of_def is_ufsi_def
  by (sep_auto simp: ufsi_parent_of_Abs_ufsi_eq)
  
partial_function (heap) ufsi_imp_rep_of :: "ufsi_imp \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "ufsi_imp_rep_of ufsi_imp i = do {
    pi \<leftarrow> ufsi_imp_parent_of ufsi_imp i;
    if pi = i then return i else ufsi_imp_rep_of ufsi_imp pi
  }"

lemma ufsi_imp_rep_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_rep_of ufsi_imp i
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufsi_rep_of ufsi i)>"
  using assms
proof(induction rule: ufsi_rep_of_induct)
  case "parametric"
  then show ?case
    unfolding ufa_ufs_rel_def
    by (intro rel_funI) simp
next
  case (rep i)
  then have "ufsi_rep_of ufsi i = i"
    including ufa_ufs_transfer ufsi.lifting
    using ufa_rep_of_if_refl_ufa_parent_of by (transfer, transfer)
  with rep show ?case
    by (subst ufsi_imp_rep_of.simps) sep_auto
next
  case (not_rep i)
  from not_rep.hyps have "ufsi_rep_of ufsi (ufsi_parent_of ufsi i) = ufsi_rep_of ufsi i"
    including ufa_ufs_transfer ufsi.lifting
    using ufa_rep_of_ufa_parent_of by (transfer, transfer)
  with not_rep show ?case
    by (subst ufsi_imp_rep_of.simps) sep_auto
qed

definition "ufsi_imp_size ufsi_imp x \<equiv> do {
  sz \<leftarrow> Array.nth ufsi_imp x;
  if sz < 0 then return (nat (- sz)) else return 0
}"

lemma ufsi_imp_size_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufsi_\<alpha> ufsi)"
  assumes "ufsi_rep_of ufsi i = i"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_size ufsi_imp i
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufsi_size ufsi i)>"
  using assms lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi
  unfolding is_ufsi_def ufsi_imp_size_def
  by (sep_auto simp: Abs_ufsi_inverse size_of_ufsi_def ufsi_size_Abs_ufsi)

lemma ufsi_imp_size_rule'[sep_heap_rules]:
  assumes "ufsi_invar ufsi"
  assumes "i \<in> Field (ufsi_\<alpha> (Abs_ufsi ufsi))"
  assumes "ufsi_rep_of (Abs_ufsi ufsi) i = i"
  shows
    "<ufsi_imp \<mapsto>\<^sub>a ufsi>
      ufsi_imp_size ufsi_imp i
    <\<lambda>r. ufsi_imp \<mapsto>\<^sub>a ufsi * \<up>(r = ufsi_size (Abs_ufsi ufsi) i)>"
  using assms snga_entails_is_ufsi_Abs_ufsi is_ufsi_Abs_ufsi_entails_snga ufsi_imp_size_rule
  by (metis (no_types, lifting) cons_post_rule ent_iffI entailsI)

definition "ufsi_imp_union_raw ufsi_imp rep_x rep_y sz \<equiv> do {
  Array.upd rep_x (int rep_y) ufsi_imp;
  Array.upd rep_y (- int sz) ufsi_imp
}"

lemma ufsi_imp_union_raw_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
  defines "rep_x \<equiv> ufsi_rep_of ufsi x"
  defines "rep_y \<equiv> ufsi_rep_of ufsi y"
  defines "sz_rep_x \<equiv> ufsi_size ufsi rep_x"
  defines "sz_rep_y \<equiv> ufsi_size ufsi rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows 
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_union_raw ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufsi (ufsi_union ufsi x y)>"
  using assms lt_length_if_in_Field_ufsi_\<alpha>_Abs_ufsi ufsi_union_Abs_ufsi
  unfolding ufsi_imp_union_raw_def by (sep_auto simp: is_ufsi_def)

definition "ufsi_imp_union_size ufsi_imp x y \<equiv> do {
  rep_x \<leftarrow> ufsi_imp_rep_of ufsi_imp x;
  rep_y \<leftarrow> ufsi_imp_rep_of ufsi_imp y;
  if rep_x = rep_y then
    return ufsi_imp
  else do {
    sz_rep_x \<leftarrow> ufsi_imp_size ufsi_imp rep_x;
    sz_rep_y \<leftarrow> ufsi_imp_size ufsi_imp rep_y;
    if sz_rep_x < sz_rep_y then do {
      ufsi_imp_union_raw ufsi_imp rep_x rep_y (sz_rep_x + sz_rep_y)
    }
    else do {
      ufsi_imp_union_raw ufsi_imp rep_y rep_x (sz_rep_y + sz_rep_x)
    }
  }
}"

lemma ufsi_imp_union_size_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_union_size ufsi_imp x y
    <is_ufsi (ufsi_union_size ufsi x y)>"
proof -
  include ufa_ufs_transfer Union_Find_Size_Int_Quotient.ufsi.lifting
  have "ufsi_union_size ufsi x y = ufsi"
    if "ufsi_rep_of ufsi x = ufsi_rep_of ufsi y"
    using assms that
    by (transfer, transfer)
      (use ufa_union_eq_if_rep_eq ufa_union_size_def in simp)
  moreover have "ufsi_union_size ufsi x y = ufsi_union ufsi x y"
    if "ufsi_rep_of ufsi x \<noteq> ufsi_rep_of ufsi y"
      "ufsi_size ufsi (ufsi_rep_of ufsi x) < ufsi_size ufsi (ufsi_rep_of ufsi y)"
    using assms that
    by transfer (simp add: ufs_union_size_def)
  moreover have "ufsi_union_size ufsi x y = ufsi_union ufsi y x"
    if "ufsi_rep_of ufsi x \<noteq> ufsi_rep_of ufsi y"
      "\<not> ufsi_size ufsi (ufsi_rep_of ufsi x) < ufsi_size ufsi (ufsi_rep_of ufsi y)" 
    using assms that
    by transfer (simp add: ufs_union_size_def)
  ultimately show ?thesis
    using assms unfolding ufsi_imp_union_size_def
    by sep_auto
qed

end