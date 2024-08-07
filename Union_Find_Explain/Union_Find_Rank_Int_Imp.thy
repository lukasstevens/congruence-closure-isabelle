theory Union_Find_Rank_Int_Imp
  imports Union_Find_Rank_Int_Quotient "Separation_Logic_Imperative_HOL.Sep_Main"
begin

type_synonym ufri_imp = "int array"

definition is_ufri :: "ufri \<Rightarrow> ufri_imp \<Rightarrow> assn" where
  "is_ufri ufri p \<equiv> \<exists>\<^sub>Aufri_imp. p \<mapsto>\<^sub>a ufri_imp *
    \<up>(ufri_invar ufri_imp \<and> Abs_ufri ufri_imp = ufri)"

lemma snga_entails_is_ufri_Abs_ufri:
  assumes "ufri_invar ufri_imp"
  shows "p \<mapsto>\<^sub>a ufri_imp \<Longrightarrow>\<^sub>A is_ufri (Abs_ufri ufri_imp) p"
  using assms unfolding is_ufri_def
  by (intro entailsI) auto

lemma is_ufri_Abs_ufri_entails_snga:
  assumes "ufri_invar ufri_imp"
  shows "is_ufri (Abs_ufri ufri_imp) p \<Longrightarrow>\<^sub>A p \<mapsto>\<^sub>a ufri_imp"
  using assms unfolding is_ufri_def
  by (intro entailsI) (use Abs_ufri_inject in auto)

definition ufri_imp_init :: "nat \<Rightarrow> ufri_imp Heap" where
  "ufri_imp_init n \<equiv> Array.new n (-1)"

lemma ufri_imp_init_rule[sep_heap_rules]:
  "<emp> ufri_imp_init n <is_ufri (ufri_init n)>"
  unfolding ufri_imp_init_def is_ufri_def[abs_def]
  using ufri_invar_replicate_neg_1  
  by (sep_auto simp: Abs_ufri_replicate_neg_1_eq_ufri_init)
  
definition "ufri_imp_parent_of p i \<equiv>
  do {
    n \<leftarrow> Array.nth p i;
    return (if n < 0 then i else nat n)
  }"

lemma ufri_parent_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufri_\<alpha> ufri)"
  shows "<is_ufri ufri p> ufri_imp_parent_of p i <\<lambda>r. is_ufri ufri p * \<up>(r = ufri_parent_of ufri i)>"
  using assms lt_length_if_in_Field_ufri_\<alpha>_Abs_ufri
  unfolding ufri_imp_parent_of_def is_ufri_def
  by (sep_auto simp: ufri_parent_of_Abs_ufri_eq)
  
partial_function (heap) ufri_imp_rep_of :: "ufri_imp \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "ufri_imp_rep_of p i = do {
    pi \<leftarrow> ufri_imp_parent_of p i;
    if pi = i then return i else ufri_imp_rep_of p pi
  }"

lemma ufri_imp_rep_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufri_\<alpha> ufri)"
  shows "<is_ufri ufri p> ufri_imp_rep_of p i <\<lambda>r. is_ufri ufri p * \<up>(r = ufri_rep_of ufri i)>"
  using assms
proof(induction rule: ufri_rep_of_induct)
  case "parametric"
  then show ?case
    unfolding ufa_ufr_rel_def
    by (intro rel_funI) simp
next
  case (rep i)
  then have "ufri_rep_of ufri i = i"
    including ufa_ufr_transfer ufri.lifting
    using ufa_rep_of_if_refl_ufa_parent_of by (transfer, transfer)
  with rep show ?case
    by (subst ufri_imp_rep_of.simps) sep_auto
next
  case (not_rep i)
  from not_rep.hyps have "ufri_rep_of ufri (ufri_parent_of ufri i) = ufri_rep_of ufri i"
    including ufa_ufr_transfer ufri.lifting
    using ufa_rep_of_ufa_parent_of by (transfer, transfer)
  with not_rep show ?case
    by (subst ufri_imp_rep_of.simps) sep_auto
qed

lemma ufri_imp_rep_of_rule':
  assumes "ufri_invar ufri"
  assumes "i \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  shows "<p \<mapsto>\<^sub>a ufri> ufri_imp_rep_of p i
    <\<lambda>r. p \<mapsto>\<^sub>a ufri * \<up>(r = ufri_rep_of (Abs_ufri ufri) i)>"
  using assms ufri_imp_rep_of_rule
  by (metis ent_iffI is_ufri_Abs_ufri_entails_snga snga_entails_is_ufri_Abs_ufri)

definition "ufri_imp_rank p x \<equiv> do {
  r \<leftarrow> Array.nth p x;
  if r < 0 then return (nat (- r)) else return 0
}"

lemma ufri_imp_rank_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufri_\<alpha> ufri)"
  assumes "ufri_rep_of ufri i = i"
  shows "<is_ufri ufri p> ufri_imp_rank p i <\<lambda>r. is_ufri ufri p * \<up>(r = ufri_rank ufri i)>"
  using assms lt_length_if_in_Field_ufri_\<alpha>_Abs_ufri
  unfolding is_ufri_def ufri_imp_rank_def
  by (sep_auto simp: Abs_ufri_inverse rank_of_ufri_def ufri_rank_Abs_ufri)

lemma ufri_imp_rank_rule'[sep_heap_rules]:
  assumes "ufri_invar ufri"
  assumes "i \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  assumes "ufri_rep_of (Abs_ufri ufri) i = i"
  shows "<p \<mapsto>\<^sub>a ufri> ufri_imp_rank p i
    <\<lambda>r. p \<mapsto>\<^sub>a ufri * \<up>(r = ufri_rank (Abs_ufri ufri) i)>"
  using assms snga_entails_is_ufri_Abs_ufri is_ufri_Abs_ufri_entails_snga ufri_imp_rank_rule
  by (metis (no_types, lifting) cons_post_rule ent_iffI entailsI)

definition "ufri_imp_union_raw p rep_x rep_y rank \<equiv> do {
  Array.upd rep_x (int rep_y) p;
  Array.upd rep_y (- int rank) p
}"

lemma ufri_imp_union_raw_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufri_\<alpha> ufri)" "y \<in> Field (ufri_\<alpha> ufri)"
  defines "rep_x \<equiv> ufri_rep_of ufri x"
  defines "rep_y \<equiv> ufri_rep_of ufri y"
  defines "rank_rep_x \<equiv> ufri_rank ufri rep_x"
  defines "rank_rep_y \<equiv> ufri_rank ufri rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows 
    "<is_ufri ufri p>
      ufri_imp_union_raw p rep_x rep_y (rank_rep_x + rank_rep_y)
    <is_ufri (ufri_union ufri x y)>"
  using assms lt_length_if_in_Field_ufri_\<alpha>_Abs_ufri ufri_union_Abs_ufri
  unfolding ufri_imp_union_raw_def by (sep_auto simp: is_ufri_def)

definition "ufri_imp_union_rank p x y \<equiv> do {
  rep_x \<leftarrow> ufri_imp_rep_of p x;
  rep_y \<leftarrow> ufri_imp_rep_of p y;
  if rep_x = rep_y then
    return p
  else do {
    rank_rep_x \<leftarrow> ufri_imp_rank p rep_x;
    rank_rep_y \<leftarrow> ufri_imp_rank p rep_y;
    if rank_rep_x < rank_rep_y then do {
      ufri_imp_union_raw p rep_x rep_y (rank_rep_x + rank_rep_y)
    }
    else do {
      ufri_imp_union_raw p rep_y rep_x (rank_rep_y + rank_rep_x)
    }
  }
}"

lemma ufri_imp_union_rank_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufri_\<alpha> ufri)" "y \<in> Field (ufri_\<alpha> ufri)"
  shows "<is_ufri ufri p> ufri_imp_union_rank p x y
    <is_ufri (ufri_union_rank ufri x y)>"
proof -
  include ufa_ufr_transfer Union_Find_Rank_Int_Quotient.ufri.lifting
  have "ufri_union_rank ufri x y = ufri"
    if "ufri_rep_of ufri x = ufri_rep_of ufri y"
    using assms that
    by (transfer, transfer)
      (use ufa_union_eq_if_rep_eq ufa_union_rank_def in simp)
  moreover have "ufri_union_rank ufri x y = ufri_union ufri x y"
    if "ufri_rep_of ufri x \<noteq> ufri_rep_of ufri y"
      "ufri_rank ufri (ufri_rep_of ufri x) < ufri_rank ufri (ufri_rep_of ufri y)"
    using assms that
    by transfer (simp add: ufr_union_rank_def)
  moreover have "ufri_union_rank ufri x y = ufri_union ufri y x"
    if "ufri_rep_of ufri x \<noteq> ufri_rep_of ufri y"
      "\<not> ufri_rank ufri (ufri_rep_of ufri x) < ufri_rank ufri (ufri_rep_of ufri y)" 
    using assms that
    by transfer (simp add: ufr_union_rank_def)
  ultimately show ?thesis
    using assms unfolding ufri_imp_union_rank_def
    by sep_auto
qed

end