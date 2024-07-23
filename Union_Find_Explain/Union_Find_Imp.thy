theory Union_Find_Imp
  imports Union_Find "Separation_Logic_Imperative_HOL.Sep_Main"
begin

lemma pcr_ufa_transfer:
  includes lifting_syntax
  shows "(list_all2 (=) ===> pcr_ufa ===> (=)) (=) pcr_ufa"
  by (intro rel_funI) (metis left_uniqueD list_all2_eq ufa.left_unique)

type_synonym ufa_imp = "nat array"

definition is_ufa :: "ufa \<Rightarrow> ufa_imp \<Rightarrow> assn" where
  "is_ufa ufa p \<equiv> \<exists>\<^sub>Auf. p \<mapsto>\<^sub>a uf * \<up>(pcr_ufa uf ufa)"

definition ufa_imp_init :: "nat \<Rightarrow> ufa_imp Heap" where
  "ufa_imp_init n \<equiv> Array.of_list [0..<n]"

lemma ufa_imp_init_rule[sep_heap_rules]:
  "<emp> ufa_imp_init n <is_ufa (ufa_init n)>"
proof -
  note [transfer_rule] = pcr_ufa_transfer
  have "pcr_ufa uf (ufa_init n)" if "uf = [0..<n]" for uf
    using that including ufa.lifting by transfer
  then show ?thesis
   unfolding ufa_imp_init_def is_ufa_def
   by sep_auto 
qed

definition "ufa_imp_parent_of p i \<equiv> Array.nth p i"

lemma ufa_parent_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufa_\<alpha> ufa)"
  shows "<is_ufa ufa p> ufa_imp_parent_of p i <\<lambda>r. is_ufa ufa p * \<up>(r = ufa_parent_of ufa i)>"
proof -
  note [transfer_rule] = pcr_ufa_transfer
  have "ufa_parent_of ufa i = uf ! i" "i < length uf"
    if "pcr_ufa uf ufa" "i \<in> Field (ufa_\<alpha> ufa)" for uf
    using that including ufa.lifting
    by (transfer, simp)+
  then show ?thesis
    using assms unfolding ufa_imp_parent_of_def is_ufa_def by sep_auto
qed

partial_function (heap) ufa_imp_rep_of :: "ufa_imp \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "ufa_imp_rep_of p i = do {
    pi \<leftarrow> ufa_imp_parent_of p i;
    if pi = i then return i else ufa_imp_rep_of p pi
  }"

lemma ufa_imp_rep_of_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufa_\<alpha> ufa)"
  shows "<is_ufa ufa p> ufa_imp_rep_of p i <\<lambda>r. is_ufa ufa p * \<up>(r = ufa_rep_of ufa i)>"
  using assms
proof(induction rule: ufa_rep_of_induct)
  case (rep i)
  then have "ufa_rep_of ufa i = i"
    using ufa_rep_of_if_refl_ufa_parent_of by (transfer, transfer)
  with rep show ?case
    by (subst ufa_imp_rep_of.simps) sep_auto
next
  case (not_rep i)
  from not_rep.hyps have "ufa_rep_of ufa (ufa_parent_of ufa i) = ufa_rep_of ufa i"
    using ufa_rep_of_ufa_parent_of by (transfer, transfer)
  with not_rep show ?case
    by (subst ufa_imp_rep_of.simps) sep_auto
qed

definition ufa_imp_union :: "ufa_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufa_imp Heap" where
  "ufa_imp_union p x y \<equiv> do {
    rep_x \<leftarrow> ufa_imp_rep_of p x;
    rep_y \<leftarrow> ufa_imp_rep_of p y;
    Array.upd rep_x rep_y p
  }"

lemma ufa_imp_union_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> ufa)" "y \<in> Field (ufa_\<alpha> ufa)"
  shows "<is_ufa ufa p> ufa_imp_union p x y <is_ufa (ufa_union ufa x y)>"
proof -
  note [transfer_rule] = pcr_ufa_transfer
  have
    "ufa_rep_of ufa x < length uf"
    "pcr_ufa (uf[ufa_rep_of ufa x := ufa_rep_of ufa y]) (ufa_union ufa x y)"
    if "pcr_ufa uf ufa" "x \<in> Field (ufa_\<alpha> ufa)" "y \<in> Field (ufa_\<alpha> ufa)" for uf
    using that including ufa.lifting by (transfer, simp)+
  then have "<is_ufa ufa p> Array.upd (ufa_rep_of ufa x) (ufa_rep_of ufa y) p
    <is_ufa (ufa_union ufa x y)>"
    using assms ufa_invar_list_update_rep_of_rep_of unfolding is_ufa_def
    by sep_auto
  with assms show ?thesis
    unfolding ufa_imp_union_def by sep_auto
qed

end