theory Union_Find_Rank_Imp
  imports Union_Find_Rank Union_Find_Imp
begin

type_synonym ufr_imp = "(nat array \<times> nat array)"

definition is_ufr' :: "ufr \<Rightarrow> nat array \<Rightarrow> assn" where
  "is_ufr' ufr prs \<equiv> \<exists>\<^sub>Ars. prs \<mapsto>\<^sub>a rs *
    \<up>((\<forall>i \<in> Field (ufr_\<alpha> ufr). i < length rs) \<and>
    ufr_invar (ufa_of_ufr ufr, (!) rs) \<and>
    eq_ufr (Abs_ufr (ufa_of_ufr ufr, (!) rs)) ufr)"

definition is_ufr :: "ufr \<Rightarrow> ufr_imp \<Rightarrow> assn" where
  "is_ufr ufr p \<equiv>
    is_ufa (ufa_of_ufr ufr) (fst p) *
    is_ufr' ufr (snd p)"

lemma is_ufr_entails_is_ufr_if_eq_ufr:
  assumes "eq_ufr ufr2 ufr1"
  shows "is_ufr ufr1 p \<Longrightarrow>\<^sub>A is_ufr ufr2 p"
  using assms unfolding is_ufr_def is_ufa_def is_ufr'_def eq_ufr_def
  by (sep_auto simp: ufr_\<alpha>_def ufr_rank_def)

definition ufr_imp_init :: "nat \<Rightarrow> ufr_imp Heap" where
  "ufr_imp_init n \<equiv> do {
    puf \<leftarrow> ufa_imp_init n;
    prs \<leftarrow> Array.new n (1::nat);
    return (puf, prs)
  }"

lemma ufa_of_ufr_ufr_init_eq_ufa_init[simp]:
  "ufa_of_ufr (ufr_init n) = ufa_init n"
  by (simp add: ufa_of_ufr.rep_eq ufr_init.rep_eq)

lemma ufr_imp_init_rule[sep_heap_rules]:
  "<emp> ufr_imp_init n <is_ufr (ufr_init n)>"
proof -
  let ?ufr_init' = "\<lambda>n. (ufa_init n, (!) (replicate n 1))"
  have "ufr_invar (?ufr_init' n)"
    by (auto simp: ufa_rank_ufa_init intro!: ufr_invarI)
  moreover from this have "eq_ufr (Abs_ufr (?ufr_init' n)) (ufr_init n)"
    unfolding eq_ufr_def ufr_rank_def
    including ufa_ufr_transfer supply ufa_of_ufr_transfer[transfer_rule]
    by transfer (auto simp: eq_onp_same_args ufa_of_ufr.abs_eq)
  ultimately show ?thesis
    unfolding ufr_imp_init_def is_ufr_def is_ufr'_def
    by (sep_auto simp: ufr_\<alpha>_def)
qed

definition "ufr_imp_parent_of p \<equiv> ufa_imp_parent_of (fst p)"

lemma ufr_imp_parent_of_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufr_\<alpha> ufr)"
  shows "<is_ufr ufr p> ufr_imp_parent_of p x <\<lambda>r. is_ufr ufr p * \<up>(r = ufr_parent_of ufr x)>"
  using assms unfolding ufr_imp_parent_of_def is_ufr_def
  by (cases p) (sep_auto simp: ufr_\<alpha>_def ufr_parent_of_def)

definition "ufr_imp_rep_of p \<equiv> ufa_imp_rep_of (fst p)"

lemma ufr_imp_rep_of_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufr_\<alpha> ufr)"
  shows "<is_ufr ufr p> ufr_imp_rep_of p x <\<lambda>r. is_ufr ufr p * \<up>(r = ufr_rep_of ufr x)>"
  using assms unfolding ufr_imp_rep_of_def is_ufr_def
  by (cases p) (sep_auto simp: ufr_\<alpha>_def ufr_rep_of_def)

definition "ufr_imp_rank p x \<equiv> Array.nth (snd p) x"

lemma ufr_imp_rank_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufr_\<alpha> ufr)"
  assumes "ufr_rep_of ufr x = x"
  shows "<is_ufr ufr p> ufr_imp_rank p x <\<lambda>r. is_ufr ufr p * \<up>(r = ufr_rank ufr x)>"
  using assms unfolding is_ufr_def is_ufr'_def ufr_imp_rank_def  ufr_invar_def
  by (sep_auto simp: ufr_\<alpha>_def ufr_rep_of_def ufr_rank_def split: prod.splits)

definition "ufr_imp_union_raw p rep_x rep_y rank \<equiv> do {
  puf' \<leftarrow> ufa_imp_union (fst p) rep_x rep_y;
  prs' \<leftarrow> Array.upd rep_y rank (snd p);
  return (puf', prs')
}"

lemma ufr_invar_ufr_union_raw:
  fixes rs :: "nat list"
  assumes "ufr_invar (ufa_of_ufr ufr, (!) rs)" "\<forall>i \<in> Field (ufr_\<alpha> ufr). i < length rs"
  assumes "x \<in> Field (ufr_\<alpha> ufr)" "y \<in> Field (ufr_\<alpha> ufr)"
  defines "rep_x \<equiv> ufr_rep_of ufr x" and "rep_y \<equiv> ufr_rep_of ufr y"
  defines "rank_rep_x \<equiv> ufr_rank ufr rep_x" and "rank_rep_y \<equiv> ufr_rank ufr rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "ufr_invar (ufa_union (ufa_of_ufr ufr) x y, (!) (rs[rep_y := rank_rep_x + rank_rep_y]))"
proof -
  include ufa_ufr_transfer
  note ufa_of_ufr_transfer[transfer_rule]
  from assms(1-4,9) show ?thesis
    unfolding ufa_of_ufr_ufr_union[symmetric]
    unfolding ufr_invar_def assms(5-8)
    by transfer
      (auto simp: nth_list_update ufa_rep_of_ufa_union ufa_rank_ufa_union_if_ufa_rep_of_neq)
qed

lemma Abs_ufr_ufr_union_raw_eq_ufr_ufr_union:
  fixes rs :: "nat list"
  assumes "eq_ufr (Abs_ufr (ufa_of_ufr ufr, (!) rs)) ufr"
  assumes "ufr_invar (ufa_of_ufr ufr, (!) rs)" "\<forall>i \<in> Field (ufr_\<alpha> ufr). i < length rs"
  assumes "x \<in> Field (ufr_\<alpha> ufr)" "y \<in> Field (ufr_\<alpha> ufr)"
  defines "rep_x \<equiv> ufr_rep_of ufr x" and "rep_y \<equiv> ufr_rep_of ufr y"
  defines "rank_rep_x \<equiv> ufr_rank ufr rep_x" and "rank_rep_y \<equiv> ufr_rank ufr rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "eq_ufr (Abs_ufr (ufa_union (ufa_of_ufr ufr) x y, (!) (rs[rep_y := rank_rep_x + rank_rep_y])))
      (ufr_union ufr x y)"
proof -  
  note ufr_invar_ufr_union_raw[OF assms(2-5) assms(10)[unfolded rep_x_def rep_y_def]]
  then show ?thesis
    unfolding assms(6-9) eq_ufr_def ufr_rank_def
    by (auto simp: ufa_of_ufr_ufr_union eq_onp_same_args ufa_of_ufr.abs_eq)
qed

lemma ufr_imp_union_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufr_\<alpha> ufr)" "y \<in> Field (ufr_\<alpha> ufr)"
  defines "rep_x \<equiv> ufr_rep_of ufr x"
  defines "rep_y \<equiv> ufr_rep_of ufr y"
  defines "rank_rep_x \<equiv> ufr_rank ufr rep_x"
  defines "rank_rep_y \<equiv> ufr_rank ufr rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows 
    "<is_ufr ufr p>
      ufr_imp_union_raw p rep_x rep_y (rank_rep_x + rank_rep_y)
    <is_ufr (ufr_union ufr x y)>"
proof -
  from assms(1,2) have rep_in_Field_ufr_\<alpha>:
    "rep_x \<in> Field (ufr_\<alpha> ufr)" "rep_y \<in> Field (ufr_\<alpha> ufr)"
    unfolding rep_x_def rep_y_def including ufa_ufr_transfer by (transfer, simp)+
  with assms have [sep_heap_rules]:
    "<is_ufr ufr p> ufa_imp_union (fst p) rep_x rep_y
    <\<lambda>r. is_ufa (ufa_union (ufa_of_ufr ufr) rep_x rep_y) r * is_ufr' ufr (snd p)>"
    unfolding is_ufr_def
    by (sep_auto simp: ufr_\<alpha>_def split: prod.splits)
  from assms rep_in_Field_ufr_\<alpha> have [sep_heap_rules]:
    "<is_ufr' ufr prs>
      Array.upd rep_y (rank_rep_x + rank_rep_y) prs
    <\<lambda>r. is_ufr' (ufr_union ufr x y) r>" for prs
    unfolding is_ufr'_def
    using ufr_invar_ufr_union_raw Abs_ufr_ufr_union_raw_eq_ufr_ufr_union
    by (sep_auto simp: ufa_of_ufr_ufr_union ufr_\<alpha>_def)
  from assms(1,2) have
    "ufa_union (ufa_of_ufr ufr) rep_x rep_y = ufa_union (ufa_of_ufr ufr) x y"
    unfolding rep_x_def rep_y_def ufr_\<alpha>_def ufr_rep_of_def
    by simp
  with rep_in_Field_ufr_\<alpha>[unfolded ufr_\<alpha>_def] show ?thesis
   unfolding ufr_imp_union_raw_def is_ufr_def
   by (sep_auto simp: ufa_of_ufr_ufr_union)
qed

definition "ufr_imp_union_rank p x y \<equiv> do {
  rep_x \<leftarrow> ufr_imp_rep_of p x;
  rep_y \<leftarrow> ufr_imp_rep_of p y;
  if rep_x = rep_y then return p
  else do {
    rank_rep_x \<leftarrow> ufr_imp_rank p rep_x;
    rank_rep_y \<leftarrow> ufr_imp_rank p rep_y;
    if rank_rep_x < rank_rep_y then ufr_imp_union_raw p rep_x rep_y (rank_rep_x + rank_rep_y)
    else ufr_imp_union_raw p rep_y rep_x (rank_rep_y + rank_rep_x)
  }
}"

lemma ufr_imp_union_rank_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufr_\<alpha> ufr)" "y \<in> Field (ufr_\<alpha> ufr)"
  shows "<is_ufr ufr p> ufr_imp_union_rank p x y <is_ufr (ufr_union_rank ufr x y)>"
proof -
  include ufa_ufr_transfer
  from assms have
    "ufr_rep_of ufr x \<in> Field (ufr_\<alpha> ufr)" "ufr_rep_of ufr y \<in> Field (ufr_\<alpha> ufr)"
    by (transfer, simp)+
  moreover from assms have 
    "ufr_rep_of ufr (ufr_rep_of ufr x) = ufr_rep_of ufr x"
    "ufr_rep_of ufr (ufr_rep_of ufr y) = ufr_rep_of ufr y"
    by (transfer, simp)+
  moreover have "eq_ufr (ufr_union_rank ufr x y) ufr"
    if "ufr_rep_of ufr x = ufr_rep_of ufr y"
    using that
    by transfer (metis ufa_union_eq_if_not_in_Field_ufa_\<alpha> ufa_union_eq_if_rep_eq ufa_union_rank_def)
  ultimately show ?thesis
    using is_ufr_entails_is_ufr_if_eq_ufr
    unfolding ufr_imp_union_rank_def ufr_union_rank_def
    by (sep_auto simp: assms)
qed

end