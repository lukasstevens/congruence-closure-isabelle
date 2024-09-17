theory Union_Find_Size_Imp
  imports Union_Find_Size Union_Find_Imp
begin

type_synonym ufs_imp = "(nat array \<times> nat array)"

definition is_ufs' :: "ufs \<Rightarrow> nat array \<Rightarrow> assn" where
  "is_ufs' ufs prs \<equiv> \<exists>\<^sub>Ars. prs \<mapsto>\<^sub>a rs *
    \<up>((\<forall>i \<in> Field (ufs_\<alpha> ufs). i < length rs) \<and>
    ufs_invar (ufa_of_ufs ufs, (!) rs) \<and>
    eq_ufs (Abs_ufs (ufa_of_ufs ufs, (!) rs)) ufs)"

definition is_ufs :: "ufs \<Rightarrow> ufs_imp \<Rightarrow> assn" where
  "is_ufs ufs p \<equiv>
    is_ufa (ufa_of_ufs ufs) (fst p) *
    is_ufs' ufs (snd p)"

lemma is_ufs_entails_is_ufs_if_eq_ufs:
  assumes "eq_ufs ufs2 ufs1"
  shows "is_ufs ufs1 p \<Longrightarrow>\<^sub>A is_ufs ufs2 p"
  using assms unfolding is_ufs_def is_ufa_def is_ufs'_def eq_ufs_def
  by (sep_auto simp: ufs_\<alpha>_def ufs_size_def)

definition ufs_imp_init :: "nat \<Rightarrow> ufs_imp Heap" where
  "ufs_imp_init n \<equiv> do {
    puf \<leftarrow> ufa_imp_init n;
    prs \<leftarrow> Array.new n (1::nat);
    return (puf, prs)
  }"

lemma ufa_of_ufs_ufs_init_eq_ufa_init[simp]:
  "ufa_of_ufs (ufs_init n) = ufa_init n"
  by (simp add: ufa_of_ufs.rep_eq ufs_init.rep_eq)

lemma ufs_imp_init_rule[sep_heap_rules]:
  "<emp> ufs_imp_init n <is_ufs (ufs_init n)>"
proof -
  let ?ufs_init' = "\<lambda>n. (ufa_init n, (!) (replicate n 1))"
  have "ufs_invar (?ufs_init' n)"
    by (auto simp: ufa_size_ufa_init intro!: ufs_invarI)
  moreover from this have "eq_ufs (Abs_ufs (?ufs_init' n)) (ufs_init n)"
    unfolding eq_ufs_def ufs_size_def
    including ufa_ufs_transfer supply ufa_of_ufs_transfer[transfer_rule]
    by transfer (auto simp: eq_onp_same_args ufa_of_ufs.abs_eq)
  ultimately show ?thesis
    unfolding ufs_imp_init_def is_ufs_def is_ufs'_def
    by (sep_auto simp: ufs_\<alpha>_def)
qed

definition "ufs_imp_parent_of p \<equiv> ufa_imp_parent_of (fst p)"

lemma ufs_imp_parent_of_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufs_\<alpha> ufs)"
  shows "<is_ufs ufs p> ufs_imp_parent_of p x <\<lambda>r. is_ufs ufs p * \<up>(r = ufs_parent_of ufs x)>"
  using assms unfolding ufs_imp_parent_of_def is_ufs_def
  by (cases p) (sep_auto simp: ufs_\<alpha>_def ufs_parent_of_def)

definition "ufs_imp_rep_of p \<equiv> ufa_imp_rep_of (fst p)"

lemma ufs_imp_rep_of_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufs_\<alpha> ufs)"
  shows "<is_ufs ufs p> ufs_imp_rep_of p x <\<lambda>r. is_ufs ufs p * \<up>(r = ufs_rep_of ufs x)>"
  using assms unfolding ufs_imp_rep_of_def is_ufs_def
  by (cases p) (sep_auto simp: ufs_\<alpha>_def ufs_rep_of_def)

definition "ufs_imp_size p x \<equiv> Array.nth (snd p) x"

lemma ufs_imp_size_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufs_\<alpha> ufs)"
  assumes "ufs_rep_of ufs x = x"
  shows "<is_ufs ufs p> ufs_imp_size p x <\<lambda>r. is_ufs ufs p * \<up>(r = ufs_size ufs x)>"
  using assms unfolding is_ufs_def is_ufs'_def ufs_imp_size_def  ufs_invar_def
  by (sep_auto simp: ufs_\<alpha>_def ufs_rep_of_def ufs_size_def split: prod.splits)

definition "ufs_imp_union_raw p rep_x rep_y sz \<equiv> do {
  puf' \<leftarrow> ufa_imp_union (fst p) rep_x rep_y;
  prs' \<leftarrow> Array.upd rep_y sz (snd p);
  return (puf', prs')
}"

lemma ufs_invar_ufs_union_raw:
  fixes rs :: "nat list"
  assumes "ufs_invar (ufa_of_ufs ufs, (!) rs)" "\<forall>i \<in> Field (ufs_\<alpha> ufs). i < length rs"
  assumes "x \<in> Field (ufs_\<alpha> ufs)" "y \<in> Field (ufs_\<alpha> ufs)"
  defines "rep_x \<equiv> ufs_rep_of ufs x" and "rep_y \<equiv> ufs_rep_of ufs y"
  defines "sz_rep_x \<equiv> ufs_size ufs rep_x" and "sz_rep_y \<equiv> ufs_size ufs rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "ufs_invar (ufa_union (ufa_of_ufs ufs) x y, (!) (rs[rep_y := sz_rep_x + sz_rep_y]))"
proof -
  include ufa_ufs_transfer
  note ufa_of_ufs_transfer[transfer_rule]
  from assms(1-4,9) show ?thesis
    unfolding ufa_of_ufs_ufs_union[symmetric]
    unfolding ufs_invar_def assms(5-8)
    by transfer
      (auto simp: nth_list_update ufa_rep_of_ufa_union ufa_size_ufa_union_if_ufa_rep_of_neq)
qed

lemma Abs_ufs_ufs_union_raw_eq_ufs_ufs_union:
  fixes rs :: "nat list"
  assumes "eq_ufs (Abs_ufs (ufa_of_ufs ufs, (!) rs)) ufs"
  assumes "ufs_invar (ufa_of_ufs ufs, (!) rs)" "\<forall>i \<in> Field (ufs_\<alpha> ufs). i < length rs"
  assumes "x \<in> Field (ufs_\<alpha> ufs)" "y \<in> Field (ufs_\<alpha> ufs)"
  defines "rep_x \<equiv> ufs_rep_of ufs x" and "rep_y \<equiv> ufs_rep_of ufs y"
  defines "sz_rep_x \<equiv> ufs_size ufs rep_x" and "sz_rep_y \<equiv> ufs_size ufs rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "eq_ufs (Abs_ufs (ufa_union (ufa_of_ufs ufs) x y, (!) (rs[rep_y := sz_rep_x + sz_rep_y])))
      (ufs_union ufs x y)"
proof -  
  note ufs_invar_ufs_union_raw[OF assms(2-5) assms(10)[unfolded rep_x_def rep_y_def]]
  then show ?thesis
    unfolding assms(6-9) eq_ufs_def ufs_size_def
    by (auto simp: ufa_of_ufs_ufs_union eq_onp_same_args ufa_of_ufs.abs_eq)
qed

lemma ufs_imp_union_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufs_\<alpha> ufs)" "y \<in> Field (ufs_\<alpha> ufs)"
  defines "rep_x \<equiv> ufs_rep_of ufs x"
  defines "rep_y \<equiv> ufs_rep_of ufs y"
  defines "sz_rep_x \<equiv> ufs_size ufs rep_x"
  defines "sz_rep_y \<equiv> ufs_size ufs rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows 
    "<is_ufs ufs p>
      ufs_imp_union_raw p rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufs (ufs_union ufs x y)>"
proof -
  from assms(1,2) have rep_in_Field_ufs_\<alpha>:
    "rep_x \<in> Field (ufs_\<alpha> ufs)" "rep_y \<in> Field (ufs_\<alpha> ufs)"
    unfolding rep_x_def rep_y_def including ufa_ufs_transfer by (transfer, simp)+
  with assms have [sep_heap_rules]:
    "<is_ufs ufs p> ufa_imp_union (fst p) rep_x rep_y
    <\<lambda>r. is_ufa (ufa_union (ufa_of_ufs ufs) rep_x rep_y) r * is_ufs' ufs (snd p)>"
    unfolding is_ufs_def
    by (sep_auto simp: ufs_\<alpha>_def split: prod.splits)
  from assms rep_in_Field_ufs_\<alpha> have [sep_heap_rules]:
    "<is_ufs' ufs prs>
      Array.upd rep_y (sz_rep_x + sz_rep_y) prs
    <\<lambda>r. is_ufs' (ufs_union ufs x y) r>" for prs
    unfolding is_ufs'_def
    using ufs_invar_ufs_union_raw Abs_ufs_ufs_union_raw_eq_ufs_ufs_union
    by (sep_auto simp: ufa_of_ufs_ufs_union ufs_\<alpha>_def)
  from assms(1,2) have
    "ufa_union (ufa_of_ufs ufs) rep_x rep_y = ufa_union (ufa_of_ufs ufs) x y"
    unfolding rep_x_def rep_y_def ufs_\<alpha>_def ufs_rep_of_def
    by simp
  with rep_in_Field_ufs_\<alpha>[unfolded ufs_\<alpha>_def] show ?thesis
   unfolding ufs_imp_union_raw_def is_ufs_def
   by (sep_auto simp: ufa_of_ufs_ufs_union)
qed

definition "ufs_imp_union_size p x y \<equiv> do {
  rep_x \<leftarrow> ufs_imp_rep_of p x;
  rep_y \<leftarrow> ufs_imp_rep_of p y;
  if rep_x = rep_y then return p
  else do {
    sz_rep_x \<leftarrow> ufs_imp_size p rep_x;
    sz_rep_y \<leftarrow> ufs_imp_size p rep_y;
    if sz_rep_x < sz_rep_y then ufs_imp_union_raw p rep_x rep_y (sz_rep_x + sz_rep_y)
    else ufs_imp_union_raw p rep_y rep_x (sz_rep_y + sz_rep_x)
  }
}"

lemma ufs_imp_union_size_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufs_\<alpha> ufs)" "y \<in> Field (ufs_\<alpha> ufs)"
  shows "<is_ufs ufs p> ufs_imp_union_size p x y <is_ufs (ufs_union_size ufs x y)>"
proof -
  include ufa_ufs_transfer
  from assms have
    "ufs_rep_of ufs x \<in> Field (ufs_\<alpha> ufs)" "ufs_rep_of ufs y \<in> Field (ufs_\<alpha> ufs)"
    by (transfer, simp)+
  moreover from assms have 
    "ufs_rep_of ufs (ufs_rep_of ufs x) = ufs_rep_of ufs x"
    "ufs_rep_of ufs (ufs_rep_of ufs y) = ufs_rep_of ufs y"
    by (transfer, simp)+
  moreover have "eq_ufs (ufs_union_size ufs x y) ufs"
    if "ufs_rep_of ufs x = ufs_rep_of ufs y"
    using that
    by transfer (metis ufa_union_eq_if_not_in_Field_ufa_\<alpha> ufa_union_eq_if_rep_eq ufa_union_size_def)
  ultimately show ?thesis
    using is_ufs_entails_is_ufs_if_eq_ufs
    unfolding ufs_imp_union_size_def ufs_union_size_def
    by (sep_auto simp: assms)
qed

end