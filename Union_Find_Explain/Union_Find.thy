theory Union_Find
  imports Collections.Partial_Equivalence_Relation
begin

definition "parent_of uf i \<equiv> uf ! i"

function (domintros) rep_of 
  where "rep_of uf i = (let pi = parent_of uf i in if pi = i then i else rep_of uf pi)"
  by pat_completeness auto

definition ufa_\<alpha> :: "nat list \<Rightarrow> nat rel" where
  "ufa_\<alpha> uf \<equiv> {(x, y). x < length uf \<and> y < length uf \<and> rep_of uf x = rep_of uf y}"

lemma part_equiv_ufa_\<alpha>[simp, intro!]: "part_equiv (ufa_\<alpha> uf)"
  unfolding ufa_\<alpha>_def
  by (rule part_equivI) (auto intro: symI transI)

definition "ufa_invar uf \<equiv>
  \<forall>i \<in> Field (ufa_\<alpha> uf). rep_of_dom (uf, i) \<and> parent_of uf i \<in> Field (ufa_\<alpha> uf)"

lemma lt_length_if_in_Field_ufa_\<alpha>:
  "i < length uf \<longleftrightarrow> i \<in> Field (ufa_\<alpha> uf)"
  unfolding ufa_\<alpha>_def
  by (auto simp: Field_iff)

lemma ufa_invarD:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  shows rep_of_domI: "rep_of_dom (uf, i)" and "parent_of uf i \<in> Field (ufa_\<alpha> uf)"
  using assms unfolding ufa_invar_def parent_of_def by auto

lemma rep_of_if_refl_parent_of:
  "parent_of uf i = i \<Longrightarrow> rep_of uf i = i"
  by (subst rep_of.psimps) (auto intro: rep_of.domintros)

lemma rep_of_if_irrefl_parent_of:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  assumes "parent_of uf i \<noteq> i"
  shows "rep_of uf i = rep_of uf (parent_of uf i)"
  using assms
  by (subst rep_of.psimps) (auto dest: ufa_invarD)

lemmas rep_of_simps = rep_of_if_refl_parent_of rep_of_if_irrefl_parent_of

lemma rep_of_induct[case_names base step, consumes 2]:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  assumes base: "\<And>i. \<lbrakk> ufa_invar uf; i \<in> Field (ufa_\<alpha> uf); parent_of uf i = i \<rbrakk> \<Longrightarrow> P uf i"
  assumes step: "\<And>i. \<lbrakk> ufa_invar uf; i \<in> Field (ufa_\<alpha> uf); parent_of uf i \<noteq> i; P uf (parent_of uf i) \<rbrakk>
    \<Longrightarrow> P uf i"
  shows "P uf i"
proof -
  note ufa_invarD[OF \<open>ufa_invar uf\<close> \<open>i \<in> Field (ufa_\<alpha> uf)\<close>]
  then have "ufa_invar uf \<and> i \<in> Field (ufa_\<alpha> uf) \<longrightarrow> P uf i"
    by (induction uf\<equiv>uf i rule: rep_of.pinduct) (auto intro: step base dest: ufa_invarD)
  with \<open>ufa_invar uf\<close> \<open>i \<in> Field (ufa_\<alpha> uf)\<close> show ?thesis
    by blast
qed

lemma parent_of_rep_of[simp]:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  shows "parent_of uf (rep_of uf i) = rep_of uf i"
  using rep_of_domI[OF assms] assms
  by (induction rule: rep_of.pinduct) (auto simp: ufa_invarD rep_of.psimps Let_def)

lemma rep_of_in_FieldI[simp, intro]:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  shows "rep_of uf i \<in> Field (ufa_\<alpha> uf)"
  using assms
  by (induction rule: rep_of_induct) (auto simp: rep_of_simps)

lemma rep_of_rep_of[simp]:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  shows "rep_of uf (rep_of uf i) = rep_of uf i"
  using assms by (auto simp: rep_of_simps)

lemma rep_of_upd_rep_of:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "rep_of (uf[rep_of uf x := rep_of uf x]) i = rep_of uf i"
  using assms by (metis list_update_id parent_of_def parent_of_rep_of)

lemma rep_of_parent_of[simp]:
  assumes "ufa_invar uf" "i \<in> Field (ufa_\<alpha> uf)"
  shows "rep_of uf (parent_of uf i) = rep_of uf i"
  using assms by (metis rep_of_if_irrefl_parent_of)

lemma rep_of_eq_iff_in_ufa_\<alpha>:
  assumes "ufa_invar uf" "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "rep_of uf x = rep_of uf y \<longleftrightarrow> (x, y) \<in> ufa_\<alpha> uf"
  using assms unfolding ufa_\<alpha>_def by (auto simp: Field_iff)

definition "ufa_init n \<equiv> [0..<n]"

lemma length_ufa_init[simp]: "length (ufa_init n) = n"
  unfolding ufa_init_def by simp

lemma Field_ufa_\<alpha>_ufa_init[simp]: "Field (ufa_\<alpha> (ufa_init n)) = {0..<n}"
  unfolding ufa_init_def ufa_\<alpha>_def by (auto simp: Field_iff)

lemma parent_of_ufa_init[simp]:
  assumes "i \<in> Field (ufa_\<alpha> (ufa_init n))"
  shows "parent_of (ufa_init n) i = i"
  using assms unfolding parent_of_def ufa_init_def ufa_\<alpha>_def
  by (auto simp: Field_iff)

lemma ufa_invar_ufa_init[simp, intro!]: "ufa_invar (ufa_init n)"
  unfolding ufa_invar_def
  by (auto intro: rep_of.domintros)

lemma ufa_\<alpha>_ufa_init: "ufa_\<alpha> (ufa_init n) = {(x, x)|x. x < n}"
  unfolding ufa_\<alpha>_def using ufa_invar_ufa_init[of n]
  by (auto simp: rep_of_if_refl_parent_of)

definition "ufa_union uf x y = uf[rep_of uf x := rep_of uf y]"

lemma Field_ufa_\<alpha>_ufa_union[simp]:
  assumes "ufa_invar uf" "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "Field (ufa_\<alpha> (ufa_union uf x y)) = Field (ufa_\<alpha> uf)"
  using assms unfolding ufa_\<alpha>_def ufa_union_def
  by (auto simp: Field_iff)

lemma parent_of_ufa_union:
  assumes "z \<in> Field (ufa_\<alpha> uf)"
  shows "parent_of (ufa_union uf x y) z =
    (if z = rep_of uf x then rep_of uf y else parent_of uf z)"
  unfolding parent_of_def ufa_union_def
  using assms lt_length_if_in_Field_ufa_\<alpha> by auto

lemma ufa_invar_ufa_union:
  assumes "ufa_invar uf" "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_invar (ufa_union uf x y)"
proof -
  have "rep_of_dom (ufa_union uf x y, i)" if "i \<in> Field (ufa_\<alpha> uf)" for i
    using assms(1) that assms(2-)
  proof(induct rule: rep_of_induct)
    case (base i)
    note [intro!] = rep_of.domintros[where i=i] rep_of.domintros[where i="parent_of uf i" for uf]
    from base show ?case
      by (auto simp: parent_of_ufa_union)
  next
    case (step i)
    then show ?case
      by(auto simp: parent_of_ufa_union intro!: rep_of.domintros[where i=i])
  qed
  with assms show ?thesis
    by (fastforce simp: parent_of_ufa_union ufa_invar_def)
qed

lemma rep_of_ufa_union:
  assumes "ufa_invar uf" "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "i \<in> Field (ufa_\<alpha> uf)"
  shows "rep_of (ufa_union uf x y) i =
    (if rep_of uf i = rep_of uf x then rep_of uf y else rep_of uf i)"
  using \<open>ufa_invar uf\<close> \<open>i \<in> Field (ufa_\<alpha> uf)\<close>
proof(induction rule: rep_of_induct)
  case (base i)
  with assms(2,3) show ?case
    sorry
next
  case (step i)
  then show ?case sorry
qed

lemma ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha>[simp]:
  assumes "ufa_invar uf" "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_\<alpha> (ufa_union uf x y) = per_union (ufa_\<alpha> uf) x y"
  unfolding ufa_\<alpha>_def per_union_def using assms
  by (auto simp: rep_of_ufa_union lt_length_if_in_Field_ufa_\<alpha> split: if_split_asm)



end