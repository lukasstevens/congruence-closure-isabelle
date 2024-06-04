theory Union_Find_Rank_Int
  imports Union_Find_Rank "List-Index.List_Index"
begin

definition "uf_of_ufri \<equiv> map_index (\<lambda>i x. if x < 0 then i else nat x)"

definition "rank_of_ufri ufri i \<equiv> nat (- (ufri ! i))"

definition "ufri_invar ufri \<equiv>
  ufa_invar (uf_of_ufri ufri) \<and> ufr_invar (Abs_ufa (uf_of_ufri ufri), rank_of_ufri ufri)"

lemma ufri_invarD:
  assumes "ufri_invar ufri"
  shows
    "ufa_invar (uf_of_ufri ufri)"
    "ufr_invar (Abs_ufa (uf_of_ufri ufri), rank_of_ufri ufri)"
  using assms unfolding ufri_invar_def by safe

typedef ufri = "{ufri. ufri_invar ufri}"
proof -
  have "ufa_\<alpha> (Abs_ufa []) = {}"
    unfolding ufa_\<alpha>.rep_eq
    by (simp add: Abs_ufa_inverse Union_Find.\<alpha>_def ufa_invar_def)
  then have "ufri_invar []"
    unfolding ufri_invar_def ufr_invar_def ufa_invar_def uf_of_ufri_def rank_of_ufri_def
    by simp
  then show ?thesis
    by blast
qed

setup_lifting type_definition_ufri

lemma length_uf_of_ufri[simp]:
  "length (uf_of_ufri ufri) = length ufri"
  unfolding uf_of_ufri_def by simp

context
  includes ufa.lifting ufr.lifting
begin

lift_definition ufa_of_ufri :: "ufri \<Rightarrow> ufa" is uf_of_ufri
  unfolding ufri_invar_def by blast

lift_definition ufr_of_ufri :: "ufri \<Rightarrow> ufr" is
  "\<lambda>ufri. (ufa_of_ufri (Abs_ufri ufri), rank_of_ufri ufri)"
  using Abs_ufri_inverse unfolding ufa_of_ufri_def ufri_invar_def
  by simp

definition "ufri_of_uf uf r \<equiv> map_index (\<lambda>i x. if x = i then - (int (r i)) else int x) uf"

lemma uf_of_ufri_ufri_of_uf:
  assumes "ufa_invar uf" "\<forall>i < length uf. uf ! i = i \<longrightarrow> r i > 0"
  shows "uf_of_ufri (ufri_of_uf uf r) = uf"
  using assms
  unfolding uf_of_ufri_def ufri_of_uf_def map_index'_comp
  by (intro map_index_congL) auto

lemma uf_of_ufri_ufri_of_uf_Rep_ufa:
  assumes "\<forall>i \<in> Field (ufa_\<alpha> ufa). ufa_rep_of ufa i = i \<longrightarrow> r i > 0"
  shows "uf_of_ufri (ufri_of_uf (Rep_ufa ufa) r) = Rep_ufa ufa"
  using assms uf_of_ufri_ufri_of_uf ufa_rep_of_if_refl_ufa_parent_of
  by transfer simp

lemma rank_of_ufri_ufri_of_uf:
  assumes "i < length uf" "uf ! i = i"
  shows "rank_of_ufri (ufri_of_uf uf r) i = r i"
  using assms unfolding ufri_of_uf_def rank_of_ufri_def by auto

lemma rank_of_ufri_ufri_of_uf_Rep_ufa:
  assumes "i \<in> Field (ufa_\<alpha> ufa)" "ufa_rep_of ufa i = i"
  shows "rank_of_ufri (ufri_of_uf (Rep_ufa ufa) r) i = r i"
  using assms rank_of_ufri_ufri_of_uf nth_rep_of_eq_rep_of
  by transfer fastforce

lift_definition ufri_of_ufr :: "ufr \<Rightarrow> ufri" is
  "\<lambda>(ufa, r). ufri_of_uf (Rep_ufa ufa) r"
proof -
  fix ufr
  assume "ufr_invar ufr"
  show "?thesis ufr"
  proof(cases ufr)
    case (Pair ufa r)
    with \<open>ufr_invar ufr\<close> have "r i > 0"
      if "i \<in> Field (ufa_\<alpha> ufa)" "ufa_rep_of ufa i = i" for i
      using that card_gt_0_iff
      unfolding ufa_rank_def ufr_invar_def by auto
    
    with \<open>ufr_invar ufr\<close> show ?thesis
      unfolding ufri_invar_def ufr_invar_def Pair
      using Rep_ufa Rep_ufa_inverse
      by (auto simp: uf_of_ufri_ufri_of_uf_Rep_ufa rank_of_ufri_ufri_of_uf_Rep_ufa)
  qed
qed

end

lemma nth_lt_0_if_ufri_invar:
  assumes "ufri_invar ufri"
  assumes "i < length ufri"
  assumes "uf_of_ufri ufri ! i = i"
  shows "ufri ! i < 0"
proof -
  from assms have "i \<in> Field (ufa_\<alpha> (Abs_ufa (uf_of_ufri ufri)))"
    unfolding ufa_\<alpha>.rep_eq ufri_invar_def Abs_ufa_inverse
    by (simp add: Abs_ufa_inverse)
  moreover from assms have "ufa_parent_of (Abs_ufa (uf_of_ufri ufri)) i = i"
    unfolding ufa_parent_of_def ufri_invar_def
    by (simp add: Abs_ufa_inverse)
  note ufa_rep_of_if_refl_ufa_parent_of[OF this]
  moreover from calculation have
    "rank_of_ufri ufri i = ufa_rank (Abs_ufa (uf_of_ufri ufri)) i"
    using assms unfolding ufri_invar_def ufr_invar_def by auto
  ultimately show ?thesis
    unfolding rank_of_ufri_def using ufa_rank_neq_0
    by (metis linorder_not_le nat_le_0 neg_le_0_iff_le)
qed

lemma ufri_of_uf_uf_of_ufri:
  assumes "ufri_invar ufri"
  shows "ufri_of_uf (uf_of_ufri ufri) (rank_of_ufri ufri) = ufri"
  using assms nth_lt_0_if_ufri_invar[OF assms]
  unfolding ufri_of_uf_def uf_of_ufri_def rank_of_ufri_def map_index'_comp
  by (intro map_index_congL) fastforce

lemma ufri_of_ufr_ufr_of_ufri:
  "ufri_of_ufr (ufr_of_ufri ufri) = ufri"
proof -
  have [simp]: "Rep_ufa (ufa_of_ufri (Abs_ufri ufri)) = uf_of_ufri ufri"
    if "ufri_invar ufri" for ufri
    using that
    by (simp add: Abs_ufri_inverse ufa_of_ufri.rep_eq)
  show ?thesis
    by transfer (simp add: ufri_of_uf_uf_of_ufri)
qed

lemma Abs_ufri_eq:
  assumes "ufri_invar ufri"
  shows "Abs_ufri ufri = ufri_of_ufr (Abs_ufr (Abs_ufa (uf_of_ufri ufri), rank_of_ufri ufri))"
  using assms unfolding ufri_of_ufr_def
  by (simp add: ufri_invar_def Abs_ufr_inverse Abs_ufa_inverse ufri_of_uf_uf_of_ufri)

lifting_update ufri.lifting
lifting_forget ufri.lifting

end