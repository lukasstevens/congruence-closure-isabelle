theory Union_Find_Rank_Int_Quotient
  imports Union_Find_Rank_Int
begin

lemma ufri_of_ufr_eq_if_eq_ufr:
  includes ufa.lifting ufr.lifting ufri.lifting
  assumes "eq_ufr ufr1 ufr2"
  shows "ufri_of_ufr ufr1 = ufri_of_ufr ufr2"
  using assms unfolding eq_ufr_def ufr_\<alpha>_def ufr_rep_of_def ufr_rank_def
  apply (transfer, unfold ufr_invar_def, transfer)
  by (simp add: ufri_of_uf_def rep_of.psimps ufa_invarD(1)
      map_index_cong pred_prod_beta split: prod.splits)

lemma eq_ufr_if_ufri_of_ufr_eq:
  includes ufa.lifting ufr.lifting ufri.lifting
  assumes "ufri_of_ufr ufr1 = ufri_of_ufr ufr2"
  shows "eq_ufr ufr1 ufr2"
  using assms unfolding eq_ufr_def ufr_\<alpha>_def ufr_rep_of_def ufr_rank_def
  apply (transfer, unfold ufr_invar_def case_prod_unfold)
  by (metis Rep_ufa_inject gr_zeroI uf_of_ufri_ufri_of_uf_Rep_ufa ufa_rank_neq_0)

definition "ufr_ufri_rel ufr ufri \<equiv> ufri = ufri_of_ufr ufr"

lemma right_unique_ufr_ufri_rel[transfer_rule]:
  "right_unique ufr_ufri_rel"
  unfolding right_unique_def ufr_ufri_rel_def by blast

lemma bi_total_ufr_ufri_rel[transfer_rule]:
  "bi_total ufr_ufri_rel"
  unfolding bi_total_def right_total_def ufr_ufri_rel_def
  by (metis ufri_of_ufr_ufr_of_ufri)

lemma Quotient_ufri_ufr:
  "Quotient eq_ufr ufri_of_ufr ufr_of_ufri ufr_ufri_rel"
  using ufri_of_ufr_ufr_of_ufri ufri_of_ufr_eq_if_eq_ufr eq_ufr_if_ufri_of_ufr_eq
  unfolding ufr_ufri_rel_def
  by (intro QuotientI) blast+

setup_lifting Quotient_ufri_ufr reflp_eq_ufr

lift_definition ufri_\<alpha> :: "ufri \<Rightarrow> nat rel" is ufr_\<alpha>
  unfolding eq_ufr_def ufr_rep_of_def ufr_\<alpha>_def ufr_rank_def
  including ufr.lifting
  by transfer auto

lift_definition ufri_parent_of :: "ufri \<Rightarrow> nat \<Rightarrow> nat" is ufr_parent_of
  unfolding eq_ufr_def ufr_parent_of_def ufr_rep_of_def ufr_\<alpha>_def ufr_rank_def
  including ufr.lifting
  by transfer auto

lift_definition ufri_rep_of :: "ufri \<Rightarrow> nat \<Rightarrow> nat" is ufr_rep_of
  unfolding eq_ufr_def ufr_rep_of_def ufr_\<alpha>_def ufr_rank_def
  including ufr.lifting
  by transfer auto

lift_definition ufri_rank :: "ufri \<Rightarrow> nat \<Rightarrow> nat" is ufr_rank
  unfolding eq_ufr_def ufr_parent_of_def ufr_rep_of_def ufr_\<alpha>_def ufr_rank_def
  including ufr.lifting
  by transfer auto

lemma ufri_rep_of_induct[case_names "parametric" rep not_rep, consumes 1]:
  includes lifting_syntax
  assumes "i \<in> Field (ufri_\<alpha> uf)"
  assumes
    "(ufa_ufr_rel ===> (=) ===> (=))
      (\<lambda>ufa. P (ufri_of_ufr (ufr_of_ufa ufa))) (\<lambda>ufr. P (ufri_of_ufr ufr))"
  assumes rep: "\<And>i. \<lbrakk> i \<in> Field (ufri_\<alpha> uf); ufri_parent_of uf i = i \<rbrakk> \<Longrightarrow> P uf i"
  assumes not_rep:
    "\<And>i. \<lbrakk> i \<in> Field (ufri_\<alpha> uf); ufri_parent_of uf i \<noteq> i; P uf (ufri_parent_of uf i) \<rbrakk>
    \<Longrightarrow> P uf i"
  shows "P uf i"
proof -
  from assms(2) have [transfer_rule]:
    "(pcr_ufri ===> (=) ===> (=)) (\<lambda>ufr. P (ufri_of_ufr ufr)) P"
    using ufr_ufri_rel_def ufri.pcr_cr_eq by fastforce
  from assms(1,3-) show ?thesis
    by (transfer fixing: P) (rule ufr_rep_of_induct[OF _ assms(2)])
qed  

lift_definition ufri_init :: "nat \<Rightarrow> ufri" is ufr_init .

lemma eq_ufr_ufr_union_if_eq_ufr:
  assumes "eq_ufr ufr1 ufr2"
  shows "eq_ufr (ufr_union ufr1 x y) (ufr_union ufr2 x y)"
  using assms
  unfolding eq_ufr_def ufr_rep_of_def ufr_parent_of_def ufr_\<alpha>_def ufr_rank_def
  including ufr.lifting
  by transfer (simp add: case_prod_unfold ufa_rep_of_ufa_union Let_def split: if_splits)

lift_definition ufri_union :: "ufri \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufri" is ufr_union
  by (fact eq_ufr_ufr_union_if_eq_ufr)

lift_definition ufri_union_rank :: "ufri \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufri" is ufr_union_rank
proof -
  fix ufr1 ufr2 x y
  assume "eq_ufr ufr1 ufr2"
  show "?thesis ufr1 ufr2 x y"
  proof(cases "x \<in> Field (ufr_\<alpha> ufr1) \<and> y \<in> Field (ufr_\<alpha> ufr2)")
    case False
    with ufr_\<alpha>_eq_if_eq_ufr[OF \<open>eq_ufr ufr1 ufr2\<close>] have
      "ufr_union ufr1 x y = ufr1" "ufr_union ufr1 y x = ufr1"
      "ufr_union ufr2 x y = ufr2" "ufr_union ufr2 y x = ufr2"
      including ufr.lifting unfolding ufr_\<alpha>_def by (transfer; auto)+  
    with \<open>eq_ufr ufr1 ufr2\<close> show ?thesis
      unfolding ufr_union_rank_def by simp
  next
    case True
    with \<open>eq_ufr ufr1 ufr2\<close> show ?thesis
      unfolding ufr_union_rank_def
      by (auto simp: eq_ufr_ufr_union_if_eq_ufr ufr_rank_eq_if_eq_ufr)
  qed
qed
 
lift_definition ufri_compress :: "ufri \<Rightarrow> nat \<Rightarrow> ufri" is ufr_compress
  unfolding eq_ufr_def ufr_rep_of_def ufr_\<alpha>_def ufr_rank_def
  including ufr.lifting
  by transfer (simp add: case_prod_unfold)

lemma ufr_of_ufri_Abs_ufri_transfer[transfer_rule]:
  includes lifting_syntax
  shows "((=) ===> pcr_ufri) (\<lambda>ufri. ufr_of_ufri (Abs_ufri ufri)) Abs_ufri"
  unfolding ufri.pcr_cr_eq ufr_ufri_rel_def using ufri_of_ufr_ufr_of_ufri
  by (intro rel_funI) simp

lemma ufa_of_ufr_ufr_of_ufri_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(pcr_ufri ===> ufa_ufr_rel) ufa_of_ufr ufr_of_ufri"
  unfolding ufri.pcr_cr_eq ufr_ufri_rel_def ufa_ufr_rel_def
  by (metis (mono_tags, lifting) Quotient_rep_abs_fold_unmap Quotient_ufri_ufr eq_ufr_def rel_funI)

lemma ufr_of_ufa_ufri_of_ufr_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(ufa_ufr_rel ===> pcr_ufri) ufr_of_ufa ufri_of_ufr"
  unfolding ufa_ufr_rel_def ufr_ufri_rel_def ufri.pcr_cr_eq
  by (intro rel_funI, transfer)
    (auto simp: eq_ufr_ufr_of_ufa_ufa_of_ufr)

lemma ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri:
  "ufa_of_ufri ufri = ufa_of_ufr (ufr_of_ufri ufri)"
  by (simp add: Rep_ufri_inverse ufa_of_ufr.rep_eq ufr_of_ufri.rep_eq)

lemma ufa_of_ufri_transfer[transfer_rule]:
  includes lifting_syntax ufa_ufr_transfer
  notes [transfer_rule] = ufa_of_ufr_transfer
  shows "(pcr_ufri ===> (=)) ufa_of_ufr ufa_of_ufri"
  unfolding ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri ufri.pcr_cr_eq ufr_ufri_rel_def
  by (intro rel_funI, transfer)
    (metis eq_ufr_def fst_conv ufa_of_ufr.rep_eq ufr_of_ufa.rep_eq)

lemma ufri_of_ufr_ufr_of_ufa_ufa_of_ufr[simp]:
  includes ufa_ufr_transfer
  notes ufa_of_ufr_transfer[transfer_rule]
  shows "ufri_of_ufr (ufr_of_ufa (ufa_of_ufr ufr)) = ufri_of_ufr ufr"
  by transfer simp

lemma ufa_of_ufr_ufr_of_ufri_Abs_ufri_eq:
  assumes "ufri_invar ufri"
  shows "ufa_of_ufr (ufr_of_ufri (Abs_ufri ufri)) = Abs_ufa (uf_of_ufri ufri)"
  using assms
  by (simp add: Rep_ufri_inverse eq_onp_same_args
      ufa_of_ufr.rep_eq ufa_of_ufri.abs_eq ufr_of_ufri.rep_eq)

lemma map_index_congL':
  assumes "\<forall>i < length xs. f i (xs ! i) = ys ! i"
  assumes "length xs = length ys"
  shows "map_index f xs = ys"
  using assms
  by (metis length_map_index' nth_equalityI nth_map_index)

lemma uf_of_ufri_replicate_neg_1_eq[simp]:
  "uf_of_ufri (replicate n (-1)) = [0..<n]"
  unfolding uf_of_ufri_def 
  by (intro map_index_congL') auto

lemma rank_of_ufri_replicate_neg_1_eq:
  assumes "i < n"
  shows "rank_of_ufri (replicate n (-1)) i = (if i < n then 1 else undefined)"
  using assms rank_of_ufri_def by force

lemma ufri_invar_replicate_neg_1:
  "ufri_invar (replicate n (-1))"
proof -
  have "ufa_invar (uf_of_ufri (replicate n (-1)))"
    unfolding ufa_invar_def
    by (auto intro: rep_of.domintros)
  moreover have
    "ufr_invar (Abs_ufa (uf_of_ufri (replicate n (-1))), rank_of_ufri (replicate n (-1)))"
    using ufa_\<alpha>_ufa_init ufa_rank_ufa_init
    unfolding ufr_invar_def ufa_init.abs_eq
    by (auto simp: rank_of_ufri_replicate_neg_1_eq Field_iff)
  ultimately show ?thesis
    unfolding ufri_invar_def by blast
qed

lemma Abs_ufri_replicate_neg_1_eq_ufri_init:
  includes ufa.lifting ufa_ufr_transfer
  notes [transfer_rule] = Rep_ufa_ufa_of_ufr_transfer
  shows "Abs_ufri (replicate n (-1)) = ufri_init n"
  apply (transfer, transfer, transfer)
  using ufa_of_ufr_ufr_of_ufri_Abs_ufri_eq[OF ufri_invar_replicate_neg_1]
  using ufa_init.rep_eq ufa_init.abs_eq
  by simp

lemma ufri_rep_of_in_Field_ufri_\<alpha>I[simp, intro]:
  includes ufa_ufr_transfer
  assumes "i \<in> Field (ufri_\<alpha> ufri)"
  shows "ufri_rep_of ufri i \<in> Field (ufri_\<alpha> ufri)"
  using assms by (transfer, transfer) simp

lemma ufri_rep_of_ufri_rep_of[simp]:
  includes ufa_ufr_transfer
  assumes "i \<in> Field (ufri_\<alpha> ufri)"
  shows "ufri_rep_of ufri (ufri_rep_of ufri i) = ufri_rep_of ufri i"
  using assms by (transfer, transfer) simp

lemma lt_length_if_in_Field_ufri_\<alpha>_Abs_ufri:
  includes ufa_ufr_transfer ufa.lifting
  notes [transfer_rule] = Rep_ufa_ufa_of_ufr_transfer
  assumes "ufri_invar ufri"
  assumes "i \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  shows "i < length ufri"
  using assms
  apply(transfer, transfer, transfer)
  using Abs_ufri_inverse ufa_of_ufr.rep_eq ufa_of_ufri.rep_eq ufr_of_ufri.rep_eq
  by auto

lemma eq_uf_of_ufri[simp]:
  assumes "ufri_invar ufri"
  shows "Rep_ufa (ufa_of_ufr (ufr_of_ufri (Abs_ufri ufri))) = uf_of_ufri ufri"
  using assms
  by (simp add: Abs_ufri_inverse ufa_of_ufr.rep_eq ufa_of_ufri.rep_eq ufr_of_ufri.rep_eq)

lemma ufri_parent_of_Abs_ufri_eq:
  includes ufa.lifting ufa_ufr_transfer
  notes [transfer_rule] = Rep_ufa_ufa_of_ufr_transfer
  assumes "ufri_invar ufri"
  assumes "i \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  shows "ufri_parent_of (Abs_ufri ufri) i = (if ufri ! i < 0 then i else nat (ufri ! i))"
  using assms
  apply transfer
  apply transfer
  apply transfer
  by (simp add: uf_of_ufri_def)

lemma ufri_rep_of_Abs_ufri_eq:
  includes ufa.lifting ufa_ufr_transfer
  notes [transfer_rule] = Rep_ufa_ufa_of_ufr_transfer
  assumes "ufri_invar ufri"
  assumes "i \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  shows "ufri_rep_of (Abs_ufri ufri) i =
    (let pi = ufri_parent_of (Abs_ufri ufri) i
    in if pi = i then i else ufri_rep_of (Abs_ufri ufri) pi)"
  using assms
  apply transfer
  apply transfer
  apply transfer
  by (simp add: Let_def rep_of.psimps ufa_invarD(1) ufri_invarD(1))

lemma ufri_rank_Abs_ufri:
  assumes "ufri_invar ufri"
  assumes "x \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  assumes "ufri_rep_of (Abs_ufri ufri) x = x"
  shows "ufri_rank (Abs_ufri ufri) x = rank_of_ufri ufri x"
  using assms ufr_rank_Abs_ufr[OF assms(1)[THEN ufri_invarD(2)]]
  by transfer (auto simp: ufr_of_ufri.abs_eq ufa_of_ufri.abs_eq eq_onp_same_args)

lemma map_index_list_update:
  "map_index f (list_update xs i x) = list_update (map_index f xs) i (f i x)"
  apply(intro map_index_congL')
  by (cases "i < length xs") (auto simp: nth_list_update)

lemma uf_of_ufri_list_update:
  "uf_of_ufri (ufri[i := x]) = (uf_of_ufri ufri)[i := (if x < 0 then i else nat x)]"
  unfolding uf_of_ufri_def map_index_list_update by blast

lemma ufri_union_Abs_ufri:
  notes [transfer_rule] = Rep_ufa_ufa_of_ufr_transfer
  assumes "ufri_invar ufri"
  assumes "x \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  assumes "y \<in> Field (ufri_\<alpha> (Abs_ufri ufri))"
  defines "rep_x \<equiv> ufri_rep_of (Abs_ufri ufri) x"
  defines "rep_y \<equiv> ufri_rep_of (Abs_ufri ufri) y"
  defines "r_rep_x \<equiv> ufri_rank (Abs_ufri ufri) rep_x"
  defines "r_rep_y \<equiv> ufri_rank (Abs_ufri ufri) rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "ufri_invar (ufri[rep_x := int rep_y, rep_y := - int (r_rep_x + r_rep_y)])"
      (is "ufri_invar ?ufri'")
  and
    "ufri_union (Abs_ufri ufri) x y =
    Abs_ufri (ufri[rep_x := int rep_y, rep_y := - int (r_rep_x + r_rep_y)])"
proof -
  let ?ufa = "Abs_ufa (uf_of_ufri ufri)"
  
  note ufa_invar = \<open>ufri_invar ufri\<close>[THEN ufri_invarD(1)]
  from ufa_invar assms(2,3) have in_Field_ufa_\<alpha>:
    "x \<in> Field (ufa_\<alpha> ?ufa)" "y \<in> Field (ufa_\<alpha> ?ufa)"
    using lt_length_if_in_Field_ufri_\<alpha>_Abs_ufri[OF assms(1)]
    by (simp_all add: Abs_ufa_inverse ufa_\<alpha>.rep_eq)
  from assms(1) have rep_eq_ufa_rep_of:
    "rep_x = ufa_rep_of ?ufa x"
    "rep_y = ufa_rep_of ?ufa y"
    unfolding rep_x_def rep_y_def including ufa_ufr_transfer
    by (transfer, transfer, metis Rep_ufa_inverse eq_uf_of_ufri)+
  from assms(1) have r_rep_eq_ufa_rank:
    "r_rep_x = ufa_rank ?ufa (ufa_rep_of ?ufa x) "
    "r_rep_y = ufa_rank ?ufa (ufa_rep_of ?ufa y)"
    unfolding r_rep_x_def r_rep_y_def rep_eq_ufa_rep_of
    including ufa_ufr_transfer
    by (transfer, transfer, metis Rep_ufa_inverse eq_uf_of_ufri)+
 
  from assms(1-3) have "ufa_invar (uf_of_ufri (ufri[rep_x := int rep_y]))"
    unfolding rep_x_def rep_y_def uf_of_ufri_list_update
    including ufa_ufr_transfer ufa.lifting
    by (transfer, transfer, transfer)
      (simp add: ufa_invar_list_update_rep_of_rep_of ufri_invarD(1))
  moreover have swap:
    "ufri[rep_y := - int (r_rep_x + r_rep_y), rep_x := int rep_y] =
    ufri[rep_x := int rep_y, rep_y := - int (r_rep_x + r_rep_y)]"
    using \<open>rep_x \<noteq> rep_y\<close> by (metis list_update_swap)
  moreover have
    "uf_of_ufri (ufri[rep_y := - int (r_rep_x + r_rep_y)]) = uf_of_ufri ufri"
  proof -
    from in_Field_ufa_\<alpha> ufa_rank_neq_0 have "r_rep_x > 0" "r_rep_y > 0"
      unfolding r_rep_eq_ufa_rank by simp_all
    moreover from ufa_invar in_Field_ufa_\<alpha> have "uf_of_ufri ufri ! rep_y = rep_y"
      unfolding rep_eq_ufa_rep_of
      by (metis ufa_parent_of.abs_eq ufa_parent_of_ufa_rep_of eq_onp_eqD)
    ultimately show ?thesis
      unfolding uf_of_ufri_list_update by simp (metis list_update_id)
  qed
  ultimately have uf_of_ufri'_eq:
    "uf_of_ufri ?ufri' = uf_of_ufri (ufri[rep_x := int rep_y])"
    by (metis uf_of_ufri_list_update)
  with \<open>ufa_invar (uf_of_ufri (ufri[rep_x := int rep_y]))\<close> have "ufa_invar (uf_of_ufri ?ufri')"
    by simp

  from assms(1-3) have uf_of_ufri'_eq_ufa_union:
    "Abs_ufa (uf_of_ufri ?ufri') = ufa_union ?ufa x y"
  proof -
    from assms(1) have eq_onp_ufa_invar_uf_of_ufri:
      "eq_onp ufa_invar (uf_of_ufri ufri) (uf_of_ufri ufri)"
      by (simp add: eq_onp_same_args ufri_invarD(1))
    from assms(1-3) show ?thesis
      unfolding uf_of_ufri'_eq
      unfolding ufa_union.abs_eq[OF eq_onp_ufa_invar_uf_of_ufri]
      unfolding rep_x_def rep_y_def r_rep_x_def r_rep_y_def
      including ufa_ufr_transfer ufa.lifting
      by (transfer, transfer, transfer) (simp add: uf_of_ufri_list_update)
  qed

  have "ufr_invar (Abs_ufa (uf_of_ufri ?ufri'), rank_of_ufri ?ufri')"
  proof (rule ufr_invarI)
    fix i
    assume i_in_Field': "i \<in> Field (ufa_\<alpha> (Abs_ufa (uf_of_ufri ?ufri')))"
    assume i_is_ufa_rep': "ufa_rep_of (Abs_ufa (uf_of_ufri ?ufri')) i = i"
    from i_in_Field' have i_in_Field:
      "i \<in> Field (ufa_\<alpha> ?ufa)"
      unfolding uf_of_ufri'_eq_ufa_union by force
    from in_Field_ufa_\<alpha> i_in_Field i_is_ufa_rep' have i_is_ufa_rep:
      "ufa_rep_of ?ufa i = i"
      unfolding uf_of_ufri'_eq_ufa_union
      by (metis ufa_rep_of_ufa_rep_of ufa_rep_of_ufa_union)
    from i_in_Field' i_is_ufa_rep' \<open>rep_x \<noteq> rep_y\<close> have "i \<noteq> rep_x"
      unfolding uf_of_ufri'_eq_ufa_union
      using in_Field_ufa_\<alpha> rep_eq_ufa_rep_of by auto    
    have rank_of_ufri'_eq: "rank_of_ufri ?ufri' i =
      (if i = rep_y then r_rep_x + r_rep_y else rank_of_ufri ufri i)"
    proof -
      from assms(1-3) have "rep_x < length ufri" "rep_y < length ufri"
        using lt_length_if_in_Field_ufri_\<alpha>_Abs_ufri unfolding rep_x_def rep_y_def
        by blast+
      with \<open>i \<noteq> rep_x\<close> show ?thesis
        unfolding rank_of_ufri_def by (auto simp: nth_list_update)
    qed
    note ufa_rank_ufa_union_if_ufa_rep_of_neq[OF \<open>rep_x \<noteq> rep_y\<close>[unfolded rep_eq_ufa_rep_of]]
    note [simp] = this[OF in_Field_ufa_\<alpha> i_in_Field]
    from i_in_Field i_is_ufa_rep \<open>i \<noteq> rep_x\<close> in_Field_ufa_\<alpha> show
      "rank_of_ufri ?ufri' i = ufa_rank (Abs_ufa (uf_of_ufri ?ufri')) i"
      unfolding rank_of_ufri'_eq uf_of_ufri'_eq_ufa_union
      unfolding rep_eq_ufa_rep_of r_rep_eq_ufa_rank
      using assms(1)[unfolded ufri_invar_def ufr_invar_def] by simp
  qed
  with \<open>ufa_invar (uf_of_ufri ?ufri')\<close> show "ufri_invar ?ufri'"
    unfolding ufri_invar_def by simp

  with assms(1) uf_of_ufri'_eq_ufa_union show "ufri_union (Abs_ufri ufri) x y = Abs_ufri ?ufri'"
    including ufa_ufr_transfer
    by (transfer, transfer) (metis Rep_ufa_inverse eq_uf_of_ufri)
qed
  
lifting_update ufri.lifting
lifting_forget ufri.lifting

end