theory Union_Find_Rank
  imports Union_Find
begin

definition "ufr_invar ufr \<equiv> (case ufr of (ufa, r) \<Rightarrow>
  (\<forall>i \<in> Field (ufa_\<alpha> ufa). ufa_rep_of ufa i = i \<longrightarrow> r i = ufa_rank ufa i))"

lemma ufr_invarI:
  assumes "\<And>i. \<lbrakk> i \<in> Field (ufa_\<alpha> ufa); ufa_rep_of ufa i = i \<rbrakk> \<Longrightarrow> r i = ufa_rank ufa i"
  shows "ufr_invar (ufa, r)"
  using assms unfolding ufr_invar_def by blast

typedef ufr = "{ufr. ufr_invar ufr}"
proof -
  have "ufr_invar (ufa_init 0, (\<lambda>x. 1))"
    unfolding ufr_invar_def ufa_invar_def
    by auto
  then show ?thesis
    by blast
qed

setup_lifting type_definition_ufr

lift_definition ufa_of_ufr :: "ufr \<Rightarrow> ufa" is fst
  unfolding ufr_invar_def .

lift_definition ufr_of_ufa :: "ufa \<Rightarrow> ufr" is
  "\<lambda>uf. (uf, ufa_rank uf)"
  unfolding ufr_invar_def by simp

lift_definition ufr_init :: "nat \<Rightarrow> ufr" is
  "\<lambda>n. (ufa_init n, (\<lambda>_. 1))"
proof -
  have "ufa_rank (ufa_init n) i = 1" if "i < n" for n i
    using that unfolding ufa_rank_def ufa_eq_class_def ufa_\<alpha>_ufa_init
    by (auto simp: Image_def)
  then show "ufr_invar (ufa_init n, \<lambda>_. 1)" for n
    unfolding ufr_invar_def by auto
qed

definition "ufr_parent_of ufr \<equiv> ufa_parent_of (ufa_of_ufr ufr)"

definition "ufr_rep_of ufr \<equiv> ufa_rep_of (ufa_of_ufr ufr)"

definition "ufr_\<alpha> ufr \<equiv> ufa_\<alpha> (ufa_of_ufr ufr)"

definition "ufr_rank ufr \<equiv> ufa_rank (ufa_of_ufr ufr)"

lift_definition ufr_union :: "ufr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufr" is
  "\<lambda>(ufa, r) x y.
    if x \<notin> Field (ufa_\<alpha> ufa) \<or> y \<notin> Field (ufa_\<alpha> ufa) then (ufa, r)
    else
      let
        rep_x = ufa_rep_of ufa x;
        rep_y = ufa_rep_of ufa y
      in
        if rep_x = rep_y then (ufa, r)
        else (ufa_union ufa x y, r(rep_y := r rep_y + r rep_x))"
proof -
  fix ufr x y
  assume "ufr_invar ufr"
  then show "?thesis ufr x y"
  proof(cases "x \<notin> Field (ufa_\<alpha> (fst ufr)) \<or> y \<notin> Field (ufa_\<alpha> (fst ufr))")
    case in_Field_ufa_\<alpha>: False
    with \<open>ufr_invar ufr\<close> show ?thesis
    proof(cases "ufa_rep_of (fst ufr) x = ufa_rep_of (fst ufr) y")
      case ufa_rep_of_neq: False
      note [simp] = ufa_rep_of_ufa_union ufa_rank_ufa_union_if_ufa_rep_of_neq
      from \<open>ufr_invar ufr\<close> in_Field_ufa_\<alpha> ufa_rep_of_neq show ?thesis
        unfolding ufr_invar_def
        by (auto simp: Let_def split: prod.splits)
    qed (use \<open>ufr_invar ufr\<close> in \<open>auto split: prod.splits\<close>)
  qed (auto split: prod.splits)
qed

definition "ufr_union_rank ufr x y \<equiv>
  let
    rep_x = ufr_rep_of ufr x;
    rep_y = ufr_rep_of ufr y
  in
    if ufr_rank ufr rep_x < ufr_rank ufr rep_y then ufr_union ufr x y
    else ufr_union ufr y x"

lift_definition ufr_compress :: "ufr \<Rightarrow> nat \<Rightarrow> ufr" is
  "\<lambda>(ufa, r) x. (ufa_compress ufa x, r)"
  unfolding ufr_invar_def
  by (auto split: prod.splits)

context includes lifting_syntax
begin

named_theorems ufa_ufr_transfer

definition "ufa_ufr_rel ufa ufr \<equiv> ufa = ufa_of_ufr ufr"

lemma left_unique_ufa_ufr_rel[ufa_ufr_transfer]:
  "left_unique ufa_ufr_rel"
  unfolding left_unique_def ufa_ufr_rel_def by blast

lemma bi_total_ufa_ufr_rel[ufa_ufr_transfer]:
  "bi_total ufa_ufr_rel"
  unfolding bi_total_def ufa_ufr_rel_def
  by (metis fst_conv ufa_of_ufr.rep_eq ufr_of_ufa.rep_eq)

lemma ufa_of_ufr_transfer:
  "(ufa_ufr_rel ===> (=)) id ufa_of_ufr"
  using ufa_ufr_rel_def by auto

lemma ufr_parent_of_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=) ===> (=)) ufa_parent_of ufr_parent_of"
  unfolding ufa_ufr_rel_def ufr_parent_of_def by blast

lemma ufr_rep_of_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=) ===> (=)) ufa_rep_of ufr_rep_of"
  unfolding ufa_ufr_rel_def ufr_rep_of_def by blast

lemma ufr_\<alpha>_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=)) ufa_\<alpha> ufr_\<alpha>"
  unfolding ufa_ufr_rel_def ufr_\<alpha>_def by blast

lemma ufr_rank_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=) ===> (=)) ufa_rank ufr_rank"
  unfolding ufa_ufr_rel_def ufr_rank_def by blast

lemma ufa_of_ufr_ufr_init:
  "ufa_of_ufr (ufr_init n) = ufa_init n"
  by transfer simp

lemma ufa_init_ufr_union_transfer[ufa_ufr_transfer]:
  "((=) ===> ufa_ufr_rel) ufa_init ufr_init"
  by (intro rel_funI) (auto simp: ufa_ufr_rel_def ufa_of_ufr_ufr_init)

lemma ufa_of_ufr_ufr_union:
  "ufa_of_ufr (ufr_union ufr x y) = ufa_union (ufa_of_ufr ufr) x y"
  by transfer (auto simp: Let_def)

lemma ufa_union_ufr_union_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=) ===> (=) ===> ufa_ufr_rel) ufa_union ufr_union"
  by (intro rel_funI) (auto simp: ufa_ufr_rel_def ufa_of_ufr_ufr_union case_prod_unfold Let_def)

lemma ufa_of_ufr_ufr_compress:
  "ufa_of_ufr (ufr_compress ufr x) = ufa_compress (ufa_of_ufr ufr) x"
  by transfer (simp split: prod.splits)

lemma ufa_compress_ufr_compress_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=) ===> ufa_ufr_rel) ufa_compress ufr_compress"
  unfolding ufa_ufr_rel_def
  by (intro rel_funI) (simp add: ufa_of_ufr_ufr_compress)

lemma ufa_of_ufr_ufr_union_rank:
  "ufa_of_ufr (ufr_union_rank ufr x y) = ufa_union_rank (ufa_of_ufr ufr) x y"
  unfolding ufr_union_rank_def ufr_rep_of_def ufr_rank_def
  by transfer (auto simp: ufa_union_rank_def Let_def)

lemma ufa_union_rank_ufr_union_rank_transfer[ufa_ufr_transfer]:
  "(ufa_ufr_rel ===> (=) ===> (=) ===> ufa_ufr_rel) ufa_union_rank ufr_union_rank"
  unfolding ufa_ufr_rel_def
  by (intro rel_funI) (simp add: ufa_of_ufr_ufr_union_rank)

end

lemma ufr_rep_of_induct[case_names "parametric" rep not_rep, consumes 1]:
  includes lifting_syntax
  notes [transfer_rule] = ufa_ufr_transfer
  assumes "i \<in> Field (ufr_\<alpha> uf)"
  assumes [transfer_rule]:
    "(ufa_ufr_rel ===> (=) ===> (=)) (\<lambda>ufa. P (ufr_of_ufa ufa)) P"
  assumes rep: "\<And>i. \<lbrakk> i \<in> Field (ufr_\<alpha> uf); ufr_parent_of uf i = i \<rbrakk> \<Longrightarrow> P uf i"
  assumes not_rep:
    "\<And>i. \<lbrakk> i \<in> Field (ufr_\<alpha> uf); ufr_parent_of uf i \<noteq> i; P uf (ufr_parent_of uf i) \<rbrakk>
    \<Longrightarrow> P uf i"
  shows "P uf i"
  using assms(1,3-)
  by (transfer fixing: P) (rule ufa_rep_of_induct)

lemma ufr_rep_of_eq_iff_in_ufr_\<alpha>:
  assumes "x \<in> Field (ufr_\<alpha> ufr)" "y \<in> Field (ufr_\<alpha> ufr)"
  shows "ufr_rep_of ufr x = ufr_rep_of ufr y \<longleftrightarrow> (x, y) \<in> ufr_\<alpha> ufr"
  using assms ufa_rep_of_eq_iff_in_ufa_\<alpha>
  unfolding ufr_\<alpha>_def ufr_rep_of_def by simp

lemma ufr_\<alpha>_ufr_init:
  "ufr_\<alpha> (ufr_init n) = {(x, x) |x. x < n}"
  using ufa_\<alpha>_ufa_init unfolding ufr_\<alpha>_def by transfer simp

lemma ufr_\<alpha>_ufr_union:
  "ufr_\<alpha> (ufr_union ufr x y) = per_union (ufr_\<alpha> ufr) x y"
proof -
  have "per_union (ufr_\<alpha> ufr) x y = ufr_\<alpha> ufr"
    if "x \<notin> Field (ufr_\<alpha> ufr) \<or> y \<notin> Field (ufr_\<alpha> ufr)"
    using that unfolding per_union_def Field_iff by blast
  moreover have "per_union (ufr_\<alpha> ufr) x y = ufr_\<alpha> ufr"
    if "x \<in> Field (ufr_\<alpha> ufr)" "y \<in> Field (ufr_\<alpha> ufr)"
       "ufr_rep_of ufr x = ufr_rep_of ufr y"
    using that per_union_cmp[OF part_equiv_ufa_\<alpha>]
    unfolding ufr_\<alpha>_def ufr_rep_of_def
    by transfer (simp add: ufa_\<alpha>I)
  ultimately show ?thesis
    unfolding ufr_\<alpha>_def ufr_rep_of_def
    by transfer (auto split: if_splits simp: Let_def)
qed

lemma ufr_\<alpha>_ufr_union_rank:
  "ufr_\<alpha> (ufr_union_rank ufr x y) = per_union (ufr_\<alpha> ufr) x y"
  unfolding ufr_union_rank_def using ufr_\<alpha>_ufr_union by simp

lemma ufr_\<alpha>_ufr_compress:
  "ufr_\<alpha> (ufr_compress ufr x) = ufr_\<alpha> ufr"
  unfolding ufr_\<alpha>_def by transfer force

lifting_update ufr.lifting
lifting_forget ufr.lifting

definition "eq_ufr ufr1 ufr2 \<equiv> ufa_of_ufr ufr1 = ufa_of_ufr ufr2 \<and>
  (\<forall>i \<in> Field (ufr_\<alpha> ufr1). ufr_rep_of ufr1 i = i \<longrightarrow> ufr_rank ufr1 i = ufr_rank ufr2 i)"

lemma refl_eq_ufr[simp, intro]: "eq_ufr ufr ufr"
  unfolding eq_ufr_def by simp

lemma reflp_eq_ufr: "reflp eq_ufr"
  by (intro reflpI) simp

lemma sym_eq_ufr: "eq_ufr ufr1 ufr2 \<Longrightarrow> eq_ufr ufr2 ufr1"
  unfolding eq_ufr_def ufr_rep_of_def ufr_\<alpha>_def including ufr.lifting
  by transfer auto

lemma trans_eq_ufr: "eq_ufr ufr1 ufr2 \<Longrightarrow> eq_ufr ufr2 ufr3 \<Longrightarrow> eq_ufr ufr1 ufr3"
  unfolding eq_ufr_def ufr_rep_of_def ufr_\<alpha>_def including ufr.lifting
  by transfer auto

lemma equivp_eq_ufr: "equivp eq_ufr"
  using sym_eq_ufr trans_eq_ufr
  by (intro equivpI reflpI sympI transpI) blast+

lemma eq_ufr_eq_transfer[ufa_ufr_transfer]:
  includes lifting_syntax
  shows "(ufa_ufr_rel ===> ufa_ufr_rel ===> (=)) (=) eq_ufr"
  unfolding eq_ufr_def
  apply(intro rel_funI)
  using ufa_ufr_rel_def ufr_rank_def by auto

lemma ufr_rep_of_eq_if_eq_ufr:
  notes [transfer_rule] = ufa_ufr_transfer ufa_of_ufr_transfer
  assumes "eq_ufr ufr1 ufr2"
  shows "ufr_rep_of ufr1 i = ufr_rep_of ufr2 i"
  using assms unfolding eq_ufr_def
  by transfer simp

lemma ufr_rank_eq_if_eq_ufr:
  notes [transfer_rule] = ufa_ufr_transfer ufa_of_ufr_transfer
  assumes "eq_ufr ufr1 ufr2"
  assumes "i \<in> Field (ufr_\<alpha> ufr1)"
  shows "ufr_rank ufr1 (ufr_rep_of ufr1 i) = ufr_rank ufr2 (ufr_rep_of ufr2 i)"
  using assms unfolding eq_ufr_def
  by transfer simp

lemma ufr_\<alpha>_eq_if_eq_ufr[simp]:
  notes [transfer_rule] = ufa_ufr_transfer ufa_of_ufr_transfer
  assumes "eq_ufr ufr1 ufr2"
  shows "ufr_\<alpha> ufr1 = ufr_\<alpha> ufr2"
  using assms unfolding eq_ufr_def
  by transfer simp

lemma ufr_rank_Abs_ufr:
  assumes "ufr_invar ufr"
  assumes "x \<in> Field (ufr_\<alpha> (Abs_ufr ufr))"
  assumes "ufr_rep_of (Abs_ufr ufr) x = x"
  shows "ufr_rank (Abs_ufr ufr) x = snd ufr x"
proof -
  from assms have [simp]:
    "ufa_of_ufr (Abs_ufr ufr) = fst ufr"
    using Abs_ufr_inverse ufa_of_ufr.rep_eq by simp
  from assms show ?thesis
    unfolding ufr_invar_def ufr_rank_def ufr_rep_of_def ufr_\<alpha>_def
    by (transfer fixing: ufr) auto
qed

lemma ufr_union_Abs_ufr:
  assumes "ufr_invar ufr"
  assumes "x \<in> Field (ufr_\<alpha> (Abs_ufr ufr))" "y \<in> Field (ufr_\<alpha> (Abs_ufr ufr))"
  assumes "ufr_rep_of (Abs_ufr ufr) x \<noteq> ufr_rep_of (Abs_ufr ufr) y"
  shows "ufr_union (Abs_ufr ufr) x y =
    Abs_ufr (ufa_union (fst ufr) x y,
      (snd ufr)(ufr_rep_of (Abs_ufr ufr) y := ufr_rank (Abs_ufr ufr) x + ufr_rank (Abs_ufr ufr) y))"
proof -
  from assms have [simp]:
    "ufa_of_ufr (Abs_ufr ufr) = fst ufr"
    using Abs_ufr_inverse ufa_of_ufr.rep_eq by simp
  from assms show ?thesis
    unfolding ufr_\<alpha>_def ufr_rep_of_def ufr_rank_def
    by (subst ufr_union.abs_eq)
      (auto simp: eq_onp_same_args ufr_invar_def add.commute Let_def case_prod_unfold)
qed


bundle ufa_ufr_transfer
begin

declare ufa_ufr_transfer[transfer_rule]

end

end