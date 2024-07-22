theory Explain_Imp
  imports
    Explain_Correctness
    Union_Find_Rank_Int_Imp
    Dynamic_Array
begin

record ufe_ds_imp =
  uf_ds :: ufri_imp
  au_ds :: "nat option Heap.array"
  unions :: "(nat \<times> nat) dyn_array"

definition "is_au_ds \<equiv> \<lambda>(au, n) au_imp. \<exists>\<^sub>Aau_list.
  au_imp \<mapsto>\<^sub>a au_list *
  \<up>(n = length au_list \<and> au = (\<lambda>k. if k < length au_list then au_list ! k else None))"

definition is_ufe_ds :: "ufe_ds \<times> nat \<Rightarrow> ufe_ds_imp \<Rightarrow> assn" where
  "is_ufe_ds \<equiv> \<lambda>(ufe_ds, n) ufe_ds_impl.
    is_ufri (ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))) (uf_ds ufe_ds_impl) *
    \<up>(\<forall>i \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds)). i < n) *
    is_au_ds (ufe_ds.au_ds ufe_ds, n) (au_ds ufe_ds_impl) *
    is_dyn_array (ufe_ds.unions ufe_ds) (unions ufe_ds_impl)"

lemma is_au_ds_upd_rule[sep_heap_rules]:
  assumes "i < n"
  shows "<is_au_ds (au, n) au_imp> Array.upd i x au_imp <is_au_ds (au(i := x), n)>"
  using assms
  unfolding is_au_ds_def by sep_auto

lemma is_au_ds_nth_rule[sep_heap_rules]:
  assumes "i < n"
  shows "<is_au_ds (au, n) au_imp> Array.nth au_imp i <\<lambda>r. is_au_ds (au, n) au_imp * \<up>(r = au i)>"
  using assms
  unfolding is_au_ds_def by sep_auto

lemma nth_au_ds_rule[sep_heap_rules]:
  assumes "i \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      Array.nth (au_ds ufe_ds_imp) i
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufe_ds.au_ds ufe_ds i)>"
  using assms unfolding is_ufe_ds_def by sep_auto

lemma nth_unions_rule[sep_heap_rules]:
  assumes "i < length (ufe_ds.unions ufe_ds)"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      Dynamic_Array.nth (unions ufe_ds_imp) i
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufe_ds.unions ufe_ds ! i)>"
  using assms unfolding is_ufe_ds_def by sep_auto

definition "ufe_imp_init n \<equiv> do {
  uf \<leftarrow> ufri_imp_init n;
  au \<leftarrow> Array.new n None;
  us \<leftarrow> Dynamic_Array.new (0, 0);
  return \<lparr> uf_ds = uf, au_ds = au, unions = us \<rparr>
}"

lemma new_is_au_ds_rule[sep_heap_rules]:
  "<emp> Array.new n None <is_au_ds (Map.empty, n)>"
  unfolding is_au_ds_def by sep_auto

lemma ufe_imp_init_rule[sep_heap_rules]:
  "<emp> ufe_imp_init n <is_ufe_ds (ufe_init n, n)>"
proof -
  have "ufri_of_ufr (ufr_of_ufa (ufa_init n)) = ufri_init n"
    including ufri.lifting apply transfer
    including ufa_ufr_transfer apply transfer
    by simp
  then show ?thesis
    unfolding ufe_imp_init_def is_ufe_ds_def
    by sep_auto
qed

definition "ufe_imp_union_raw ufe_ds_imp x y rep_x rep_y rank \<equiv> do {
  len \<leftarrow> Dynamic_Array.length (unions ufe_ds_imp);
  uf' \<leftarrow> ufri_imp_union_raw (uf_ds ufe_ds_imp) rep_x rep_y rank;
  au' \<leftarrow> Array.upd rep_x (Some len) (au_ds ufe_ds_imp);
  us' \<leftarrow> Dynamic_Array.push (unions ufe_ds_imp) (0, 0) (x, y);
  return \<lparr> uf_ds = uf', au_ds = au', unions = us' \<rparr>
}"


lemma ufr_of_ufa_ufri_of_ufr_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(ufa_ufr_rel ===> pcr_ufri) ufr_of_ufa ufri_of_ufr"
  using ufa_ufr_rel_def ufr_ufri_rel_def ufri.pcr_cr_eq by auto

lemma ufe_imp_union_raw_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  defines "rep_x \<equiv> ufe_rep_of ufe_ds x"
  defines "rep_y \<equiv> ufe_rep_of ufe_ds y"
  defines "rank_rep_x \<equiv> ufa_rank (ufe_ds.uf_ds ufe_ds) rep_x"
  defines "rank_rep_y \<equiv> ufa_rank (ufe_ds.uf_ds ufe_ds) rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufe_imp_union_raw ufe_ds_imp x y rep_x rep_y (rank_rep_x + rank_rep_y)
    <is_ufe_ds (ufe_union ufe_ds x y, n)>\<^sub>t"
proof -
  include ufri.lifting ufa_ufr_transfer
  define ufri where "ufri \<equiv> ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1,2) have "x \<in> Field (ufri_\<alpha> ufri)" "y \<in> Field (ufri_\<alpha> ufri)"
    unfolding ufri_def by (transfer, transfer, simp)+
  moreover have "rep_x = ufri_rep_of ufri x" "rep_y = ufri_rep_of ufri y"
    unfolding ufri_def rep_x_def rep_y_def
    by (transfer, transfer, simp)+
  moreover have "rank_rep_x = ufri_rank ufri rep_x" "rank_rep_y = ufri_rank ufri rep_y"
    unfolding ufri_def rank_rep_x_def rank_rep_y_def rep_x_def rep_y_def
    by (transfer, transfer, simp)+
  moreover have
    "ufri_of_ufr (ufr_of_ufa (ufa_union (ufe_ds.uf_ds ufe_ds) x y)) = ufri_union ufri x y"
    unfolding ufri_def by (transfer, transfer, simp)
  moreover have "ufe_rep_of ufe_ds x = ufri_rep_of ufri x"
    unfolding ufri_def by (transfer, transfer, simp)
  ultimately show ?thesis
    using \<open>rep_x \<noteq> rep_y\<close> ufa_rep_of_in_Field_ufa_\<alpha>I[OF assms(1)]
    unfolding ufe_imp_union_raw_def is_ufe_ds_def
    by (sep_auto simp: ufri_def[symmetric] fun_upd_def)
qed

definition "ufe_imp_union_rank ufe_ds_imp x y \<equiv> do {
  rep_x \<leftarrow> ufri_imp_rep_of (uf_ds ufe_ds_imp) x;
  rep_y \<leftarrow> ufri_imp_rep_of (uf_ds ufe_ds_imp) y;
  if rep_x = rep_y then return ufe_ds_imp
  else do {
    rank_rep_x \<leftarrow> ufri_imp_rank (uf_ds ufe_ds_imp) rep_x;
    rank_rep_y \<leftarrow> ufri_imp_rank (uf_ds ufe_ds_imp) rep_y;
    if rank_rep_x < rank_rep_y then
      ufe_imp_union_raw ufe_ds_imp x y rep_x rep_y (rank_rep_x + rank_rep_y)
    else
      ufe_imp_union_raw ufe_ds_imp y x rep_y rep_x (rank_rep_y + rank_rep_x)
  }
}"

lemma ufri_imp_rep_of_is_ufe_ds_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufri_imp_rep_of (uf_ds ufe_ds_imp) x
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufe_rep_of ufe_ds x)>"
proof -
  include ufri.lifting ufa_ufr_transfer
  define ufri where "ufri \<equiv> ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1) have "x \<in> Field (ufri_\<alpha> ufri)"
    unfolding ufri_def by (transfer, transfer, simp)
  moreover have "ufri_rep_of ufri x = ufe_rep_of ufe_ds x"
    unfolding ufri_def by (transfer, transfer, simp) 
  ultimately show ?thesis
    unfolding is_ufe_ds_def ufri_def by sep_auto
qed

lemma ufri_imp_rank_is_ufe_ds_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = x"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufri_imp_rank (uf_ds ufe_ds_imp) x
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufa_rank (ufe_ds.uf_ds ufe_ds) x)>"
proof -
  include ufri.lifting ufa_ufr_transfer
  define ufri where "ufri \<equiv> ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1) have "x \<in> Field (ufri_\<alpha> ufri)"
    unfolding ufri_def by (transfer, transfer, simp)
  moreover from assms(2) have "ufri_rep_of ufri x = x"
    unfolding ufri_def by (transfer, transfer, simp)
  moreover have "ufri_rank ufri x = ufa_rank (ufe_ds.uf_ds ufe_ds) x"
    unfolding ufri_def by (transfer, transfer, simp) 
  ultimately show ?thesis
    unfolding is_ufe_ds_def ufri_def by sep_auto
qed

lemma ufe_imp_union_rank_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufe_imp_union_rank ufe_ds_imp x y
    <is_ufe_ds (ufe_union_rank ufe_ds x y, n)>\<^sub>t"
proof -
  include ufri.lifting ufa_ufr_transfer
  define ufri where "ufri \<equiv> ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1,2) have "x \<in> Field (ufri_\<alpha> ufri)" "y \<in> Field (ufri_\<alpha> ufri)"
    unfolding ufri_def by (transfer, transfer, simp)+
  moreover from assms(3) have "ufri_rep_of ufri x \<noteq> ufri_rep_of ufri y"
    unfolding ufri_def by (transfer, transfer, simp)+
  ultimately show ?thesis
    using assms unfolding ufe_imp_union_rank_def ufe_union_rank_def ufri_def
    by (sep_auto simp del: ufa_rank_ufa_rep_of)
qed

partial_function (heap) ufri_imp_awalk_verts_from_rep_acc where
  [code]: "ufri_imp_awalk_verts_from_rep_acc ufri x vs = do {
    px \<leftarrow> ufri_imp_parent_of ufri x;
    if px = x then return (x # vs) 
    else ufri_imp_awalk_verts_from_rep_acc ufri px (x # vs)
  }"

lemma ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri:
  "ufa_of_ufri ufri = ufa_of_ufr (ufr_of_ufri ufri)"
  by (simp add: Rep_ufri_inverse ufa_of_ufr.rep_eq ufr_of_ufri.rep_eq)

lemma ufri_imp_awalk_verts_from_rep_acc_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufri_\<alpha> ufri)"
  shows
    "<is_ufri ufri ufri_imp>
      ufri_imp_awalk_verts_from_rep_acc ufri_imp x vs
    <\<lambda>r. is_ufri ufri ufri_imp * \<up>(r = awalk_verts_from_rep (ufa_of_ufri ufri) x @ vs)>"
  using assms
proof(induction arbitrary: vs rule: ufri_rep_of_induct)
  case "parametric"
  then show ?case
    unfolding ufa_ufr_rel_def rel_fun_def by simp
next
  case (rep i)
  moreover from this have "ufa_parent_of (ufa_of_ufri ufri) i = i"
    unfolding ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri
    using ufr_parent_of_def ufri_parent_of.rep_eq by force
  moreover from this have "awalk_verts_from_rep_dom (ufa_of_ufri ufri) i"
    using awalk_verts_from_rep.domintros by force
  ultimately show ?case
    by (subst ufri_imp_awalk_verts_from_rep_acc.simps)
      (sep_auto simp: awalk_verts_from_rep.psimps)
next
  case (not_rep i)
  moreover from this have "ufa_parent_of (ufa_of_ufri ufri) i = ufri_parent_of ufri i"
    unfolding ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri
    using ufr_parent_of_def ufri_parent_of.rep_eq by force
  moreover from not_rep.hyps have "awalk_verts_from_rep_dom (ufa_of_ufri ufri) i"
    unfolding ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri
    using awalk_verts_from_rep.domintros
    by (simp add: ufr_\<alpha>_def ufri_\<alpha>.rep_eq)
  ultimately show ?case
    by (subst ufri_imp_awalk_verts_from_rep_acc.simps)
      (sep_auto simp: awalk_verts_from_rep.psimps)
qed

definition "ufri_imp_awalk_verts_from_rep ufri x \<equiv> ufri_imp_awalk_verts_from_rep_acc ufri x []"

lemma ufri_imp_awalk_verts_from_rep_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufri_\<alpha> ufri)"
  shows
    "<is_ufri ufri ufri_imp>
      ufri_imp_awalk_verts_from_rep ufri_imp x
    <\<lambda>r. is_ufri ufri ufri_imp * \<up>(r = awalk_verts_from_rep (ufa_of_ufri ufri) x)>"
  using assms ufri_imp_awalk_verts_from_rep_acc_rule[where ?vs="[]"]
  unfolding ufri_imp_awalk_verts_from_rep_def by simp

definition "ufri_imp_lca ufri x y \<equiv> do {
    vsx \<leftarrow> ufri_imp_awalk_verts_from_rep ufri x;
    vsy \<leftarrow> ufri_imp_awalk_verts_from_rep ufri y;
    return (last (longest_common_prefix vsx vsy))
  }"

lemma is_ufri_ufri_imp_lca_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufri_\<alpha> ufri)" "y \<in> Field (ufri_\<alpha> ufri)"
  shows
    "<is_ufri ufri ufri_imp> ufri_imp_lca ufri_imp x y 
    <\<lambda>r. is_ufri ufri ufri_imp * \<up>(r = ufa_lca (ufa_of_ufri ufri) x y)>"
  using assms unfolding ufri_imp_lca_def
  by (sep_auto simp: ufa_lca_def)

lemma ufri_imp_lca_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp> ufri_imp_lca (uf_ds ufe_ds_imp) x y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufa_lca (ufe_ds.uf_ds ufe_ds) x y)>"
proof -
  include ufri.lifting ufa_ufr_transfer
  define ufri where "ufri \<equiv> ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1,2) have "x \<in> Field (ufri_\<alpha> ufri)" "y \<in> Field (ufri_\<alpha> ufri)"
    unfolding ufri_def by (transfer, transfer, simp)+
  moreover have "ufa_lca (ufa_of_ufri ufri) x y = ufa_lca (ufe_ds.uf_ds ufe_ds) x y"
    unfolding ufri_def ufa_of_ufri_eq_ufa_of_ufr_ufr_of_ufri
    using ufa_of_ufr.rep_eq ufr_of_ufa.rep_eq
    by (metis Quotient_rep_abs Quotient_ufri_ufr eq_ufr_def fst_eqD)
  ultimately show ?thesis
    using assms
    unfolding is_ufe_ds_def ufri_def by sep_auto
qed

partial_function (heap) find_newest_on_walk_acc_imp where
  [code]: "find_newest_on_walk_acc_imp ufe_ds_imp y x acc =
    (if y = x then return acc
    else do {
      au_x \<leftarrow> Array.nth (au_ds ufe_ds_imp) x;
      px \<leftarrow> ufri_imp_parent_of (uf_ds ufe_ds_imp) x;
      find_newest_on_walk_acc_imp ufe_ds_imp y px (combine_options max au_x acc)
    })"

lemma (in ufe_tree) find_newest_on_walk_acc_imp_rule[sep_heap_rules]:
  assumes "awalk z p y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      find_newest_on_walk_acc_imp ufe_ds_imp z y acc
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp *
      \<up>(r = combine_options max acc (find_newest_on_walk ufe_ds z y))>"
proof -
  note find_newest_on_walk_dom[OF assms]
  moreover from assms have "y \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
    by blast
  ultimately show ?thesis
  proof(induction arbitrary: p acc rule: find_newest_on_walk.pinduct)
    case (1 z y)

    moreover from 1 have "y \<in> Field (ufri_\<alpha> (ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))))"
      including ufri.lifting ufa_ufr_transfer
      by (transfer, transfer) simp
    moreover from this have
      "ufri_parent_of (ufri_of_ufr (ufr_of_ufa (ufe_ds.uf_ds ufe_ds))) y =
        ufe_parent_of ufe_ds y"
      including ufri.lifting ufa_ufr_transfer
      by (transfer, transfer) simp
    ultimately have [sep_heap_rules]:
      "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
        ufri_imp_parent_of (ufe_ds_imp.uf_ds ufe_ds_imp) y
      <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufa_parent_of (ufe_ds.uf_ds ufe_ds) y)>"
      unfolding is_ufe_ds_def by sep_auto

    note [sep_heap_rules] = "1.IH"
    from "1.prems" "1.hyps" show ?case
      by (subst find_newest_on_walk_acc_imp.simps)
        (sep_auto simp: find_newest_on_walk.psimps combine_options_assoc combine_options_commute)
  qed
qed

definition find_newest_on_walk_imp :: "ufe_ds_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "find_newest_on_walk_imp ufe_ds_imp y x \<equiv> find_newest_on_walk_acc_imp ufe_ds_imp y x None"

lemma (in ufe_tree) find_newest_on_walk_imp_rule[sep_heap_rules]:
  assumes "awalk z p y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      find_newest_on_walk_imp ufe_ds_imp z y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = find_newest_on_walk ufe_ds z y)>"
  using assms unfolding find_newest_on_walk_imp_def
  by sep_auto

partial_function (heap) explain_imp :: "ufe_ds_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf Heap" where
  "explain_imp ufe_ds_imp x y =
    (if x = y then return (ReflP x)
    else do {
      lca \<leftarrow> ufri_imp_lca (uf_ds ufe_ds_imp) x y;
      newest_x \<leftarrow> find_newest_on_walk_imp ufe_ds_imp lca x;
      newest_y \<leftarrow> find_newest_on_walk_imp ufe_ds_imp lca y;
      if newest_x \<ge> newest_y then do {
        (ax, bx) \<leftarrow> Dynamic_Array.nth (unions ufe_ds_imp) (the newest_x);
        pxax \<leftarrow> explain_imp ufe_ds_imp x ax;
        pbxy \<leftarrow> explain_imp ufe_ds_imp bx y;
        return (TransP (TransP pxax (AssmP (the newest_x))) pbxy)
      } else do {
        (ay, by) \<leftarrow> Dynamic_Array.nth (unions ufe_ds_imp) (the newest_y);
        pxby \<leftarrow> explain_imp ufe_ds_imp x by;
        payy \<leftarrow> explain_imp ufe_ds_imp ay y;
        return (TransP (TransP pxby (SymP (AssmP (the newest_y)))) payy)
      }
    })"

lemma (in ufe_invars) explain_imp_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (ufe_ds.uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      explain_imp ufe_ds_imp x y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = explain ufe_init (ufe_ds.unions ufe_ds) x y)>"
  using assms
proof(induction rule: explain_code_induct)
  case (eq x)
  then show ?case
    by (subst explain_imp.simps) sep_auto
next
  case (newest_x x y ax bx)
  then interpret ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales
  from newest_x have
    "find_newest_on_walk ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) y \<le>
      find_newest_on_walk ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) x"
    by order
  moreover from newest_x obtain px py where
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) px x"
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) py y"
    using lca_ufa_lca lca_reachableD reachable_awalk
    by (metis in_verts_if_rep_of_eq)
  moreover from this newest_x have
    "the (find_newest_on_walk ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) x)
      < length (ufe_ds.unions ufe_ds)"
    using find_newest_on_walk_if_eq newest_on_walk_find_newest_on_walk newest_on_walk_lt_length_unions
    by (metis less_option_None)
  ultimately show ?case
    using newest_x.prems newest_x.hyps
    apply(subst explain_imp.simps)
    apply(vcg)
     apply(rule newest_x.IH(1))
    apply(vcg)
     apply(rule newest_x.IH(2))
    apply(sep_auto simp: explain_code)
    done
next
  case (newest_y x y ay "by")
  then interpret ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales
  from newest_y have
    "\<not> find_newest_on_walk ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) y \<le>
      find_newest_on_walk ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) x"
    by order
  moreover from newest_y obtain px py where
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) px x"
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) py y"
    using lca_ufa_lca lca_reachableD reachable_awalk
    by (metis in_verts_if_rep_of_eq)
  moreover from this newest_y have
    "the (find_newest_on_walk ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) y)
      < length (ufe_ds.unions ufe_ds)"
    using find_newest_on_walk_if_eq newest_on_walk_find_newest_on_walk newest_on_walk_lt_length_unions
    by (metis less_option_None)
  ultimately show ?case
    using newest_y.prems newest_y.hyps
    apply(subst explain_imp.simps)
    apply(vcg)
     apply(rule newest_y.IH(1))
    apply(vcg)
     apply(rule newest_y.IH(2))
    apply(sep_auto simp: explain_code)
    done
qed

end
