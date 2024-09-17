theory Explain_Imp
  imports
    Explain_Efficient_Correctness
    "Union_Find.Union_Find_Size_Int_Imp"
    Dynamic_Array
begin

record ufe_ds_imp =
  uf_ds :: ufsi_imp
  au_ds :: "nat option Heap.array"
  unions :: "(nat \<times> nat) dyn_array"

definition "is_au_ds \<equiv> \<lambda>(au, n) au_imp. \<exists>\<^sub>Aau_list.
  au_imp \<mapsto>\<^sub>a au_list *
  \<up>(n = length au_list \<and> au = (\<lambda>k. if k < length au_list then au_list ! k else None))"

definition is_ufe_ds :: "ufe_ds \<times> nat \<Rightarrow> ufe_ds_imp \<Rightarrow> assn" where
  "is_ufe_ds \<equiv> \<lambda>(ufe_ds, n) ufe_ds_imp.
    is_ufsi (ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))) (uf_ds ufe_ds_imp) *
    \<up>(Field (ufe_\<alpha> ufe_ds) = {0..<n}) *
    is_au_ds (ufe_ds.au_ds ufe_ds, n) (au_ds ufe_ds_imp) *
    is_dyn_array (ufe_ds.unions ufe_ds) (unions ufe_ds_imp)"

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
  assumes "i \<in> Field (ufe_\<alpha> ufe_ds)"
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
  uf \<leftarrow> ufsi_imp_init n;
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
  have "ufsi_of_ufs (ufs_of_ufa (ufa_init n)) = ufsi_init n"
    including ufsi.lifting apply transfer
    including ufa_ufs_transfer apply transfer
    by simp
  then show ?thesis
    unfolding ufe_imp_init_def is_ufe_ds_def
    by sep_auto
qed

definition "ufe_imp_union_raw ufe_ds_imp x y rep_x rep_y sz \<equiv> do {
  len \<leftarrow> Dynamic_Array.length (unions ufe_ds_imp);
  uf' \<leftarrow> ufsi_imp_union_raw (uf_ds ufe_ds_imp) rep_x rep_y sz;
  au' \<leftarrow> Array.upd rep_x (Some len) (au_ds ufe_ds_imp);
  us' \<leftarrow> Dynamic_Array.push (unions ufe_ds_imp) (0, 0) (x, y);
  return \<lparr> uf_ds = uf', au_ds = au', unions = us' \<rparr>
}"

lemma ufe_imp_union_raw_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  defines "rep_x \<equiv> ufe_rep_of ufe_ds x"
  defines "rep_y \<equiv> ufe_rep_of ufe_ds y"
  defines "sz_rep_x \<equiv> ufa_size (ufe_ds.uf_ds ufe_ds) rep_x"
  defines "sz_rep_y \<equiv> ufa_size (ufe_ds.uf_ds ufe_ds) rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufe_imp_union_raw ufe_ds_imp x y rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufe_ds (ufe_union ufe_ds x y, n)>\<^sub>t"
proof -
  include ufsi.lifting ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1,2) have "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)+
  moreover have "rep_x = ufsi_rep_of ufsi x" "rep_y = ufsi_rep_of ufsi y"
    unfolding ufsi_def rep_x_def rep_y_def
    by (transfer, transfer, simp)+
  moreover have "sz_rep_x = ufsi_size ufsi rep_x" "sz_rep_y = ufsi_size ufsi rep_y"
    unfolding ufsi_def sz_rep_x_def sz_rep_y_def rep_x_def rep_y_def
    by (transfer, transfer, simp)+
  moreover have
    "ufsi_of_ufs (ufs_of_ufa (ufa_union (ufe_ds.uf_ds ufe_ds) x y)) = ufsi_union ufsi x y"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "ufe_rep_of ufe_ds x = ufsi_rep_of ufsi x"
    unfolding ufsi_def by (transfer, transfer, simp)
  ultimately show ?thesis
    using \<open>rep_x \<noteq> rep_y\<close> ufa_rep_of_in_Field_ufa_\<alpha>I[OF assms(1)]
    unfolding ufe_imp_union_raw_def is_ufe_ds_def
    by (sep_auto simp: ufsi_def[symmetric] fun_upd_def)
qed

definition "ufe_imp_union_size ufe_ds_imp x y \<equiv> do {
  rep_x \<leftarrow> ufsi_imp_rep_of (uf_ds ufe_ds_imp) x;
  rep_y \<leftarrow> ufsi_imp_rep_of (uf_ds ufe_ds_imp) y;
  if rep_x = rep_y then return ufe_ds_imp
  else do {
    sz_rep_x \<leftarrow> ufsi_imp_size (uf_ds ufe_ds_imp) rep_x;
    sz_rep_y \<leftarrow> ufsi_imp_size (uf_ds ufe_ds_imp) rep_y;
    if sz_rep_x < sz_rep_y then
      ufe_imp_union_raw ufe_ds_imp x y rep_x rep_y (sz_rep_x + sz_rep_y)
    else
      ufe_imp_union_raw ufe_ds_imp y x rep_y rep_x (sz_rep_y + sz_rep_x)
  }
}"

lemma ufsi_imp_rep_of_is_ufe_ds_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufsi_imp_rep_of (uf_ds ufe_ds_imp) x
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufe_rep_of ufe_ds x)>"
proof -
  include ufsi.lifting ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1) have "x \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "ufsi_rep_of ufsi x = ufe_rep_of ufe_ds x"
    unfolding ufsi_def by (transfer, transfer, simp) 
  ultimately show ?thesis
    unfolding is_ufe_ds_def ufsi_def by sep_auto
qed

lemma ufsi_imp_size_is_ufe_ds_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = x"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufsi_imp_size (uf_ds ufe_ds_imp) x
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufa_size (ufe_ds.uf_ds ufe_ds) x)>"
proof -
  include ufsi.lifting ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1) have "x \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover from assms(2) have "ufsi_rep_of ufsi x = x"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "ufsi_size ufsi x = ufa_size (ufe_ds.uf_ds ufe_ds) x"
    unfolding ufsi_def by (transfer, transfer, simp) 
  ultimately show ?thesis
    unfolding is_ufe_ds_def ufsi_def by sep_auto
qed

lemma ufe_imp_union_size_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      ufe_imp_union_size ufe_ds_imp x y
    <is_ufe_ds (ufe_union_size ufe_ds x y, n)>\<^sub>t"
proof -
  include ufsi.lifting ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1,2) have "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)+
  moreover from assms(3) have "ufsi_rep_of ufsi x \<noteq> ufsi_rep_of ufsi y"
    unfolding ufsi_def by (transfer, transfer, simp)+
  ultimately show ?thesis
    using assms unfolding ufe_imp_union_size_def ufe_union_size_def ufsi_def
    by (sep_auto simp del: ufa_size_ufa_rep_of)
qed

partial_function (heap) ufsi_imp_awalk_verts_from_rep_acc where
  [code]: "ufsi_imp_awalk_verts_from_rep_acc ufsi x vs = do {
    px \<leftarrow> ufsi_imp_parent_of ufsi x;
    if px = x then return (x # vs) 
    else ufsi_imp_awalk_verts_from_rep_acc ufsi px (x # vs)
  }"

lemma ufsi_imp_awalk_verts_from_rep_acc_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_awalk_verts_from_rep_acc ufsi_imp x vs
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = awalk_verts_from_rep (ufa_of_ufsi ufsi) x @ vs)>"
  using assms
proof(induction arbitrary: vs rule: ufsi_rep_of_induct)
  case "parametric"
  then show ?case
    unfolding ufa_ufs_rel_def rel_fun_def
    by simp
next
  case (rep i)
  moreover from this have "ufa_parent_of (ufa_of_ufsi ufsi) i = i"
    including ufa_ufs_transfer ufsi.lifting
    by transfer (simp add: ufs_parent_of_def)
  moreover from this have "awalk_verts_from_rep_dom (ufa_of_ufsi ufsi) i"
    using awalk_verts_from_rep.domintros by force
  ultimately show ?case
    by (subst ufsi_imp_awalk_verts_from_rep_acc.simps)
      (sep_auto simp: awalk_verts_from_rep.psimps)
next
  case (not_rep i)
  moreover from this have "ufa_parent_of (ufa_of_ufsi ufsi) i = ufsi_parent_of ufsi i"
    unfolding ufa_of_ufsi_eq_ufa_of_ufs_ufs_of_ufsi
    using ufs_parent_of_def ufsi_parent_of.rep_eq by force
  moreover from not_rep.hyps have "awalk_verts_from_rep_dom (ufa_of_ufsi ufsi) i"
    unfolding ufa_of_ufsi_eq_ufa_of_ufs_ufs_of_ufsi
    using awalk_verts_from_rep.domintros
    by (simp add: ufs_\<alpha>_def ufsi_\<alpha>.rep_eq)
  ultimately show ?case
    by (subst ufsi_imp_awalk_verts_from_rep_acc.simps)
      (sep_auto simp: awalk_verts_from_rep.psimps)
qed

definition "ufsi_imp_awalk_verts_from_rep ufsi x \<equiv> ufsi_imp_awalk_verts_from_rep_acc ufsi x []"

lemma ufsi_imp_awalk_verts_from_rep_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp>
      ufsi_imp_awalk_verts_from_rep ufsi_imp x
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = awalk_verts_from_rep (ufa_of_ufsi ufsi) x)>"
  using assms ufsi_imp_awalk_verts_from_rep_acc_rule[where ?vs="[]"]
  unfolding ufsi_imp_awalk_verts_from_rep_def by simp

definition "ufsi_imp_lca ufsi x y \<equiv> do {
    vsx \<leftarrow> ufsi_imp_awalk_verts_from_rep ufsi x;
    vsy \<leftarrow> ufsi_imp_awalk_verts_from_rep ufsi y;
    return (last (longest_common_prefix vsx vsy))
  }"

lemma is_ufsi_ufsi_imp_lca_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
  shows
    "<is_ufsi ufsi ufsi_imp> ufsi_imp_lca ufsi_imp x y 
    <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(r = ufa_lca (ufa_of_ufsi ufsi) x y)>"
  using assms unfolding ufsi_imp_lca_def
  by (sep_auto simp: ufa_lca_def)

lemma ufsi_imp_lca_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp> ufsi_imp_lca (uf_ds ufe_ds_imp) x y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufa_lca (ufe_ds.uf_ds ufe_ds) x y)>"
proof -
  include ufsi.lifting ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))"
  from assms(1,2) have "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)+
  moreover have "ufa_lca (ufa_of_ufsi ufsi) x y = ufa_lca (ufe_ds.uf_ds ufe_ds) x y"
    unfolding ufsi_def
    by transfer simp
  ultimately show ?thesis
    using assms
    unfolding is_ufe_ds_def ufsi_def by sep_auto
qed

partial_function (heap) find_newest_on_path_acc_imp where
  [code]: "find_newest_on_path_acc_imp ufe_ds_imp y x acc =
    (if y = x then return acc
    else do {
      au_x \<leftarrow> Array.nth (au_ds ufe_ds_imp) x;
      px \<leftarrow> ufsi_imp_parent_of (uf_ds ufe_ds_imp) x;
      find_newest_on_path_acc_imp ufe_ds_imp y px (max au_x acc)
    })"

lemma (in ufe_tree) find_newest_on_path_acc_imp_rule[sep_heap_rules]:
  assumes "awalk z p y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      find_newest_on_path_acc_imp ufe_ds_imp z y acc
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp *
      \<up>(r = max acc (find_newest_on_path ufe_ds z y))>"
proof -
  note find_newest_on_path_dom[OF assms]
  moreover from assms have "y \<in> Field (ufe_\<alpha> ufe_ds)"
    by blast
  ultimately show ?thesis
  proof(induction arbitrary: p acc rule: find_newest_on_path.pinduct)
    case (1 z y)

    moreover from 1 have "y \<in> Field (ufsi_\<alpha> (ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))))"
      including ufsi.lifting ufa_ufs_transfer
      by (transfer, transfer) simp
    moreover from this have
      "ufsi_parent_of (ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))) y =
        ufe_parent_of ufe_ds y"
      including ufsi.lifting ufa_ufs_transfer
      by (transfer, transfer) simp
    ultimately have [sep_heap_rules]:
      "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
        ufsi_imp_parent_of (ufe_ds_imp.uf_ds ufe_ds_imp) y
      <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = ufa_parent_of (ufe_ds.uf_ds ufe_ds) y)>"
      unfolding is_ufe_ds_def by sep_auto

    note [sep_heap_rules] = "1.IH"
    from "1.prems" "1.hyps" show ?case
      apply (subst find_newest_on_path_acc_imp.simps)
      by (sep_auto simp: find_newest_on_path.psimps max_def less_eq_option_None_is_None)
  qed
qed

definition find_newest_on_path_imp :: "ufe_ds_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "find_newest_on_path_imp ufe_ds_imp y x \<equiv> find_newest_on_path_acc_imp ufe_ds_imp y x None"

lemma (in ufe_tree) find_newest_on_path_imp_rule[sep_heap_rules]:
  assumes "awalk z p y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      find_newest_on_path_imp ufe_ds_imp z y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(r = find_newest_on_path ufe_ds z y)>"
  using assms unfolding find_newest_on_path_imp_def
  by sep_auto

partial_function (heap) explain_imp :: "ufe_ds_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf Heap" where
  "explain_imp ufe_ds_imp x y =
    (if x = y then return (ReflP x)
    else do {
      lca \<leftarrow> ufsi_imp_lca (uf_ds ufe_ds_imp) x y;
      newest_x \<leftarrow> find_newest_on_path_imp ufe_ds_imp lca x;
      newest_y \<leftarrow> find_newest_on_path_imp ufe_ds_imp lca y;
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
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      explain_imp ufe_ds_imp x y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp *
    \<up>(r = explain (ufe_ds.uf_ds ufe_init) (ufe_ds.unions ufe_ds) x y)>"
  unfolding explain_eq_explain'[OF assms]
  using explain'_dom_if_ufe_rep_of_eq[OF assms(1-3)] assms
proof(induction rule: explain'_pinduct)
  case (eq x)
  then show ?case
    by (subst explain_imp.simps) sep_auto
next
  case (newest_x x y ax bx)
  then interpret ufe_tree where ufe_ds = ufe_ds and pivot = x
    by unfold_locales
  from newest_x obtain px py where
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) px x"
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) py y"
    using lca_ufa_lca lca_reachableD reachable_awalk
    by (metis in_verts_if_ufa_rep_of_eq)
  moreover from this newest_x have
    "the (find_newest_on_path ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) x)
      < length (ufe_ds.unions ufe_ds)"
    using find_newest_on_path_if_eq newest_on_path_find_newest_on_path newest_on_path_lt_length_unions
    by (metis less_eq_option_None_is_None)
  ultimately show ?case
    using newest_x.prems newest_x.hyps
    apply(subst explain_imp.simps)
    apply(vcg)
     apply(rule newest_x.IH(1))
    apply(vcg)
     apply(rule newest_x.IH(2))
    apply(sep_auto simp: explain'.psimps[OF explain'_dom_if_ufe_rep_of_eq])
    done
next
  case (newest_y x y ay "by")
  then interpret ufe_tree where ufe_ds = ufe_ds and pivot = x
    by unfold_locales
  from newest_y obtain px py where
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) px x"
    "awalk (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) py y"
    using lca_ufa_lca lca_reachableD reachable_awalk
    by (metis in_verts_if_ufa_rep_of_eq)
  moreover from this newest_y have
    "the (find_newest_on_path ufe_ds (ufa_lca (ufe_ds.uf_ds ufe_ds) x y) y)
      < length (ufe_ds.unions ufe_ds)"
    using find_newest_on_path_if_eq newest_on_path_find_newest_on_path newest_on_path_lt_length_unions
    by (metis less_eq_option_None)
  ultimately show ?case
    using newest_y.prems newest_y.hyps
    apply(subst explain_imp.simps)
    apply(vcg)
     apply(rule newest_y.IH(1))
    apply(vcg)
     apply(rule newest_y.IH(2))
    apply(sep_auto simp: explain'.psimps[OF explain'_dom_if_ufe_rep_of_eq])
    done
qed

definition "explain_partial_imp ufe_ds_imp x y \<equiv>
  if x = y then return (Some (ReflP x))
  else do {
    n \<leftarrow> Array.len (uf_ds ufe_ds_imp);
    if x < n \<and> y < n then do {
      rep_x \<leftarrow> ufsi_imp_rep_of (uf_ds ufe_ds_imp) x;
      rep_y \<leftarrow> ufsi_imp_rep_of (uf_ds ufe_ds_imp) y;
      if rep_x = rep_y then do {
        p \<leftarrow> explain_imp ufe_ds_imp x y;
        return (Some p)
      }
      else return None
    }
    else return None
  }"

lemma (in ufe_invars) explain_partial_imp_rule[sep_heap_rules]:
  shows
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp>
      explain_partial_imp ufe_ds_imp x y
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp *
      \<up>(r = explain_partial (ufe_ds.uf_ds ufe_init) (ufe_ds.unions ufe_ds) x y)>"
proof -
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufe_ds.uf_ds ufe_ds))"
  have "ufsi_\<alpha> ufsi = ufe_\<alpha> ufe_ds"
    unfolding ufsi_def
    including ufsi.lifting ufa_ufs_transfer 
    by (transfer, transfer) simp
  have
    "<is_ufsi ufsi (uf_ds ufe_ds_imp)> Array.len (uf_ds ufe_ds_imp)
    <\<lambda>r. is_ufsi ufsi (uf_ds ufe_ds_imp) *
      \<up>(\<forall>i. i < r \<longleftrightarrow> i \<in> Field (ufsi_\<alpha> ufsi))>"
    unfolding is_ufsi_def
    by (sep_auto simp: Field_ufsi_\<alpha>_Abs_ufsi_eq)
  note [sep_heap_rules] =
    this[unfolded \<open>ufsi_\<alpha> ufsi = ufe_\<alpha> ufe_ds\<close>, unfolded ufsi_def]
  have [sep_heap_rules]:
    "<is_ufe_ds (ufe_ds, n) ufe_ds_imp> Array.len (ufe_ds_imp.uf_ds ufe_ds_imp)
    <\<lambda>r. is_ufe_ds (ufe_ds, n) ufe_ds_imp * \<up>(\<forall>i. i < r \<longleftrightarrow> i \<in> Field (ufe_\<alpha> ufe_ds))>"
    unfolding is_ufe_ds_def
    by sep_auto
  have "(x, y) \<in> equivcl (set (ufe_ds.unions ufe_ds)) \<longleftrightarrow>
    x = y \<or>
    x \<in> Field (ufe_\<alpha> ufe_ds) \<and> y \<in> Field (ufe_\<alpha> ufe_ds) \<and>
    ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
    using in_equivcl_iff_eq_or_ufa_rep_of_eq
    using uf_ds_ufe_ds_eq_ufa_unions
    by (metis eff_unions ufa_\<alpha>_uf_ds_ufe_init valid_unions_if_eff_unions)
  then show ?thesis
    unfolding explain_partial_imp_def explain_partial_def
    by sep_auto
qed

end
