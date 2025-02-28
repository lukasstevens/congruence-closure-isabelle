theory Explain_Imp
  imports
    Explain_Efficient_Correctness
    "Union_Find.Union_Find_Size_Int_Imp"
    Dynamic_Array
begin

section \<open>Basic Union-Find-Explain\<close>

record ufe_imp =
  uf_ds\<^sub>i :: ufsi_imp
  au_ds\<^sub>i :: "nat option Heap.array"
  unions\<^sub>i :: "(nat \<times> nat) dyn_array"

definition "is_au_ds \<equiv> \<lambda>(au, n) au_imp. \<exists>\<^sub>Aau_list.
  au_imp \<mapsto>\<^sub>a au_list *
  \<up>(n = length au_list \<and> au = (\<lambda>k. if k < length au_list then au_list ! k else None))"

definition is_ufe :: "ufe \<times> nat \<Rightarrow> ufe_imp \<Rightarrow> assn" where
  "is_ufe \<equiv> \<lambda>(ufe, n) ufe_imp.
    is_ufsi (ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))) (uf_ds\<^sub>i ufe_imp) *
    \<up>(Field (ufe_\<alpha> ufe) = {0..<n}) *
    is_au_ds (au_ds ufe, n) (au_ds\<^sub>i ufe_imp) *
    is_dyn_array (unions ufe) (unions\<^sub>i ufe_imp)"

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
  assumes "i \<in> Field (ufe_\<alpha> ufe)"
  shows
    "<is_ufe (ufe, n) ufe_imp>
      Array.nth (au_ds\<^sub>i ufe_imp) i
    <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(r = au_ds ufe i)>"
  using assms unfolding is_ufe_def by sep_auto

lemma nth_unions_rule[sep_heap_rules]:
  assumes "i < length (unions ufe)"
  shows
    "<is_ufe (ufe, n) ufe_imp>
      Dynamic_Array.nth (unions\<^sub>i ufe_imp) i
    <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(r = unions ufe ! i)>"
  using assms unfolding is_ufe_def by sep_auto

definition ufe_imp_init :: "nat \<Rightarrow> ufe_imp Heap" where
  "ufe_imp_init n \<equiv> do {
    uf \<leftarrow> ufsi_imp_init n;
    au \<leftarrow> Array.new n None;
    us \<leftarrow> Dynamic_Array.new (0, 0);
    return \<lparr> uf_ds\<^sub>i = uf, au_ds\<^sub>i = au, unions\<^sub>i = us \<rparr>
  }"

lemma new_is_au_ds_rule[sep_heap_rules]:
  "<emp> Array.new n None <is_au_ds (Map.empty, n)>"
  unfolding is_au_ds_def by sep_auto

lemma ufe_imp_init_rule[sep_heap_rules]:
  "<emp> ufe_imp_init n <is_ufe (ufe_init n, n)>"
proof -
  have "ufsi_of_ufs (ufs_of_ufa (ufa_init n)) = ufsi_init n"
    including ufsi.lifting apply transfer
    including ufa_ufs_transfer apply transfer
    by simp
  then show ?thesis
    unfolding ufe_imp_init_def is_ufe_def
    by sep_auto
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
    including ufa_ufs_transfer and ufsi.lifting
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
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  shows
    "<is_ufe (ufe, n) ufe_imp> ufsi_imp_lca (uf_ds\<^sub>i ufe_imp) x y
    <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(r = ufa_lca (uf_ds ufe) x y)>"
proof -
  include ufsi.lifting and ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))"
  from assms(1,2) have "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)+
  moreover have "ufa_lca (ufa_of_ufsi ufsi) x y = ufa_lca (uf_ds ufe) x y"
    unfolding ufsi_def
    by transfer simp
  ultimately show ?thesis
    using assms
    unfolding is_ufe_def ufsi_def by sep_auto
qed

partial_function (heap) find_newest_on_path_acc_imp where
  [code]: "find_newest_on_path_acc_imp ufe_imp y x acc =
    (if y = x then return acc
    else do {
      au_x \<leftarrow> Array.nth (au_ds\<^sub>i ufe_imp) x;
      px \<leftarrow> ufsi_imp_parent_of (uf_ds\<^sub>i ufe_imp) x;
      find_newest_on_path_acc_imp ufe_imp y px (max au_x acc)
    })"

lemma (in ufe_forest) find_newest_on_path_acc_imp_rule[sep_heap_rules]:
  assumes "awalk z p y"
  shows
    "<is_ufe (ufe, n) ufe_imp>
      find_newest_on_path_acc_imp ufe_imp z y acc
    <\<lambda>r. is_ufe (ufe, n) ufe_imp *
      \<up>(r = max acc (find_newest_on_path ufe z y))>"
proof -
  note find_newest_on_path_dom[OF assms]
  moreover from assms have "y \<in> Field (ufe_\<alpha> ufe)"
    by blast
  ultimately show ?thesis
  proof(induction arbitrary: p acc rule: find_newest_on_path.pinduct)
    case (1 z y)

    moreover from "1"(3) have "y \<in> Field (ufsi_\<alpha> (ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))))"
      including ufsi.lifting and ufa_ufs_transfer
      by (transfer, transfer) simp
    moreover from this have
      "ufsi_parent_of (ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))) y =
        ufe_parent_of ufe y"
      including ufsi.lifting and ufa_ufs_transfer
      by (transfer, transfer) simp
    ultimately have [sep_heap_rules]:
      "<is_ufe (ufe, n) ufe_imp>
        ufsi_imp_parent_of (uf_ds\<^sub>i ufe_imp) y
      <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(r = ufa_parent_of (uf_ds ufe) y)>"
      unfolding is_ufe_def by sep_auto

    note [sep_heap_rules] = "1.IH"
    from "1.prems" "1.hyps" show ?case
      apply (subst find_newest_on_path_acc_imp.simps)
      by (sep_auto simp: find_newest_on_path.psimps max_def less_eq_option_None_is_None)
  qed
qed

definition find_newest_on_path_imp :: "ufe_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "find_newest_on_path_imp ufe_imp y x \<equiv> find_newest_on_path_acc_imp ufe_imp y x None"

lemma (in ufe_forest) find_newest_on_path_imp_rule[sep_heap_rules]:
  assumes "awalk z p y"
  shows
    "<is_ufe (ufe, n) ufe_imp>
      find_newest_on_path_imp ufe_imp z y
    <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(r = find_newest_on_path ufe z y)>"
  using assms unfolding find_newest_on_path_imp_def
  by sep_auto

partial_function (heap) explain_imp :: "ufe_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf Heap" where
  [code]: "explain_imp ufe_imp x y =
    (if x = y then return (ReflP x)
    else do {
      lca \<leftarrow> ufsi_imp_lca (uf_ds\<^sub>i ufe_imp) x y;
      newest_x \<leftarrow> find_newest_on_path_imp ufe_imp lca x;
      newest_y \<leftarrow> find_newest_on_path_imp ufe_imp lca y;
      if newest_x \<ge> newest_y then do {
        (ax, bx) \<leftarrow> Dynamic_Array.nth (unions\<^sub>i ufe_imp) (the newest_x);
        pxax \<leftarrow> explain_imp ufe_imp x ax;
        pbxy \<leftarrow> explain_imp ufe_imp bx y;
        return (TransP (TransP pxax (AssmP (the newest_x))) pbxy)
      } else do {
        (ay, by) \<leftarrow> Dynamic_Array.nth (unions\<^sub>i ufe_imp) (the newest_y);
        pxby \<leftarrow> explain_imp ufe_imp x by;
        payy \<leftarrow> explain_imp ufe_imp ay y;
        return (TransP (TransP pxby (SymP (AssmP (the newest_y)))) payy)
      }
    })"

lemma explain_imp_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  shows
    "<is_ufe (ufe, n) ufe_imp>
      explain_imp ufe_imp x y
    <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(r = explain ufe x y)>"
  unfolding explain_eq_explain'[OF assms]
  using explain'_dom_if_ufe_rep_of_eq[OF assms(1-3)] assms
proof(induction rule: explain'_pinduct)
  case (eq x)
  then show ?case
    by (subst explain_imp.simps) sep_auto
next
  case (newest_x x y ax bx)
  interpret ufe_forest ufe .

  from newest_x obtain px py where
    "awalk (ufa_lca (uf_ds ufe) x y) px x"
    "awalk (ufa_lca (uf_ds ufe) x y) py y"
    using lca_ufa_lca lca_reachableD reachable_awalk
    unfolding verts_ufa_forest_of by metis
  moreover from this newest_x have
    "the (find_newest_on_path ufe (ufa_lca (uf_ds ufe) x y) x)
      < length (unions ufe)"
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
  interpret ufe_forest ufe .
  from newest_y obtain px py where
    "awalk (ufa_lca (uf_ds ufe) x y) px x"
    "awalk (ufa_lca (uf_ds ufe) x y) py y"
    using lca_ufa_lca lca_reachableD reachable_awalk
    unfolding verts_ufa_forest_of by metis
  moreover from this newest_y have
    "the (find_newest_on_path ufe (ufa_lca (uf_ds ufe) x y) y)
      < length (unions ufe)"
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

definition "ufe_imp_link ufe_imp x y rep_x rep_y sz \<equiv> do {
  len \<leftarrow> Dynamic_Array.length (unions\<^sub>i ufe_imp);
  uf' \<leftarrow> ufsi_imp_link (uf_ds\<^sub>i ufe_imp) rep_x rep_y sz;
  au' \<leftarrow> Array.upd rep_x (Some len) (au_ds\<^sub>i ufe_imp);
  us' \<leftarrow> Dynamic_Array.push (unions\<^sub>i ufe_imp) (0, 0) (x, y);
  return \<lparr> uf_ds\<^sub>i = uf', au_ds\<^sub>i = au', unions\<^sub>i = us' \<rparr>
}"

lemma ufe_imp_link_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  defines "rep_x \<equiv> ufe_rep_of ufe x"
  defines "rep_y \<equiv> ufe_rep_of ufe y"
  defines "sz_rep_x \<equiv> ufa_size (uf_ds ufe) rep_x"
  defines "sz_rep_y \<equiv> ufa_size (uf_ds ufe) rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "<is_ufe (ufe, n) ufe_imp>
      ufe_imp_link ufe_imp x y rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufe (ufe_union ufe x y, n)>\<^sub>t"
proof -
  include ufsi.lifting and ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))"
  from assms(1,2) have "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)+
  moreover have "rep_x = ufsi_rep_of ufsi x" "rep_y = ufsi_rep_of ufsi y"
    unfolding ufsi_def rep_x_def rep_y_def
    by (transfer, transfer, simp)+
  moreover have "sz_rep_x = ufsi_size ufsi rep_x" "sz_rep_y = ufsi_size ufsi rep_y"
    unfolding ufsi_def sz_rep_x_def sz_rep_y_def rep_x_def rep_y_def
    by (transfer, transfer, simp)+
  moreover have
    "ufsi_of_ufs (ufs_of_ufa (ufa_union (uf_ds ufe) x y)) = ufsi_union ufsi x y"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "ufe_rep_of ufe x = ufsi_rep_of ufsi x"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "eff_union (uf_ds ufe) x y"
    using assms by blast
  ultimately show ?thesis
    using \<open>rep_x \<noteq> rep_y\<close> ufa_rep_of_in_Field_ufa_\<alpha>I[OF assms(1)]
    unfolding ufe_imp_link_def is_ufe_def
    by (sep_auto simp: ufsi_def[symmetric] fun_upd_def uf_ds_ufe_union_eq_if_eff_union)
qed

section \<open>Union-Find-Explain with Path Compression\<close>

record ufe_c_imp =
  ufe\<^sub>i :: ufe_imp
  uf_c_ds\<^sub>i :: ufsi_imp

definition is_ufe_c :: "(ufe \<times> nat) \<Rightarrow> ufe_c_imp \<Rightarrow> assn" where
  "is_ufe_c \<equiv> \<lambda>(ufe, n) ufe_imp_c.
    is_ufe (ufe, n) (ufe\<^sub>i ufe_imp_c) *
    is_ufsi_c (ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))) (uf_c_ds\<^sub>i ufe_imp_c)"

definition ufe_c_imp_init :: "nat \<Rightarrow> ufe_c_imp Heap" where
  "ufe_c_imp_init n \<equiv> do {
    ufe \<leftarrow> ufe_imp_init n;
    ufsi \<leftarrow> ufsi_imp_init n;
    return \<lparr> ufe\<^sub>i = ufe, uf_c_ds\<^sub>i = ufsi \<rparr>
  }"

definition ufe_c_imp_rep_of :: "ufe_c_imp \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "ufe_c_imp_rep_of ufe_c_imp \<equiv> ufsi_imp_rep_of_c (uf_c_ds\<^sub>i ufe_c_imp)"

definition ufe_c_imp_size :: "ufe_c_imp \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "ufe_c_imp_size ufe_c_imp \<equiv> ufsi_imp_size (uf_c_ds\<^sub>i ufe_c_imp)"

definition ufe_c_imp_link :: "ufe_c_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe_c_imp Heap" where
  "ufe_c_imp_link ufe_c_imp x y rep_x rep_y sz \<equiv> do {
    ufe_imp' \<leftarrow> ufe_imp_link (ufe\<^sub>i ufe_c_imp) x y rep_x rep_y sz;
    ufsi_imp' \<leftarrow> ufsi_imp_link (uf_c_ds\<^sub>i ufe_c_imp) rep_x rep_y sz;
    return \<lparr> ufe\<^sub>i = ufe_imp', uf_c_ds\<^sub>i = ufsi_imp' \<rparr>
  }"

definition ufe_c_imp_union_size :: "ufe_c_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe_c_imp Heap" where
  "ufe_c_imp_union_size ufe_c_imp x y \<equiv> do {
    rep_x \<leftarrow> ufe_c_imp_rep_of ufe_c_imp x;
    rep_y \<leftarrow> ufe_c_imp_rep_of ufe_c_imp y;
    if rep_x = rep_y then return ufe_c_imp
    else do {
      sz_rep_x \<leftarrow> ufe_c_imp_size ufe_c_imp rep_x;
      sz_rep_y \<leftarrow> ufe_c_imp_size ufe_c_imp rep_y;
      if sz_rep_x < sz_rep_y
      then ufe_c_imp_link ufe_c_imp x y rep_x rep_y (sz_rep_x + sz_rep_y)
      else ufe_c_imp_link ufe_c_imp y x rep_y rep_x (sz_rep_y + sz_rep_x)
    }
  }"

lemma ufe_c_imp_init_rule:
  "<emp> ufe_c_imp_init n <is_ufe_c (ufe_init n, n)>"
proof -
  include ufsi.lifting and ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (ufa_init n))"
  have "eq_on_ufsi_rep_of (ufsi_init n) ufsi"
    unfolding eq_on_ufsi_rep_of_def ufsi_def
    by (transfer, transfer) simp
  then have
    "is_ufsi (ufsi_init n) ufsi' \<Longrightarrow>\<^sub>A is_ufsi_c ufsi ufsi'" for ufsi'
    unfolding ufsi_def
    by (sep_auto eintros add: is_ufsi_entails_is_ufsi_c_if_eq_on_ufsi_rep_of)
  then show ?thesis
    unfolding ufe_c_imp_init_def is_ufe_c_def
    apply (sep_auto simp: ufsi_def[symmetric])
    using fr_refl fr_rot_rhs by blast
qed
  
lemma ufe_c_imp_rep_of_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)"
  shows
    "<is_ufe_c (ufe, n) ufe_c_imp>
      ufe_c_imp_rep_of ufe_c_imp x
    <\<lambda>r. is_ufe_c (ufe, n) ufe_c_imp * \<up>(r = ufe_rep_of ufe x)>"
proof -
  include ufsi.lifting and ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))"
  from assms(1) have "x \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "ufe_rep_of ufe x = ufsi_rep_of ufsi x"
    unfolding ufsi_def by (transfer, transfer, simp) 
  ultimately show ?thesis
    unfolding is_ufe_c_def ufe_c_imp_rep_of_def
    by (sep_auto simp: ufsi_def[symmetric])
qed

lemma ufe_c_imp_size_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = x"
  shows
    "<is_ufe_c (ufe, n) ufe_c_imp>
      ufe_c_imp_size ufe_c_imp x
    <\<lambda>r. is_ufe_c (ufe, n) ufe_c_imp * \<up>(r = ufa_size (uf_ds ufe) x)>"
proof -
  include ufsi.lifting and ufa_ufs_transfer
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))"
  from assms(1) have "x \<in> Field (ufsi_\<alpha> ufsi)"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover from assms(2) have "ufsi_rep_of ufsi x = x"
    unfolding ufsi_def by (transfer, transfer, simp)
  moreover have "ufa_size (uf_ds ufe) x = ufsi_size ufsi x"
    unfolding ufsi_def by (transfer, transfer, simp) 
  ultimately show ?thesis
    unfolding is_ufe_c_def ufe_c_imp_size_def
    by (sep_auto simp: ufsi_def[symmetric])
qed

lemma ufe_c_imp_link_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  defines "rep_x \<equiv> ufe_rep_of ufe x"
  defines "rep_y \<equiv> ufe_rep_of ufe y"
  defines "sz_rep_x \<equiv> ufa_size (uf_ds ufe) rep_x"
  defines "sz_rep_y \<equiv> ufa_size (uf_ds ufe) rep_y"
  assumes "rep_x \<noteq> rep_y"
  shows
    "<is_ufe_c (ufe, n) ufe_c_imp>
      ufe_c_imp_link ufe_c_imp x y rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufe_c (ufe_union ufe x y, n)>\<^sub>t"
proof -
  have [sep_heap_rules]:
    "<is_ufe (ufe, n) (ufe\<^sub>i ufe_c_imp)>
        ufe_imp_link (ufe\<^sub>i ufe_c_imp) x y rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufe (ufe_union ufe x y, n)>\<^sub>t"
    using assms ufe_imp_link_rule by blast

  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))"
  have [sep_heap_rules]:
    "<is_ufsi_c ufsi (uf_c_ds\<^sub>i ufe_c_imp)>
      ufsi_imp_link (uf_c_ds\<^sub>i ufe_c_imp) rep_x rep_y (sz_rep_x + sz_rep_y)
    <is_ufsi_c (ufsi_union ufsi x y)>"
  proof -
    include ufsi.lifting and ufa_ufs_transfer
    from assms(1,2) have "x \<in> Field (ufsi_\<alpha> ufsi)" "y \<in> Field (ufsi_\<alpha> ufsi)"
      unfolding ufsi_def by (transfer, transfer, simp)+
    moreover have
      "rep_x = ufsi_rep_of ufsi x" "rep_y = ufsi_rep_of ufsi y"
      unfolding rep_x_def rep_y_def ufsi_def by (transfer, transfer, simp)+
    moreover from this have
      "sz_rep_x = ufsi_size ufsi (ufsi_rep_of ufsi x)"
      "sz_rep_y = ufsi_size ufsi (ufsi_rep_of ufsi y)"
      unfolding sz_rep_x_def sz_rep_y_def ufsi_def
      by (transfer, transfer, simp)+
    ultimately show ?thesis
      using \<open>rep_x \<noteq> rep_y\<close> ufsi_imp_link_is_ufsi_c_rule by blast
  qed

  from assms have "eff_union (uf_ds ufe) x y"
    by blast
  then have eq_ufsi_union:
    "ufsi_of_ufs (ufs_of_ufa (uf_ds (ufe_union ufe x y))) = ufsi_union ufsi x y"
    unfolding ufsi_def including ufsi.lifting and ufa_ufs_transfer
    by (transfer, transfer) (simp add: uf_ds_ufe_union_eq) 

  show ?thesis
    using assms(1,2,7) unfolding ufe_c_imp_link_def
    by (sep_auto simp: is_ufe_c_def ufsi_def[symmetric] eq_ufsi_union simp del: ufa_size_ufa_rep_of)
qed
  
lemma ufe_c_imp_union_size_rule_if_ufe_rep_of_neq[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  shows
    "<is_ufe_c (ufe, n) ufe_c_imp>
      ufe_c_imp_union_size ufe_c_imp x y
    <is_ufe_c (ufe_union_size ufe x y, n)>\<^sub>t"
  using assms unfolding ufe_c_imp_union_size_def
  by (sep_auto simp: ufe_union_size_def simp del: ufa_size_ufa_rep_of)

definition "explain_partial_imp ufe_c_imp x y \<equiv>
  if x = y then return (Some (ReflP x))
  else do {
    n \<leftarrow> Array.len (uf_ds\<^sub>i (ufe\<^sub>i ufe_c_imp));
    if x < n \<and> y < n then do {
      rep_x \<leftarrow> ufe_c_imp_rep_of ufe_c_imp x;
      rep_y \<leftarrow> ufe_c_imp_rep_of ufe_c_imp y;
      if rep_x = rep_y then do {
        p \<leftarrow> explain_imp (ufe\<^sub>i ufe_c_imp) x y;
        return (Some p)
      }
      else return None
    }
    else return None
  }"

lemma explain_imp_is_ufe_c_rule[sep_heap_rules]:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  shows
    "<is_ufe_c (ufe, n) ufe_c_imp>
      explain_imp (ufe\<^sub>i ufe_c_imp) x y
    <\<lambda>r. is_ufe_c (ufe, n) ufe_c_imp * \<up>(r = explain ufe x y)>"
  using assms unfolding is_ufe_c_def by sep_auto

lemma Array_len_is_ufsi_conj_in_Field_ufsi_\<alpha>_rule[sep_heap_rules]:
  "<is_ufsi ufsi ufsi_imp>
    Array.len ufsi_imp
   <\<lambda>r. is_ufsi ufsi ufsi_imp * \<up>(\<forall>i. i < r \<longleftrightarrow> i \<in> Field (ufsi_\<alpha> ufsi))>"
  unfolding is_ufsi_def by (sep_auto simp: Field_ufsi_\<alpha>_Abs_ufsi_eq)

lemma Array_len_is_ufe_conj_in_Field_ufe_\<alpha>_rule[sep_heap_rules]:
  "<is_ufe (ufe, n) ufe_imp>
    Array.len (uf_ds\<^sub>i ufe_imp)
   <\<lambda>r. is_ufe (ufe, n) ufe_imp * \<up>(\<forall>i. i < r \<longleftrightarrow> i \<in> Field (ufe_\<alpha> ufe))>"
proof -
  define ufsi where "ufsi \<equiv> ufsi_of_ufs (ufs_of_ufa (uf_ds ufe))"
  have "ufsi_\<alpha> ufsi = ufe_\<alpha> ufe"
    unfolding ufsi_def
    including ufsi.lifting and ufa_ufs_transfer 
    by (transfer, transfer) simp
  then show ?thesis
    unfolding is_ufe_def by (sep_auto simp: ufsi_def[symmetric])
qed

lemma Array_len_is_ufe_c_conj_in_Field_ufe_\<alpha>_rule[sep_heap_rules]:
  "<is_ufe_c (ufe, n) ufe_imp>
    Array.len (uf_ds\<^sub>i (ufe\<^sub>i ufe_imp))
   <\<lambda>r. is_ufe_c (ufe, n) ufe_imp * \<up>(\<forall>i. i < r \<longleftrightarrow> i \<in> Field (ufe_\<alpha> ufe))>"
  unfolding is_ufe_c_def by sep_auto

theorem explain_partial_imp_rule[sep_heap_rules]:
  shows
    "<is_ufe_c (ufe, n) ufe_c_imp>
      explain_partial_imp ufe_c_imp x y
    <\<lambda>r. is_ufe_c (ufe, n) ufe_c_imp * \<up>(r = explain_partial ufe x y)>"
  unfolding explain_partial_imp_def explain_partial_def
  unfolding in_equivcl_iff_eq_or_ufe_rep_of_eq
  by sep_auto

export_code ufe_c_imp_init ufe_c_imp_rep_of ufe_c_imp_union_size explain_partial_imp
  in SML_imp module_name UFE file_prefix UFE

end
