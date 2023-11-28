theory UFA_Tree
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
    "Tree_Theory.LCA_Directed_Tree"
begin

definition "ufa_tree_of l x \<equiv>
  let
    vs = {y. y < length l \<and> rep_of l y = rep_of l x}
  in
    \<lparr> pverts = vs
    , parcs = {(l ! x, x) |x. x \<in> vs \<and> l ! x \<noteq> x}
    \<rparr>"

function (domintros) awalk_from_rep :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "awalk_from_rep l x =
    (if l ! x = x then [] else awalk_from_rep l (l ! x) @ [(l ! x, x)])"
  by auto

function (domintros) awalk_verts_from_rep :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "awalk_verts_from_rep l x =
    (if l ! x = x then [] else awalk_verts_from_rep l (l ! x)) @ [x]"
  by auto

lemma awalk_from_rep_dom_if_rep_of_dom[simp]:
  "rep_of_dom (l, x) \<Longrightarrow> awalk_from_rep_dom (l, x)"
  using awalk_from_rep.domintros rep_of.pinduct
  by (metis curryE curryI)

lemma awalk_verts_from_rep_dom_if_rep_of_dom[simp]:
  "rep_of_dom (l, x) \<Longrightarrow> awalk_verts_from_rep_dom (l, x)"
  using awalk_verts_from_rep.domintros rep_of.pinduct
  by (metis curryE curryI)

locale ufa_invarL =
  fixes l
  assumes ufa_invar: "ufa_invar l"
begin

lemma verts_ufa_tree_of:
  "verts (ufa_tree_of l x) = {y. y < length l \<and> rep_of l y = rep_of l x}"
  unfolding ufa_tree_of_def
  by (auto simp: rep_of_refl)

lemma ufa_tree_of_eq_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "ufa_tree_of l y = ufa_tree_of l x"
  using assms unfolding ufa_tree_of_def by auto

lemma in_verts_ufa_tree_ofD:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "y < length l" "rep_of l y = rep_of l x"
  using assms verts_ufa_tree_of by simp_all

lemma idx_in_pverts_ufa_tree_ofI:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "l ! y \<in> verts (ufa_tree_of l x)"
proof -
  note assms[THEN in_verts_ufa_tree_ofD(1)]
  then have "rep_of l (l ! y) = rep_of l y" "l ! y < length l"
    by (simp_all add: rep_of_idx ufa_invar ufa_invarD(2))
  with assms show ?thesis
    unfolding verts_ufa_tree_of 
    by (simp add: in_verts_ufa_tree_ofD(2))
qed

end

locale ufa_tree_ofL = ufa_invarL l for l + 
  fixes x assumes lt_length: "x < length l"
begin

sublocale fin_digraph "ufa_tree_of l x"
  using ufa_invar lt_length
  by (unfold_locales) (auto simp: ufa_invarD rep_of_idx ufa_tree_of_def)

lemma x_in_pverts[simp]: "x \<in> verts (ufa_tree_of l x)"
  using lt_length unfolding verts_ufa_tree_of by simp

lemma ufa_tree_of_idx[simp]:
  "ufa_tree_of l (l ! x) = ufa_tree_of l x"
  using ufa_invar lt_length unfolding ufa_tree_of_def
  by (auto simp: rep_of_idx)

lemma ufa_tree_of_rep_of:
  "ufa_tree_of l (rep_of l x) = ufa_tree_of l x"
  using ufa_invar lt_length unfolding ufa_tree_of_def
  by (auto simp: rep_of_idem)

lemma awalk_idx:
  assumes "l ! x \<noteq> x"
  shows "awalk (l ! x) [(l ! x, x)] x"
  using ufa_invar lt_length assms arc_implies_awalk
  unfolding ufa_tree_of_def
  by (auto simp: ufa_invarD rep_of_idx)

lemma awalk_from_rep_rep_of:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awalk_from_rep l (rep_of l y) = []"
proof -
  from in_verts_ufa_tree_ofD(2)[OF assms] have "rep_of l y = rep_of l x" .
  with rep_of_min[OF ufa_invar lt_length, folded this] show ?thesis
    by (metis awalk_from_rep.domintros awalk_from_rep.psimps)
qed

lemma rep_of_if_idx_same:
  assumes "y \<in> verts (ufa_tree_of l x)" "z \<in> verts (ufa_tree_of l x)"
  assumes "l ! y = y"
  shows "rep_of l z = y"
  using assms ufa_invar
  by (metis in_verts_ufa_tree_ofD rep_of_iff)

lemma awlast_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awlast (rep_of l x) (awalk_from_rep l y) = y"
proof -
  from assms ufa_invar have "awalk_from_rep_dom (l, y)"
    by (simp add: in_verts_ufa_tree_ofD(1) ufa_invarD(1))
  then show ?thesis
    using assms rep_of_if_idx_same[OF _ x_in_pverts]
    by (induction rule: awalk_from_rep.pinduct)
      (auto simp: awalk_from_rep.psimps pre_digraph.awalk_verts_conv )
qed

lemma awalk_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awalk (rep_of l y) (awalk_from_rep l y) y"
  using ufa_invar in_verts_ufa_tree_ofD(1)[OF assms] assms
proof(induction rule: rep_of_induct)
  case (base i)
  then interpret l: ufa_tree_ofL l i
    by unfold_locales blast
  from base have "awalk_from_rep l i = []"
    by (metis l.awalk_from_rep_rep_of l.x_in_pverts rep_of_refl)
  with base show "?case"
    by (simp add: awalk_Nil_iff rep_of_refl)
next
  case (step i)
  then interpret l: ufa_tree_ofL l i
    by unfold_locales blast
  from step have "awalk (rep_of l i) (awalk_from_rep l (l ! i)) (l ! i)"
    using idx_in_pverts_ufa_tree_ofI in_verts_ufa_tree_ofD(2)
    by metis
  moreover have "awalk (l ! i) [(l ! i, i)] i"
    using step  by (metis l.awalk_idx ufa_tree_of_eq_if_in_verts)
  ultimately show ?case
    using step by (simp add: awalk_from_rep.psimps ufa_invarD(1))
qed

lemma awalk_verts_awalk_from_rep:
  assumes "y \<in> pverts (ufa_tree_of l x)"
  shows "awalk_verts (rep_of l y) (awalk_from_rep l y) 
    = rep_of l y # map snd (awalk_from_rep l y)"
  using assms awalk_awalk_from_rep awalk_verts_conv' in_verts_ufa_tree_ofD(2)
  by fastforce

lemma unique_awalk_ufa_tree_of_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "\<exists>!p. awalk (rep_of l x) p y"
proof
  note in_verts_ufa_tree_ofD[OF assms]
  then interpret y: ufa_tree_ofL l y
    by (unfold_locales) auto
  from \<open>rep_of l y = rep_of l x\<close> show "awalk (rep_of l x) (awalk_from_rep l y) y"
    using assms y.awalk_awalk_from_rep
    using ufa_tree_of_eq_if_in_verts by force

  show "p = awalk_from_rep l y" if "awalk (rep_of l x) p y" for p
    using that \<open>y < length l\<close> \<open>rep_of l y = rep_of l x\<close>
  proof(induction p arbitrary: y rule: rev_induct)
    case Nil
    then show ?case
      using awalk_from_rep_rep_of
      by (fastforce simp: awalk_Nil_iff)
  next
    case (snoc a p)
    then have "awalk (rep_of l x) p (fst a)" "a \<in> arcs (ufa_tree_of l x)"
      by auto
    then have "a = (l ! y, y)" "l ! y \<noteq> y"
      unfolding ufa_tree_of_def using snoc.prems(1) by auto
    note snoc.IH[OF \<open>awalk (rep_of l x) p (fst a)\<close>]
    with snoc.prems have "p = awalk_from_rep l (l ! y)"
      unfolding \<open>a = (l ! y, y)\<close>
      using rep_of_idx ufa_invar ufa_invarD(2) by simp
    with \<open>a = (l ! y, y)\<close> \<open>l ! y \<noteq> y\<close> snoc.prems show ?case
      using ufa_invar
      by (auto simp: ufa_invarD(1) awalk_from_rep.psimps)
  qed
qed

lemma distinct_awalk_verts_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "distinct (awalk_verts (rep_of l y) (awalk_from_rep l y))"
  using assms awalk_awalk_from_rep unique_awalk_ufa_tree_of_rep
  by (metis apath_awalk_to_apath apath_def in_verts_ufa_tree_ofD(2))

lemma distinct_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "distinct (awalk_from_rep l y)"
  using distinct_verts_imp_distinct[OF awalk_awalk_from_rep distinct_awalk_verts_awalk_from_rep]
  using assms by blast

sublocale fin_directed_tree "ufa_tree_of l x" "rep_of l x"
  using lt_length ufa_invar unique_awalk_ufa_tree_of_rep
  by unfold_locales (use verts_ufa_tree_of in \<open>auto simp: rep_of_bound rep_of_idem\<close>)

end

end