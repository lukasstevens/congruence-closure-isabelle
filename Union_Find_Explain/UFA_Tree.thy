theory UFA_Tree
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
    "Tree_Theory.Directed_Tree"
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

lemma awalk_from_rep_dom_if_rep_of_dom[simp]:
  "rep_of_dom (l, x) \<Longrightarrow> awalk_from_rep_dom (l, x)"
  using awalk_from_rep.domintros rep_of.pinduct
  by (metis curryE curryI)

locale ufa_invarL =
  fixes l
  assumes ufa_invar: "ufa_invar l"
begin

lemma pverts_ufa_tree_of:
  "pverts (ufa_tree_of l x) = {y. y < length l \<and> rep_of l y = rep_of l x}"
  unfolding ufa_tree_of_def
  by (auto simp: rep_of_refl)

lemma ufa_tree_of_eq_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "ufa_tree_of l y = ufa_tree_of l x"
  using assms unfolding ufa_tree_of_def by auto

end

locale ufa_tree_ofL = ufa_invarL l for l + 
  fixes x assumes lt_length: "x < length l"
begin

sublocale fin_digraph "ufa_tree_of l x"
  using ufa_invar lt_length
  by (unfold_locales) (auto simp: ufa_invarD rep_of_idx ufa_tree_of_def)

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
  "awalk_from_rep l (rep_of l x) = []"
proof -
  from lt_length ufa_invar have "rep_of l x < length l"
    by (simp add: rep_of_bound)
  note ufa_invarD(1)[OF ufa_invar this]
  with ufa_invar lt_length rep_of_min show ?thesis
    by (simp add: awalk_from_rep.psimps)
qed
  
lemma awalk_awalk_from_rep:
  "awalk (rep_of l x) (awalk_from_rep l x) x"
  using ufa_invar lt_length
proof(induction rule: rep_of_induct)
  case (base i)
  then interpret l: ufa_tree_ofL l i
    by unfold_locales blast
  from base have "awalk_from_rep l i = []"
    using l.awalk_from_rep_rep_of by (metis rep_of_refl)
  with base show "?case"
    by (auto simp: l.awalk_Nil_iff rep_of_refl pverts_ufa_tree_of)
next
  case (step i)
  then interpret l: ufa_tree_ofL l i
    by unfold_locales blast
  from step show ?case
    by (simp add: ufa_invarD(1) awalk_from_rep.psimps rep_of_idx l.awalk_idx)
qed


lemma unique_awalk_ufa_tree_of_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "\<exists>!p. awalk (rep_of l x) p y"
proof
  from assms have "y < length l" "rep_of l y = rep_of l x"
    by (simp_all add: pverts_ufa_tree_of)
  then interpret y: ufa_tree_ofL l y
    by (unfold_locales) auto
  from \<open>rep_of l y = rep_of l x\<close> show "awalk (rep_of l x) (awalk_from_rep l y) y"
    using assms y.awalk_awalk_from_rep
    using ufa_tree_of_eq_if_in_verts by simp

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

sublocale fin_directed_tree "ufa_tree_of l x" "rep_of l x"
  using lt_length ufa_invar unique_awalk_ufa_tree_of_rep
  by unfold_locales (auto simp: pverts_ufa_tree_of rep_of_bound rep_of_idem)

end

end