theory UFA_LCA
  imports Explain_Simple UFA_Forest
begin

definition ufa_lca where
  "ufa_lca uf x y \<equiv>
    last (longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y))"

lemma ufa_lca_symmetric:
  "ufa_lca uf x y = ufa_lca uf y x"
proof -
  have
    "longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y)
    = longest_common_prefix (awalk_verts_from_rep uf y) (awalk_verts_from_rep uf x)"
    by (simp add: longest_common_prefix_max_prefix longest_common_prefix_prefix1
          longest_common_prefix_prefix2 prefix_order.eq_iff)
  then show ?thesis
    unfolding ufa_lca_def
    by auto
qed


theorem (in ufa_forest) lca_ufa_lca:
  assumes "x \<in> verts (ufa_forest_of uf)"
  assumes "y \<in> verts (ufa_forest_of uf)"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "lca (ufa_lca uf x y) x y"
proof -
  note assms(1-2)[THEN awalk_awalk_from_rep, folded assms(3)]
  note lca_last_longest_common_prefix_awalk_verts[OF this]
  with assms(3) show ?thesis
    unfolding ufa_lca_def assms(1-2)[THEN awalk_verts_from_rep_eq_awalk_verts]
    by metis
qed

lemma (in ufa_forest) ufa_rep_of_ufa_lca:
  assumes "x \<in> verts (ufa_forest_of uf)"
  assumes "y \<in> verts (ufa_forest_of uf)"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "ufa_rep_of uf (ufa_lca uf x y) = ufa_rep_of uf x"
proof -
  note lca_ufa_lca[OF assms]
  with assms show ?thesis
    using lca_reachableD(1) ufa_rep_of_eq_if_reachable by blast
qed

lemma ufa_lca_ufa_union:
  assumes "eff_union uf a b"
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of (ufa_union uf a b) x = ufa_rep_of (ufa_union uf a b) y"
  shows "ufa_lca (ufa_union uf a b) x y =
    (if ufa_rep_of uf x = ufa_rep_of uf y then ufa_lca uf x y else ufa_rep_of uf b)"
proof -
  interpret ufa_forest where uf = uf .
  interpret ufa_union_forest: ufa_forest where uf = "ufa_union uf a b" .

  note awalk_verts_from_rep_union_eq = 
    assms(2,3)[THEN awalk_verts_from_rep_ufa_union[OF eff_unionD[OF assms(1)]]]

  note assms(2,3)[THEN ufa_forest.awalk_verts_from_rep_eq_Cons[unfolded verts_ufa_forest_of]]
  then obtain px py where
    px: "awalk_verts_from_rep uf x = ufa_rep_of uf x # px" and
    py: "awalk_verts_from_rep uf y = ufa_rep_of uf y # py"
    by metis

  show ?thesis
  proof(cases "ufa_rep_of uf x = ufa_rep_of uf y")
    case True
    with px py have
      "longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y) \<noteq> []"
      by simp
    with True show ?thesis
      unfolding ufa_lca_def awalk_verts_from_rep_union_eq
      by auto
  next
    case False
    
    from False assms consider
      "ufa_rep_of uf x = ufa_rep_of uf a" "ufa_rep_of uf y = ufa_rep_of uf b" |
      "ufa_rep_of uf x = ufa_rep_of uf b" "ufa_rep_of uf y = ufa_rep_of uf a"
      by (metis eff_unionD(1,2) ufa_rep_of_ufa_union)
    then show ?thesis
    proof(cases)
      case 1
      have "longest_common_prefix (awalk_verts_from_rep uf x) py = []"
      proof(rule ccontr)
        assume "longest_common_prefix (awalk_verts_from_rep uf x) py \<noteq> []"
        with 1 px obtain py' where "py = ufa_rep_of uf a # py'"
          by (cases py) force+
        with 1 py have "awalk_verts_from_rep uf y = ufa_rep_of uf b # ufa_rep_of uf a # py'"
          by metis
        moreover note y_in_verts = assms(3)[folded verts_ufa_forest_of]
        note awalk_awalk_from_rep[OF this] awalk_verts_from_rep_eq_awalk_verts[OF this]
        ultimately have "(ufa_rep_of uf b, ufa_rep_of uf a) \<in> arcs (ufa_forest_of uf)"
          using awalk_imp_vwalk by force
        then have "ufa_parent_of uf (ufa_rep_of uf a) = ufa_rep_of uf b"
          using eq_ufa_parent_of_if_mem_arcs_ufa_forest_of by simp
        with False 1 assms(2) show False
          by (metis ufa_parent_of_ufa_rep_of)
      qed

      with assms 1 py show ?thesis
        unfolding ufa_lca_def awalk_verts_from_rep_union_eq
        by auto
    next
      case 2
      have "longest_common_prefix px (awalk_verts_from_rep uf y) = []"
      proof(rule ccontr)
        assume "longest_common_prefix px (awalk_verts_from_rep uf y) \<noteq> []"
        with 2 py obtain px' where "px = ufa_rep_of uf a # px'"
          by (cases px) force+
        with 2 px have "awalk_verts_from_rep uf x = ufa_rep_of uf b # ufa_rep_of uf a # px'"
          by metis
        moreover note y_in_verts = assms(2)[folded verts_ufa_forest_of]
        note awalk_awalk_from_rep[OF this] awalk_verts_from_rep_eq_awalk_verts[OF this]
        ultimately have "(ufa_rep_of uf b, ufa_rep_of uf a) \<in> arcs (ufa_forest_of uf)"
          using awalk_imp_vwalk by force
        then have "ufa_parent_of uf (ufa_rep_of uf a) = ufa_rep_of uf b"
          using eq_ufa_parent_of_if_mem_arcs_ufa_forest_of by simp
        with False 2 assms(3) show False
          by (metis ufa_parent_of_ufa_rep_of)
      qed

      with assms 2 False px  show ?thesis
        unfolding ufa_lca_def awalk_verts_from_rep_union_eq
        by simp
    qed
  qed
qed

lemma (in ufa_forest) ufa_union_awalk_eq:
  assumes "eff_union uf a b"
  assumes "ufa_rep_of uf x \<noteq> ufa_rep_of uf y"
  assumes "pre_digraph.awalk (ufa_forest_of (ufa_union uf a b)) x p y"
  shows "x = ufa_rep_of uf b" "p = (ufa_rep_of uf b, ufa_rep_of uf a) # awalk_from_rep uf y"
proof -
  interpret ufa_union_forest: ufa_forest where uf = "ufa_union uf a b" .
  from assms(3) have in_verts:
    "x \<in> verts (ufa_forest_of uf)" "y \<in> verts (ufa_forest_of uf)"
    using verts_ufa_forest_of_ufa_union by blast+

  from assms have "ufa_union_forest.lca (ufa_lca (ufa_union uf a b) x y) x y"
    using ufa_union_forest.ufa_rep_of_eq_if_awalk
    by (intro ufa_forest.lca_ufa_lca) blast+
  moreover from assms have "ufa_union_forest.lca x x y"
    using ufa_union_forest.reachable_awalkI ufa_union_forest.lca_same_if_reachable
    by blast
  moreover from calculation assms have "ufa_lca (ufa_union uf a b) x y = x"
    using ufa_union_forest.Uniq_lca[unfolded Uniq_def] by blast
  moreover have "ufa_lca (ufa_union uf a b) x y = ufa_rep_of uf b"
    using assms in_verts ufa_union_forest.ufa_rep_of_eq_if_awalk
    by (subst ufa_lca_ufa_union) (fastforce simp del: with_proj_simps)+

  ultimately show "x = ufa_rep_of uf b"
    by simp

  moreover from assms have
    "ufa_rep_of (ufa_union uf a b) y = ufa_rep_of (ufa_union uf a b) x"
    using ufa_union_forest.ufa_rep_of_eq_if_awalk by simp
  ultimately have "ufa_rep_of (ufa_union uf a b) y = x"
    using assms(1) ufa_rep_of_ufa_union by auto
  with assms have
    "p = awalk_from_rep (ufa_union uf a b) y"
    using ufa_union_forest.eq_awalk_from_rep_if_awalk_ufa_rep_of
    by (metis ufa_union_forest.awalkE')
  moreover from assms in_verts \<open>ufa_rep_of (ufa_union uf a b) y = x\<close> have
    "ufa_rep_of uf y = ufa_rep_of uf a"
    by (cases "ufa_rep_of uf y = ufa_rep_of uf a")
      (subst (asm) ufa_rep_of_ufa_union; fastforce simp del: with_proj_simps)+
  ultimately show "p = (ufa_rep_of uf b, ufa_rep_of uf a) # awalk_from_rep uf y"
    using assms in_verts
    by (subst (asm) awalk_from_rep_ufa_union) (auto simp del: with_proj_simps)
qed
    
end