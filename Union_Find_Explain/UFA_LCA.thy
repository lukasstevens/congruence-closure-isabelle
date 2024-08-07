theory UFA_LCA
  imports Explain_Simple UFA_Tree
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


theorem (in ufa_tree) lca_ufa_lca:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "z \<in> verts (ufa_tree_of uf x)"
  shows "lca (ufa_lca uf y z) y z"
proof -
  from assms have "ufa_rep_of uf y = ufa_rep_of uf z"
    by simp
  note assms[THEN awalk_awalk_from_rep, folded this]
  note lca_last_longest_common_prefix_awalk_verts[OF this]
  with \<open>ufa_rep_of uf y = ufa_rep_of uf z\<close> show ?thesis
    unfolding ufa_lca_def
    unfolding assms[THEN awalk_verts_from_rep_eq_awalk_verts]
    by simp
qed

theorem (in ufa_tree) ufa_rep_of_ufa_lca:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "z \<in> verts (ufa_tree_of uf x)"
  shows "ufa_rep_of uf (ufa_lca uf y z) = ufa_rep_of uf y"
proof -
  note lca_ufa_lca[OF assms]
  then have "ufa_lca uf y z \<in> verts (ufa_tree_of uf x)"
    using lca_reachableD(2) reachable_in_verts(1) by blast
  with assms show ?thesis
    by simp
qed

lemma ufa_lca_ufa_union:
  assumes "eff_union uf a b"
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of (ufa_union uf a b) x = ufa_rep_of (ufa_union uf a b) y"
  shows "ufa_lca (ufa_union uf a b) x y =
    (if ufa_rep_of uf x = ufa_rep_of uf y then ufa_lca uf x y else ufa_rep_of uf b)"
proof -
  interpret ufa_tree_x: ufa_tree where x = x
    using assms by unfold_locales
  interpret ufa_tree_y: ufa_tree where x = y
    using assms by unfold_locales

  note awalk_verts_from_rep_union_eq = 
    assms(2,3)[THEN ufa_tree_x.awalk_verts_from_rep_union[OF eff_unionD[OF assms(1)]]]
  
  show ?thesis
  proof(cases "ufa_rep_of uf x = ufa_rep_of uf y")
    case True
    with \<open>x \<in> Field (ufa_\<alpha> uf)\<close> \<open>y \<in> Field (ufa_\<alpha> uf)\<close>
    have "x \<in> verts (ufa_tree_of uf x)" "y \<in> verts (ufa_tree_of uf x)"
      using ufa_tree_x.in_verts_if_rep_of_eq by simp_all
    note this[THEN ufa_tree_x.awalk_verts_from_rep_eq_Cons]
    with True obtain px py where
      "awalk_verts_from_rep uf x = ufa_rep_of uf y # px"
      "awalk_verts_from_rep uf y = ufa_rep_of uf y # py"
      by metis
    then have
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
      from 1 obtain px where awalk_verts_from_rep_x:
        "awalk_verts_from_rep uf x = ufa_rep_of uf a # px"
        using ufa_tree_x.awalk_verts_from_rep_eq_Cons[OF ufa_tree_x.x_in_verts]
        by metis
      from 1 obtain py where awalk_verts_from_rep_y:
        "awalk_verts_from_rep uf y = ufa_rep_of uf b # py"
        using ufa_tree_y.awalk_verts_from_rep_eq_Cons[OF ufa_tree_y.x_in_verts]
        by metis

      have "longest_common_prefix (awalk_verts_from_rep uf x) py = []"
      proof(rule ccontr)
        assume "longest_common_prefix (awalk_verts_from_rep uf x) py \<noteq> []"
        then obtain py' where "py = ufa_rep_of uf a # py'"
          unfolding awalk_verts_from_rep_x by (cases py) force+
        then have "awalk_verts_from_rep uf y = ufa_rep_of uf b # ufa_rep_of uf a # py'"
          using awalk_verts_from_rep_y by blast
        moreover note ufa_tree_y.awalk_verts_from_rep_eq_awalk_verts[OF ufa_tree_y.x_in_verts]
        moreover note ufa_tree_y.awalk_awalk_from_rep[OF ufa_tree_y.x_in_verts]
        ultimately have
          "ufa_rep_of uf a \<in> verts (ufa_tree_of uf y)"
          "ufa_rep_of uf b \<in> verts (ufa_tree_of uf y)"
          using ufa_tree_y.adj_in_verts
          by (metis ufa_tree_y.awalk_imp_vwalk ufa_tree_y.vwalk_Cons_Cons)+
        note this[THEN ufa_rep_of_eq_if_in_verts[unfolded NO_MATCH_def]]
        then have "ufa_rep_of uf a = ufa_rep_of uf b"
          using eff_unionD(1,2)[OF assms(1)] ufa_rep_of_ufa_rep_of
          by simp
        with eff_unionD(3)[OF assms(1)] show False
          by blast
      qed

      with assms 1 show ?thesis
        unfolding ufa_lca_def awalk_verts_from_rep_union_eq awalk_verts_from_rep_y
        by auto
    next
      case 2
      from 2 obtain px where awalk_verts_from_rep_x:
        "awalk_verts_from_rep uf x = ufa_rep_of uf b # px"
        using ufa_tree_x.awalk_verts_from_rep_eq_Cons[OF ufa_tree_x.x_in_verts]
        by metis
      from 2 obtain py where awalk_verts_from_rep_y:
        "awalk_verts_from_rep uf y = ufa_rep_of uf a # py"
        using ufa_tree_y.awalk_verts_from_rep_eq_Cons[OF ufa_tree_y.x_in_verts]
        by metis

      have "longest_common_prefix px (awalk_verts_from_rep uf y) = []"
      proof(rule ccontr)
        assume "longest_common_prefix px (awalk_verts_from_rep uf y) \<noteq> []"
        then obtain px' where "px = ufa_rep_of uf a # px'"
          unfolding awalk_verts_from_rep_y by (cases px) force+
        then have "awalk_verts_from_rep uf x = ufa_rep_of uf b # ufa_rep_of uf a # px'"
          using awalk_verts_from_rep_x by blast
        moreover note ufa_tree_x.awalk_verts_from_rep_eq_awalk_verts[OF ufa_tree_x.x_in_verts]
        moreover note ufa_tree_x.awalk_awalk_from_rep[OF ufa_tree_x.x_in_verts]
        ultimately have
          "ufa_rep_of uf a \<in> verts (ufa_tree_of uf x)"
          "ufa_rep_of uf b \<in> verts (ufa_tree_of uf x)"
          using ufa_tree_x.adj_in_verts
          by (metis ufa_tree_x.awalk_imp_vwalk ufa_tree_x.vwalk_Cons_Cons)+
        note this[THEN ufa_rep_of_eq_if_in_verts[unfolded NO_MATCH_def]]
        then have "ufa_rep_of uf a = ufa_rep_of uf b"
          using eff_unionD(1,2)[OF assms(1)] ufa_rep_of_ufa_rep_of
          by simp
        with eff_unionD(3)[OF assms(1)] show False
          by blast
      qed

      with assms 2 False show ?thesis
        unfolding ufa_lca_def awalk_verts_from_rep_union_eq awalk_verts_from_rep_x
        by simp
    qed
  qed
qed

end