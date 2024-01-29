section \<open>Correctness proofs for Explain\<close>
theory Explain_Correctness
  imports Helper_Functions
begin

lemma (in ufe_tree) neq_find_newest_on_path:
  assumes "y \<in> verts (ufa_tree_of uf x)" "x \<noteq> y"
  assumes ulca_eq: "ulca = ufa_lca uf x y"
  shows "find_newest_on_walk uf au ulca x \<noteq> find_newest_on_walk uf au ulca y"
proof -
  note lca_ulca = lca_ufa_lca[OF \<open>y \<in> verts (ufa_tree_of uf x)\<close>]
  with ulca_eq obtain px py where
    px: "awalk ulca px x" and py: "awalk ulca py y"
    by (meson lca_reachableD reachable_awalk)
  note find_newest_on_walk_dom = this[THEN find_newest_on_walk_dom]
  note find_newest_on_walk_psimps = this[THEN find_newest_on_walk.psimps]
  consider (lca_x) "x = ulca" | (lca_y) "y = ulca" | (not_lca) "x \<noteq> ulca \<and> y \<noteq> ulca"
    using \<open>x \<noteq> y\<close> by auto
  then show ?thesis
  proof cases
    case lca_x
    then have "find_newest_on_walk uf au ulca x = None"
      using find_newest_on_walk_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_x have "find_newest_on_walk uf au ulca y \<noteq> None"
      using find_newest_on_walk_eq_Max_au_of[OF py] by blast      
    ultimately show ?thesis
      by force
  next
    case lca_y
    then have "find_newest_on_walk uf au ulca y = None"
      using find_newest_on_walk_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_y have "find_newest_on_walk uf au ulca x \<noteq> None"
      using find_newest_on_walk_eq_Max_au_of[OF px] by blast      
    ultimately show ?thesis
      by force
  next
    case not_lca
    moreover
    from not_lca px py have "px \<noteq> []" "py \<noteq> []"
      using awalk_empty_ends px by blast+
    from not_lca px py obtain ix iy where
      ix: "ix \<in> set px" "find_newest_on_walk uf au ulca x = Some (au_of ix)" and
      iy: "iy \<in> set py" "find_newest_on_walk uf au ulca y = Some (au_of iy)"
      sorry
    moreover note ps[unfolded ulca_eq] = px py
    note disjoint_tl_awalk_verts_if_awalk_lca[OF lca_ulca \<open>x \<noteq> y\<close> this]
    with ix iy ulca_eq have "ix \<noteq> iy"
      by blast
    moreover from px py ix iy have
      "ix \<in> verts (ufa_tree_of uf x)" "iy \<in> verts (ufa_tree_of uf x)"
      by (meson awalk_decomp awalk_last_in_verts in_set_tlD)+
    then have "ix < length au" "iy < length au"
      using in_verts_ufa_tree_ofD(1) length_au by simp_all
    ultimately show ?thesis
      using distinct_au[unfolded distinct_conv_nth] by simp
  qed
qed

lemma (in ufe_tree) newest_on_walk_newest_x:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "x \<noteq> y"
  assumes ulca_eq: "ulca = ufa_lca uf x y"
  assumes "newest_x = find_newest_on_walk uf au ulca x"
  assumes "newest_y = find_newest_on_walk uf au ulca y"
  assumes "newest_x > newest_y"
  obtains px where "newest_on_walk newest_x ulca px x" "ulca \<noteq> x"
proof -
  note lca_ulca = lca_ufa_lca[OF \<open>y \<in> verts (ufa_tree_of uf x)\<close>]
  with ulca_eq obtain px py where
    px: "awalk ulca px x" and py: "awalk ulca py y"
    by (meson lca_reachableD reachable_awalk)
  with assms have "newest_on_walk newest_x ulca px x" if "ulca \<noteq> x"
    using that newest_on_walk_find_newest_on_walk by blast

  moreover note px py
  note find_newest_on_walk_dom = this[THEN find_newest_on_walk_domain]
  note find_newest_on_walk_psimps = this[THEN find_newest_on_walk.psimps]
  have "ulca \<noteq> x"
  proof
    assume "ulca = x"
    with \<open>x \<noteq> y\<close> py have "l ! y \<noteq> y"
      using awalk_idx_sameD(1) by blast
    with \<open>ulca = x\<close> assms show False
      unfolding find_newest_on_walk_psimps
      using in_verts_ufa_tree_ofD(1) nth_au_nonneg_if_not_rep by fastforce
  qed

  ultimately show ?thesis
    using that by blast
qed

lemma (in ufe_invars) explain_dom_symmetric:
  assumes "explain_dom l au unions (x, y)"
  assumes "x < length l" "y < length l"
  shows "explain_dom l au unions (y, x)"
  using assms
proof(induction rule: explain_pinduct)
  case (newest_x x y ulca newest_x newest_y ax bx)
  then interpret ufe_tree l unions au x
    by (unfold_locales) blast
  from newest_x neq_find_newest_on_path have "newest_x \<noteq> newest_y"
    using in_vertsI by metis
  with newest_x.hyps have "newest_y < newest_x"
    using newest_x.hyps(7) by fastforce
  from newest_x.hyps(4) have ulca_eq: "ulca = ufa_lca uf y x"
    using ufa_lca_symmetric by simp
  note hyps = newest_x.hyps(2,3)[symmetric] ulca_eq newest_x.hyps(6,5)
    \<open>newest_y < newest_x\<close> newest_x.hyps(8)
  note domintro = explain_newest_y_domintro[OF hyps]

  with newest_x \<open>newest_y < newest_x\<close> obtain px where
    "newest_on_walk newest_x ulca px x" "ulca \<noteq> x"
    using newest_on_walk_newest_x[OF in_vertsI] by metis
  note newest_on_walk_valid_union[OF this \<open>unions ! nat newest_x = (ax, bx)\<close>]
  with newest_x.prems show ?case
    by (intro domintro newest_x.IH) assumption+
next
  case (newest_y x y ulca newest_x newest_y ay "by")
  then interpret ufe_tree l unions au y
    by (unfold_locales) blast
  from newest_y.hyps(4) have ulca_eq: "ulca = ufa_lca uf y x"
    using ufa_lca_symmetric by simp
  from newest_y have "newest_x \<le> newest_y"
    by simp
  note hyps = newest_y.hyps(2,3)[symmetric] ulca_eq newest_y.hyps(6,5)
    \<open>newest_x \<le> newest_y\<close> newest_y.hyps(8)
  note domintro = explain_newest_x_domintro[OF hyps]

  with newest_y \<open>newest_y > newest_x\<close> obtain py where
    "newest_on_walk newest_y ulca py y" "ulca \<noteq> y"
    using newest_on_walk_newest_x[OF in_vertsI] ulca_eq by blast
  note newest_on_walk_valid_union[OF this \<open>unions ! nat newest_y = (ay, by)\<close>]
  with newest_y.prems show ?case
    by (intro domintro newest_y.IH) assumption+
qed simp_all

lemma (in ufe_invars) explain_symmetric:
  assumes "explain_dom l au unions (x, y)"
  assumes "x < length l" "y < length l"
  shows "explain l au unions x y = explain l au unions y x"
  using assms
proof(induction rule: explain_pinduct)
  case (newest_x x y ulca newest_x newest_y ax bx)
  note explain_dom = this(1) explain_dom_symmetric[OF this(1) newest_x.prems]
  note explain_psimps = this[THEN explain.psimps]

  from newest_x interpret ufe_tree l unions au x
    by (unfold_locales) blast

  from newest_x neq_find_newest_on_path have "newest_x \<noteq> newest_y"
    using in_vertsI by metis
  with newest_x have "newest_x > newest_y"
    by simp

  with newest_x newest_on_walk_newest_x[OF in_vertsI] obtain px where
    "newest_on_walk newest_x ulca px x" "ulca \<noteq> x"
    by (metis \<open>newest_y < newest_x\<close>)
  note valid_union = newest_on_walk_valid_union[OF this]

  from newest_x \<open>newest_x \<noteq> newest_y\<close> show ?case
    unfolding explain_psimps using ufa_lca_symmetric[of l x y]
    by (auto simp: valid_union)
next
  case (newest_y x y ulca newest_x newest_y ay "by")
  note explain_dom = this(1) explain_dom_symmetric[OF this(1) newest_y.prems]
  note explain_psimps = this[THEN explain.psimps]

  from newest_y interpret ufe_tree l unions au y
    by (unfold_locales) blast

  from newest_y newest_on_walk_newest_x[OF in_vertsI] obtain py where
    "newest_on_walk newest_y ulca py y" "ulca \<noteq> y"
    using ufa_lca_symmetric[of l x y] by blast
  note valid_union = newest_on_walk_valid_union[OF this]

  from newest_y show ?case
    unfolding explain_psimps using ufa_lca_symmetric[of l x y]
    by (auto simp: valid_union)
qed (simp_all add: explain.psimps)

end