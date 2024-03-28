section \<open>Correctness proofs for Explain\<close>
theory Explain_Correctness
  imports Helper_Functions
begin

lemma (in ufe_tree) neq_find_newest_on_path:
  assumes "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)" "x \<noteq> y"
  assumes ulca_eq: "ulca = ufa_lca (uf_ds ufe_ds) x y"
  shows "find_newest_on_walk ufe_ds ulca x \<noteq>
    find_newest_on_walk ufe_ds ulca y"
proof -
  note lca_ulca = lca_ufa_lca[OF x_in_verts \<open>y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)\<close>]
  with ulca_eq obtain px py where
    px: "awalk ulca px x" and py: "awalk ulca py y"
    by (meson lca_reachableD reachable_awalk)
  note find_newest_on_walk_dom = this[THEN find_newest_on_walk_dom]
  note find_newest_on_walk_psimps = this[THEN find_newest_on_walk.psimps]
  consider (lca_x) "x = ulca" | (lca_y) "y = ulca" | (not_lca) "ulca \<noteq> x" "ulca \<noteq> y"
    using \<open>x \<noteq> y\<close> by auto
  then show ?thesis
  proof cases
    case lca_x
    then have "find_newest_on_walk ufe_ds ulca x = None"
      using find_newest_on_walk_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_x have "find_newest_on_walk ufe_ds ulca y \<noteq> None"
      using find_newest_on_walk_eq_Max_au_of[OF py] by blast      
    ultimately show ?thesis
      by force
  next
    case lca_y
    then have "find_newest_on_walk ufe_ds ulca y = None"
      using find_newest_on_walk_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_y have "find_newest_on_walk ufe_ds ulca x \<noteq> None"
      using find_newest_on_walk_eq_Max_au_of[OF px] by blast      
    ultimately show ?thesis
      by force
  next
    case not_lca
    moreover
    from not_lca px py have "px \<noteq> []" "py \<noteq> []"
      using awalk_empty_ends px by blast+
    from not_lca px py obtain ix iy where
      ix: "ix \<in> set px" "find_newest_on_walk ufe_ds ulca x = Some (au_of ix)" and
      iy: "iy \<in> set py" "find_newest_on_walk ufe_ds ulca y = Some (au_of iy)"
      using newest_on_walkE[unfolded newest_on_walk_def]
      by (simp add: find_newest_on_walk_eq_Max_au_of) metis
    moreover note ps[unfolded ulca_eq] = px py
    note disjoint_awalk_if_awalk_lca[OF lca_ulca \<open>x \<noteq> y\<close> this]
    with ix iy have "ix \<noteq> iy"
      by blast
    moreover from px py ix iy have
      "ix \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)" "iy \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
      by blast+
    ultimately show ?thesis
      using inj_on_au_of_arcs ix iy by (fastforce dest: inj_onD)
  qed
qed

lemma (in ufe_tree) newest_on_walk_newest_x:
  assumes "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
  assumes "x \<noteq> y"
  assumes ulca_eq: "ulca = ufa_lca (uf_ds ufe_ds) x y"
  assumes "find_newest_on_walk ufe_ds ulca x = newest_x"
  assumes "find_newest_on_walk ufe_ds ulca y = newest_y"
  assumes "newest_x > newest_y"
  obtains px where "newest_on_walk (the newest_x) ulca px x" "ulca \<noteq> x"
proof -
  note lca_ulca = lca_ufa_lca[OF x_in_verts \<open>y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)\<close>]
  with ulca_eq obtain px py where
    px: "awalk ulca px x" and py: "awalk ulca py y"
    by (meson lca_reachableD reachable_awalk)
  with assms have "newest_on_walk (the newest_x) ulca px x" if "ulca \<noteq> x"
    using that newest_on_walk_find_newest_on_walk by metis

  moreover note px py
  note find_newest_on_walk_dom = this[THEN find_newest_on_walk_dom]
  note find_newest_on_walk_psimps = this[THEN find_newest_on_walk.psimps]
  have "ulca \<noteq> x"
  proof
    assume "ulca = x"
    with \<open>x \<noteq> y\<close> py have "ufe_parent_of ufe_ds y \<noteq> y"
      using awalk_and_parent_of_reflD(1) by blast
    with \<open>ulca = x\<close> assms show False
      by simp
  qed

  ultimately show ?thesis
    using that by blast
qed


lemma (in union_find_explain_ds)
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows
    "explain (unions ufe_ds) x y =
    (if x = y then {}
    else 
      let
        lca = ufa_lca (uf_ds ufe_ds) x y;
        newest_x = find_newest_on_walk ufe_ds lca x;
        newest_y = find_newest_on_walk ufe_ds lca y
      in
        if newest_x \<ge> newest_y then
          let (ax, bx) = unions ufe_ds ! the newest_x
          in {(ax, bx)} \<union> explain (unions ufe_ds) x ax \<union> explain (unions ufe_ds) bx y
        else
          let (ay, by) = unions ufe_ds ! the newest_y
          in {(ay, by)} \<union> explain (unions ufe_ds) x by \<union> explain (unions ufe_ds) ay y)"
  using assms
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init
  with assms have "ufe_rep_of ufe_init x = ufe_rep_of ufe_init y \<longleftrightarrow> x = y"
    unfolding ufe_init_sel
    using ufp_invar_init.refl_parent_of_iff_refl_rep_of by force
  with ufe_init show ?case
    by simp
next
  case (ufe_union ufe_ds a b)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast
  from ufe_union have unions_ufe_union:
    "unions (ufe_union ufe_ds a b) = unions ufe_ds @ [(a, b)]"
    by simp
  have "unions ufe_ds @ [(a, b)] \<noteq> []"
    by blast
  have butlast_unions_append:
    "butlast (unions ufe_ds @ [(a, b)]) = unions ufe_ds"
    by simp
  have last_unions_append:
    "last (unions ufe_ds @ [(a, b)]) = (a, b)"
    by simp
  note explain.simps(2)[OF \<open>unions ufe_ds @ [(a, b)] \<noteq> []\<close>]
  note this[unfolded butlast_unions_append last_unions_append]
  note explain_simp = this[folded ufe_ds.ufe_ds_eq_ufe_unions]

  from ufe_union.prems(1,2) have
    x_in_Field_\<alpha>: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    using ufe_union.hyps(2-4) by force+
  from ufe_union.prems(3) have
    "uf_rep_of (uf_union (uf_ds ufe_ds) a b) x = uf_rep_of (uf_union (uf_ds ufe_ds) a b) y"
    using ufe_union.hyps(4) by simp
  note ufa_lca_union = 
    ufe_ds.ufa_lca_union[OF ufe_union.hyps(2-4) x_in_Field_\<alpha> y_in_Field_\<alpha> this]

  note find_newest_on_walk_ufe_union =
    ufe_ds.find_newest_on_walk_ufe_union[OF ufe_union.hyps(2-4)]

  show ?case
  proof(cases "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y")
    case True
    then have "explain (unions (ufe_union ufe_ds a b)) x y = explain (unions ufe_ds) x y"
      unfolding unions_ufe_union explain_simp by simp

    then show ?thesis sorry
  next
    case False

      
    from False ufa_lca_union have ufa_lca_union:
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b"
      using ufe_union.hyps(4) by auto
    show ?thesis
      unfolding ufa_lca_union
      sorry
  qed
qed


lemma (in union_find_explain_ds) explain_dom_symmetric:
  assumes "explain_dom ufe_ds (x, y)"
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "explain_dom ufe_ds (y, x)"
  using assms
proof(induction rule: explain_pinduct)
  case (newest_x x y ulca newest_x newest_y ax bx)
  then interpret ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales
  from newest_x neq_find_newest_on_path have "newest_x \<noteq> newest_y"
    using in_vertsI using \<alpha>_rep_of by blast
  with newest_x.hyps have "newest_y < newest_x"
    using newest_x.hyps(7) by fastforce
  from newest_x.hyps(4) have ulca_eq: "ulca = ufa_lca (uf_ds ufe_ds) y x"
    using ufa_lca_symmetric by simp
  note hyps = newest_x.hyps(2,3)[symmetric] ulca_eq newest_x.hyps(6,5)
    \<open>newest_y < newest_x\<close> newest_x.hyps(8)
  note domintro = explain_newest_y_domintro[OF hyps]

  with newest_x \<open>newest_y < newest_x\<close> obtain px where
    "newest_on_walk (the newest_x) ulca px x" "ulca \<noteq> x"
    using newest_on_walk_newest_x[OF in_vertsI] \<alpha>_rep_of by blast
    
  note newest_on_walk_valid_union[OF this \<open>unions ufe_ds ! the newest_x = (ax, bx)\<close>]
  with newest_x.prems show ?case
    by (intro domintro newest_x.IH) assumption+
next
  case (newest_y x y ulca newest_x newest_y ay "by")
  then interpret ufe_tree where x = y
    by (unfold_locales) blast
  from newest_y.hyps(4) have ulca_eq: "ulca = ufa_lca (uf_ds ufe_ds) y x"
    using ufa_lca_symmetric by simp
  from newest_y have "newest_x \<le> newest_y"
    by simp
  note hyps = newest_y.hyps(2,3)[symmetric] ulca_eq newest_y.hyps(6,5)
    \<open>newest_x \<le> newest_y\<close> newest_y.hyps(8)
  note domintro = explain_newest_x_domintro[OF hyps]

  with newest_y \<open>newest_y > newest_x\<close> obtain py where
    "newest_on_walk (the newest_y) ulca py y" "ulca \<noteq> y"
    using newest_on_walk_newest_x[OF in_vertsI] ulca_eq \<alpha>_rep_of by metis
  note newest_on_walk_valid_union[OF this \<open>unions ufe_ds ! the newest_y = (ay, by)\<close>]
  with newest_y.prems show ?case
    by (intro domintro newest_y.IH) assumption+
qed simp_all

lemma (in union_find_explain_ds) explain_symmetric:
  assumes "explain_dom ufe_ds (x, y)"
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "explain ufe_ds x y = explain ufe_ds y x"
  using assms
proof(induction rule: explain_pinduct)
  case (newest_x x y ulca newest_x newest_y ax bx)
  note explain_dom = this(1) explain_dom_symmetric[OF this(1) newest_x.prems]
  note explain_psimps = this[THEN explain.psimps]

  from newest_x interpret ufe_tree where ufe_ds = ufe_ds and x = x
    by (unfold_locales) blast

  from newest_x neq_find_newest_on_path have "newest_x \<noteq> newest_y"
    using in_vertsI \<alpha>_rep_of by metis
  with newest_x have "newest_x > newest_y"
    by simp

  with newest_x newest_on_walk_newest_x[OF in_vertsI] obtain px where
    "newest_on_walk (the newest_x) ulca px x" "ulca \<noteq> x"
    using \<alpha>_rep_of by (metis \<open>newest_y < newest_x\<close>)
  note valid_union = newest_on_walk_valid_union[OF this]

  from newest_x \<open>newest_x \<noteq> newest_y\<close> show ?case
    unfolding explain_psimps
    using valid_union ufa_lca_symmetric[of "uf_ds ufe_ds" x y]
    by auto
next
  case (newest_y x y ulca newest_x newest_y ay "by")
  note explain_dom = this(1) explain_dom_symmetric[OF this(1) newest_y.prems]
  note explain_psimps = this[THEN explain.psimps]
  from newest_y have explain_psimps:
    "explain ufe_ds x y
      = {(ay, by)} \<union> explain ufe_ds x by \<union> explain ufe_ds ay y"
    "explain ufe_ds y x
      = {(ay, by)} \<union> explain ufe_ds y ay \<union> explain ufe_ds by x"
    unfolding explain_psimps ufa_lca_symmetric[of "uf_ds ufe_ds" y x]
    by (simp_all add: Let_def less_le_not_le split: prod.splits)

  from newest_y interpret ufe_tree where ufe_ds = ufe_ds and x = x
    by (unfold_locales) blast

  note newest_on_walk_newest_x[OF in_vertsI _ _ _ newest_y.hyps(5)[symmetric]]
  with newest_y obtain py where
    "newest_on_walk (the newest_y) ulca py y" "ulca \<noteq> y"
    using ufa_lca_symmetric[of "uf_ds ufe_ds" x y] \<alpha>_rep_of
    sorry
  note valid_union = newest_on_walk_valid_union[OF this]
  then have "ay \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "by \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    using newest_y by blast+
  with newest_y have
    "explain ufe_ds x by = explain ufe_ds by x"
    "explain ufe_ds ay y = explain ufe_ds y ay"
    by blast+
  then show ?case
    unfolding explain_psimps by blast
qed (simp_all add: explain.psimps)

lemma (in union_find_explain_invars)
  assumes "explain_dom ufe_ds (x, y)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "explain_dom (ufe_union ufe_ds u v) (x, y)"
  oops

end