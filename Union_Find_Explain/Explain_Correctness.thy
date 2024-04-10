section \<open>Correctness proofs for Explain\<close>
theory Explain_Correctness
  imports Helper_Functions
begin

lemma (in union_find_explain_ds) neq_find_newest_on_path_ufa_lca_if_neq:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "x \<noteq> y"
  defines "ulca \<equiv> ufa_lca (uf_ds ufe_ds) x y"
  shows "find_newest_on_walk ufe_ds ulca x \<noteq> find_newest_on_walk ufe_ds ulca y"
proof -
  from assms interpret ufe_tree where x = x
    by unfold_locales
  from assms have "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
    using \<alpha>_rep_of in_vertsI by blast
  note lca_ulca = lca_ufa_lca[OF x_in_verts this]
  then obtain px py where
    px: "awalk ulca px x" and py: "awalk ulca py y"
    unfolding ulca_def by (meson lca_reachableD reachable_awalk)
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
    moreover note ps[unfolded ulca_def] = px py
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

context union_find_explain_ds
begin

lemma explain_symmetric:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "explain (unions ufe_ds) x y = explain (unions ufe_ds) y x"
  using assms
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init
  then show ?case by simp
next
  case (ufe_union ufe_ds a b)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast

  from ufe_union.prems(1,2) have
    x_in_Field_\<alpha>: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    using ufe_union.hyps(2-4) by force+

  from x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3) show ?case
    unfolding ufe_union_sel_if_rep_of_neq(1,3)[OF ufe_union.hyps(4)]
    unfolding explain.simps Let_def ufe_ds.ufe_ds_eq_ufe_unions[symmetric]
    by (cases rule: ufe_ds.rep_of_union_eq_cases)
      (use ufe_union.IH x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.hyps in \<open>force+\<close>)
qed

lemma explain_induct[consumes 3,
    case_names ufe_init symmetric ufe_union_if_newest_x ufe_union_if_rep_of_neq]:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes ufe_init: "\<And>x. x \<in> Field (uf_\<alpha> (uf_ds ufe_init)) \<Longrightarrow> P ufe_init x x"
  assumes symmetric: "\<And>ufe_ds x y.
    \<lbrakk> union_find_explain_ds uf_adt au_adt ufe_ds
    ; x \<in> Field (uf_\<alpha> (uf_ds ufe_ds)); y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; \<not> find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x \<ge>
      find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y
    ; P ufe_ds y x
    \<rbrakk> \<Longrightarrow> P ufe_ds x y"
  assumes ufe_union_if_newest_x: "\<And>ufe_ds a b x y.
    \<lbrakk> x \<in> Field (uf_\<alpha> (uf_ds ufe_ds)) ; y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; union_find_explain_ds uf_adt au_adt ufe_ds
    ; a \<in> Field (uf_\<alpha> (uf_ds ufe_ds)); b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds a \<noteq> ufe_rep_of ufe_ds b
    ; find_newest_on_walk (ufe_union ufe_ds a b) (ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y) x \<ge>
      find_newest_on_walk (ufe_union ufe_ds a b) (ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y) y
    ; P ufe_ds x y
    \<rbrakk> \<Longrightarrow> P (ufe_union ufe_ds a b) x y"
  assumes ufe_union_if_rep_of_neq: "\<And>ufe_ds a b x y.
    \<lbrakk> x \<in> Field (uf_\<alpha> (uf_ds ufe_ds)) ; y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y
    ; ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y
    ; union_find_explain_ds uf_adt au_adt ufe_ds
    ; a \<in> Field (uf_\<alpha> (uf_ds ufe_ds)); b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds a \<noteq> ufe_rep_of ufe_ds b
    \<rbrakk> \<Longrightarrow> P (ufe_union ufe_ds a b) x y"
  shows "P ufe_ds x y"
  using assms(1-3)
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init': ufe_init
  with ufe_init show ?case
    using ufp_invar_init.refl_parent_of_iff_refl_rep_of by force
next
  case (ufe_union ufe_ds a b x y)
  then interpret union_find_explain_ds where ufe_ds = ufe_ds
    by blast
  let ?lca = "ufa_lca (uf_ds (ufe_union ufe_ds a b))"

  from ufe_union.prems have
    x_in_Field_\<alpha>: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    using ufe_union.hyps(2-4) by auto

  show ?case
  proof(cases "find_newest_on_walk (ufe_union ufe_ds a b) (?lca x y) x \<ge>
    find_newest_on_walk (ufe_union ufe_ds a b) (?lca x y) y")
    case newest_x: True
    then show ?thesis
    proof(cases "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y")
      case True
      with ufe_union_if_newest_x[OF _ _ _ ufe_union.hyps newest_x] show ?thesis
        using x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.IH by blast
    next
      case False
      note ufe_union_if_rep_of_neq[OF _ _ _ this ufe_union.hyps]
      from this[OF x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3)] show ?thesis
        by assumption
    qed
  next
    case False
    then have
      "find_newest_on_walk (ufe_union ufe_ds a b) (?lca y x) y \<ge>
      find_newest_on_walk (ufe_union ufe_ds a b) (?lca y x) x"
      using ufa_lca_symmetric by simp
    from ufe_union_if_newest_x[OF _ _ _ _ _ _ _ this ufe_union.IH]
    have "P (ufe_union ufe_ds a b) y x"
      using x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3) ufe_union.hyps(2-4)
      using ufe_union_if_rep_of_neq union_find_explain_ds_axioms by metis
    note symmetric[OF _ _ _ _ False this]
    with ufe_union.hyps ufe_union.prems show ?thesis
      using ufe_explain_ds_union by blast
  qed
qed

lemma
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
proof(induction rule: explain_induct)
  case ufe_init
  then show ?case
    by simp
next
  case (symmetric ufe_ds x y)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast
  from symmetric interpret ufe_tree_x: ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales

  note symmetric.IH[unfolded ufa_lca_symmetric[where ?x=y and ?y=x]]
  note IH = this[folded ufe_ds.explain_symmetric[OF symmetric.hyps(2-4)]]

  note neq_find_newest_on_path =
    ufe_ds.neq_find_newest_on_path_ufa_lca_if_neq[OF symmetric.hyps(2-4)]

  let ?lca = "ufa_lca (uf_ds ufe_ds)"
  from symmetric.hyps(2-4) have lca: "ufe_tree_x.lca (?lca x y) x y"
    using ufe_tree_x.lca_ufa_lca
    by (metis ufe_ds.\<alpha>_rep_of ufe_ds.in_vertsI)

  show ?case
  proof(cases "x = y")
    case True
    then show ?thesis
      by simp
  next
    case False
    from lca obtain p where "ufe_tree_x.awalk (?lca x y) p y"
      using ufe_tree_x.lca_reachableD ufe_tree_x.reachable_awalk by blast
    moreover from symmetric.hyps False have "ufa_lca (uf_ds ufe_ds) x y \<noteq> y"
      using less_eq_option_None_is_None neq_find_newest_on_path by fastforce
    moreover from calculation False symmetric.hyps neq_find_newest_on_path obtain p where
      "ufe_tree_x.newest_on_walk (the (find_newest_on_walk ufe_ds (?lca x y) y)) (?lca x y) p y"
      using ufe_tree_x.newest_on_walk_find_newest_on_walk by blast
    ultimately obtain a b where
      eq_prod_a_b: "unions ufe_ds ! the (find_newest_on_walk ufe_ds (?lca x y) y) = (a, b)" and
      a_b_in_Field_\<alpha>: "a \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
      "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x" "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
      using False ufe_tree_x.newest_on_walk_valid_union ufe_tree_x.rep_of_eq_if_newest_on_walk
      by (meson prod.exhaust_sel)
    then have ufe_rep_of_eq:
      "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds a" "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
      using symmetric.hyps(3,4) by metis+

    then have explain_symmetric:
      "explain (unions ufe_ds) y a = explain (unions ufe_ds) a y"
      "explain (unions ufe_ds) b x = explain (unions ufe_ds) x b"
      by (intro ufe_ds.explain_symmetric symmetric.hyps a_b_in_Field_\<alpha> ufe_rep_of_eq)+

    from symmetric.hyps False neq_find_newest_on_path have
      "find_newest_on_walk ufe_ds (?lca x y) x \<le> find_newest_on_walk ufe_ds (?lca x y) y"
      by fastforce
    with symmetric.hyps False a_b_in_Field_\<alpha> show ?thesis
      unfolding IH Let_def eq_prod_a_b
      by (auto simp add: explain_symmetric)
  qed
next
  case (ufe_union_if_newest_x ufe_ds a b x y)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast
  interpret ufe_tree_x: ufe_tree where ufe_ds = ufe_ds and x = x
    by (use ufe_union_if_newest_x.hyps in unfold_locales)

  show ?case
  proof(cases "x = y")
    case True
    then show ?thesis by simp
  next
    case False
    from ufe_union_if_newest_x have unions_ufe_union:
      "unions (ufe_union ufe_ds a b) = unions ufe_ds @ [(a, b)]"
      by simp

    with explain.simps(2) ufe_union_if_newest_x.hyps(3) have explain_ufe_union:
      "explain (unions (ufe_union ufe_ds a b)) x y = explain (unions ufe_ds) x y"
      using unions_ufe_union ufe_ds.ufe_ds_eq_ufe_unions by force

    from ufe_union_if_newest_x.hyps have ufa_lca_union:
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufa_lca (uf_ds ufe_ds) x y"
      using ufe_ds.ufa_lca_union ufe_ds.rep_of_neq_if_rep_of_union_neq
      by (metis (mono_tags, opaque_lifting) uf_ds_ufe_union)

    let ?lca = "ufa_lca (uf_ds ufe_ds)"
    from ufe_union_if_newest_x.hyps(1-3) have "ufe_tree_x.lca (?lca x y) x y"
      using ufe_tree_x.lca_ufa_lca by (metis ufe_ds.\<alpha>_rep_of ufe_ds.in_vertsI)
    then obtain px py where
      x_awalk_lca_x: "ufe_tree_x.awalk (?lca x y) px x" and
      x_awalk_lca_y: "ufe_tree_x.awalk (?lca x y) py y"
      using ufe_tree_x.lca_reachableD ufe_tree_x.reachable_awalk by metis
    with ufe_union_if_newest_x.hyps(5-7) have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x) (?lca x y) px x"
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x) (?lca x y) py y"
      using ufe_tree_x.union_awalk_if_awalk by auto
    note this[THEN ufe_ds.find_newest_on_walk_ufe_union[OF ufe_union_if_newest_x.hyps(5-7)]]
    with x_awalk_lca_x x_awalk_lca_y have find_newest_on_walk_union:
      "find_newest_on_walk (ufe_union ufe_ds a b) (?lca x y) x =
      find_newest_on_walk ufe_ds (?lca x y) x" (is "_ = ?newest_x")
      "find_newest_on_walk (ufe_union ufe_ds a b) (?lca x y) y =
      find_newest_on_walk ufe_ds (?lca x y) y" (is "_ = ?newest_y")
      using ufe_tree_x.awalk_hd_in_verts by auto

    note ufe_ds.neq_find_newest_on_path_ufa_lca_if_neq[OF ufe_union_if_newest_x.hyps(1-3) False]
    with ufe_union_if_newest_x.hyps(8) have
      "find_newest_on_walk ufe_ds (?lca x y) x \<noteq> None"
      unfolding ufa_lca_union find_newest_on_walk_union
      by (metis less_eq_option_None_is_None)
    with False have "?lca x y \<noteq> x"
      using x_awalk_lca_x[THEN ufe_tree_x.find_newest_on_walk_eq_None_iff]
      by simp

    with x_awalk_lca_x have newest_on_walk_newest_x:
      "ufe_tree_x.newest_on_walk (the ?newest_x) (?lca x y) px x"
      using ufe_tree_x.newest_on_walk_find_newest_on_walk by blast
    with \<open>?lca x y \<noteq> x\<close> obtain u v where
      nth_newest_x_eq_prod_u_v: "unions ufe_ds ! the ?newest_x = (u, v)" and
      u_v_in_Field_\<alpha>: "u \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "v \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
      rep_of_u_v:
        "ufe_rep_of ufe_ds u = ufe_rep_of ufe_ds x"
        "ufe_rep_of ufe_ds v = ufe_rep_of ufe_ds x"
      using ufe_tree_x.newest_on_walk_valid_union ufe_tree_x.rep_of_eq_if_newest_on_walk
      by (metis prod.collapse)  
    with ufe_union_if_newest_x.hyps(3) have explain_union_u_v:
      "explain (unions (ufe_union ufe_ds a b)) x u = explain (unions ufe_ds) x u"
      "explain (unions (ufe_union ufe_ds a b)) v y = explain (unions ufe_ds) v y"
      unfolding unions_ufe_union
      by (simp_all add: ufe_ds.ufe_ds_eq_ufe_unions[symmetric])

    from newest_on_walk_newest_x \<open>?lca x y \<noteq> x\<close> have
      "the ?newest_x < length (unions ufe_ds)"
      using ufe_tree_x.newest_on_walk_lt_length_unions by blast
    then have nth_unions_union:
      "unions (ufe_union ufe_ds a b) ! the ?newest_x = unions ufe_ds ! the ?newest_x"
      unfolding unions_ufe_union by simp

    from False ufe_union_if_newest_x.hyps(8) show ?thesis
      unfolding explain_ufe_union ufa_lca_union Let_def
      unfolding find_newest_on_walk_union nth_unions_union
      by (simp add: nth_newest_x_eq_prod_u_v explain_union_u_v ufe_union_if_newest_x.IH)
  qed
next
  case (ufe_union_if_rep_of_neq ufe_ds a b x y)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast

  from ufe_union_if_rep_of_neq have "x \<noteq> y"
    by blast

  from ufe_union_if_rep_of_neq.hyps ufe_ds.ufa_lca_union have ufa_lca_union:
    "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b" (is "_ = ?rep_b")
    by simp

  from ufe_union_if_rep_of_neq.hyps interpret ufe_ds_union: union_find_explain_ds
    where ufe_ds = "ufe_union ufe_ds a b"
    by (intro ufe_ds.ufe_explain_ds_union)
  interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and x = b
    using \<open>b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))\<close>
    by unfold_locales force

  from ufe_union_if_rep_of_neq.hyps have
    x_in_Field_\<alpha>_union: "x \<in> Field (uf_\<alpha> (uf_ds (ufe_union ufe_ds a b)))" and
    y_in_Field_\<alpha>_union: "y \<in> Field (uf_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    by auto
  with ufe_union_if_rep_of_neq.hyps have
    "x \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) b)"
    "y \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) b)"
    by (safe intro!: ufe_tree_union.in_verts_if_rep_of_eq)
      (auto simp: uf_ds_ufe_union ufe_ds.rep_of_union split: if_splits)

  note ufe_tree_union.lca_ufa_lca[OF this]
  with ufa_lca_union have "ufe_tree_union.lca ?rep_b x y"
    by simp
  then obtain px py where
    "ufe_tree_union.awalk ?rep_b px x"
    "ufe_tree_union.awalk ?rep_b py y"
    by (meson ufe_tree_union.lca_reachableD ufe_tree_union.reachable_awalk)

  note this[THEN ufe_tree_union.find_newest_on_walk_lt_Some_length_unions]
  then have newest_leq_Some_length_unions:
    "find_newest_on_walk (ufe_union ufe_ds a b) ?rep_b x \<le> Some (length (unions ufe_ds))"
      (is "?newest_x \<le> _")
    "find_newest_on_walk (ufe_union ufe_ds a b) ?rep_b y \<le> Some (length (unions ufe_ds))"
      (is "?newest_y \<le> _")
    unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union_if_rep_of_neq.hyps(8)]
    by (cases ?newest_x; cases ?newest_y; simp)+

  note ufe_ds_union.neq_find_newest_on_path_ufa_lca_if_neq[
    OF x_in_Field_\<alpha>_union y_in_Field_\<alpha>_union ufe_union_if_rep_of_neq.hyps(3)]
  then have newest_x_neq_newest_y: "?newest_x \<noteq> ?newest_y" if "x \<noteq> y"
    using that ufa_lca_union by force

  note ufe_union_if_rep_of_neq.hyps(1-3,6-8) ufe_union_if_rep_of_neq.prems
  from this[unfolded ufe_union_sel_if_rep_of_neq[OF ufe_union_if_rep_of_neq.hyps(8)]] show ?case
  proof(cases rule: ufe_ds.rep_of_union_eq_cases)
    case 2
    with \<open>ufe_tree_union.awalk ?rep_b px x\<close> have newest_x_eq:
      "?newest_x = Some (length (unions ufe_ds))"
      using ufe_union_if_rep_of_neq.hyps(6,7)
      by (metis ufe_ds.find_newest_on_walk_ufe_union ufe_ds.rep_of_rep_of)
    with 2 newest_leq_Some_length_unions have "?newest_x \<ge> ?newest_y"
      by fastforce

    with 2 \<open>x \<noteq> y\<close> show ?thesis
      using newest_x_eq ufa_lca_union ufe_ds.ufe_ds_eq_ufe_unions by auto
  next
    case 3
    with \<open>ufe_tree_union.awalk ?rep_b py y\<close> have newest_y_eq:
      "?newest_y = Some (length (unions ufe_ds))"
      using ufe_union_if_rep_of_neq.hyps(6,7)
      by (metis ufe_ds.find_newest_on_walk_ufe_union ufe_ds.rep_of_rep_of)
    moreover note ufe_ds_union.neq_find_newest_on_path_ufa_lca_if_neq[
        OF x_in_Field_\<alpha>_union y_in_Field_\<alpha>_union ufe_union_if_rep_of_neq.hyps(3)]
    with \<open>x \<noteq> y\<close> have "?newest_x \<noteq> ?newest_y"
      using ufa_lca_union by simp
    ultimately have "\<not> ?newest_x \<ge> ?newest_y"
      using 3 newest_leq_Some_length_unions by auto

    with 3 \<open>x \<noteq> y\<close> show ?thesis
      using newest_y_eq ufa_lca_union ufe_ds.ufe_ds_eq_ufe_unions by auto
  qed (use ufe_union_if_rep_of_neq in blast)
qed


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

lemma (in union_find_explain_ds) explain_sound:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "u \<in> explain (unions ufe_ds) x y"
  shows "u \<in> set (unions ufe_ds)"
  using assms
proof(induction arbitrary: x y u rule: ufe_ds_induct)
  case ufe_init
  then show ?case by simp
next
  case (ufe_union ufe_ds x y a b)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast

  from ufe_union.prems ufe_union.hyps(2-4) show ?case
    unfolding ufe_union_sel_if_rep_of_neq(3)[OF ufe_union.hyps(4)]
    unfolding explain.simps[unfolded Let_def, folded ufe_ds.ufe_ds_eq_ufe_unions]
    by (auto simp: ufe_union.IH split: if_splits)
qed

lemma symcl_Un[simp]:
  "symcl (A \<union> B) = symcl A \<union> symcl B"
  unfolding symcl_def by auto

lemma symcl_insert:
  "symcl (insert x A) = insert x (insert (case x of (a, b) \<Rightarrow> (b, a)) (symcl A))"
  unfolding symcl_def by auto

lemma (in union_find_explain_ds) explain_complete:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "(x, y) \<in> ((explain (unions ufe_ds) x y)\<^sup>s)\<^sup>*"
  using assms
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init
  then have "x = y"
    using ufp_invar_init.refl_parent_of_iff_refl_rep_of by auto
  then show ?case
    by simp
next
  case (ufe_union ufe_ds a b x y)
  then interpret ufe_ds: union_find_explain_ds where ufe_ds = ufe_ds
    by blast

  from ufe_union.prems(1,2) have
    x_in_Field_\<alpha>: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    using ufe_union.hyps(2-4) by force+

  note x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3) ufe_union.hyps(2-4)
  from this[unfolded ufe_union_sel_if_rep_of_neq(1,3)[OF ufe_union.hyps(4)]] show ?case
  proof (cases rule: ufe_ds.rep_of_union_eq_cases)
    case 1
    with x_in_Field_\<alpha> y_in_Field_\<alpha> show ?thesis
      unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union.hyps(4)]
      unfolding explain.simps Let_def ufe_ds.ufe_ds_eq_ufe_unions[symmetric]
      by (auto simp: ufe_union.IH)
  next
    case 2
    with ufe_union.IH have
      "(x, a) \<in> ((explain (unions ufe_ds) x a)\<^sup>s)\<^sup>*" (is "_ \<in> ?explain_x_a\<^sup>*")
      "(b, y) \<in> ((explain (unions ufe_ds) b y)\<^sup>s)\<^sup>*" (is "_ \<in> ?explain_b_y\<^sup>*")
      using x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.hyps(2,3) by metis+
    then have
      "(x, y) \<in> (insert (a, b) (insert (b, a) (?explain_x_a\<^sup>* \<union> ?explain_b_y\<^sup>*)))\<^sup>*"
      by (meson UnCI insertCI rtrancl.simps)
    also have "\<dots> = (insert (a, b) (insert (b, a) (?explain_x_a \<union> ?explain_b_y)))\<^sup>*"
      using rtrancl_Un_rtrancl
      by (metis (no_types) Un_insert_left Un_insert_right rtrancl_idemp)
    finally show ?thesis
      using 2
      unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union.hyps(4)]
      unfolding explain.simps Let_def ufe_ds.ufe_ds_eq_ufe_unions[symmetric]   
      by (simp add: symcl_insert)
  next
    case 3
    with ufe_union.IH have
      "(x, b) \<in> ((explain (unions ufe_ds) x b)\<^sup>s)\<^sup>*" (is "_ \<in> ?explain_x_b\<^sup>*")
      "(a, y) \<in> ((explain (unions ufe_ds) a y)\<^sup>s)\<^sup>*" (is "_ \<in> ?explain_a_y\<^sup>*")
      using x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.hyps(2,3) by metis+
    then have
      "(x, y) \<in> (insert (a, b) (insert (b, a) (?explain_x_b\<^sup>* \<union> ?explain_a_y\<^sup>*)))\<^sup>*"
      by (meson UnCI insertCI rtrancl.simps)
    also have "\<dots> = (insert (a, b) (insert (b, a) (?explain_x_b \<union> ?explain_a_y)))\<^sup>*"
      using rtrancl_Un_rtrancl
      by (metis (no_types) Un_insert_left Un_insert_right rtrancl_idemp)
    finally show ?thesis
      using 3
      unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union.hyps(4)]
      unfolding explain.simps Let_def ufe_ds.ufe_ds_eq_ufe_unions[symmetric]   
      by (simp add: symcl_insert)
  qed
qed

end
