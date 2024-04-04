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

lemma (in union_find_parent_unions) rep_of_union_eq_cases:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_union uf a b) x = uf_rep_of (uf_union uf a b) y"
  assumes "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of uf a \<noteq> uf_rep_of uf b"
  obtains
    "uf_rep_of uf x = uf_rep_of uf y" |
    "uf_rep_of uf x \<noteq> uf_rep_of uf y"
    "uf_rep_of uf x = uf_rep_of uf a" "uf_rep_of uf y = uf_rep_of uf b" |
    "uf_rep_of uf x \<noteq> uf_rep_of uf y"
    "uf_rep_of uf x = uf_rep_of uf b" "uf_rep_of uf y = uf_rep_of uf a"
  using assms by (metis rep_of_union)

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

  have unions_ufe_union:
    "unions (ufe_union ufe_ds a b) \<noteq> []"
    "butlast (unions (ufe_union ufe_ds a b)) = unions ufe_ds"
    "last (unions (ufe_union ufe_ds a b)) = (a, b)"
    by (simp_all add: ufe_union.hyps(4))
  note explain_simp = explain.simps(2)[OF this(1)]

  from ufe_union x_in_Field_\<alpha> y_in_Field_\<alpha> have
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds b \<or> ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds b"
    if "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    using that by (metis uf_ds_ufe_union ufe_ds.rep_of_union)
  from x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3) ufe_union.hyps(2,3,4) show ?case
    unfolding ufe_union_sel_if_rep_of_neq(1)[OF ufe_union.hyps(4)]
    unfolding explain_simp unions_ufe_union ufe_ds.ufe_ds_eq_ufe_unions[symmetric]
    using ufe_union.hyps x_in_Field_\<alpha> y_in_Field_\<alpha>
    by (cases rule: ufe_ds.rep_of_union_eq_cases) (auto simp: ufe_union.IH)
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
      from ufe_union_if_rep_of_neq[OF x_in_Field_\<alpha> y_in_Field_\<alpha> this ufe_union.hyps] show ?thesis
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
      using ufe_union_if_rep_of_neq union_find_explain_ds_axioms by blast
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
    then obtain px where x_awalk_lca:
      "ufe_tree_x.awalk (?lca x y) px x"
      using ufe_tree_x.lca_reachableD ufe_tree_x.reachable_awalk by blast
    with ufe_union_if_newest_x.hyps(5-7) have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x) (?lca x y) px x"
      using ufe_tree_x.union_awalk_if_awalk
      by auto
    note ufe_ds.find_newest_on_walk_ufe_union[OF ufe_union_if_newest_x.hyps(5-7) this]
    with x_awalk_lca have find_newest_on_walk_union:
      "find_newest_on_walk (ufe_union ufe_ds a b) (?lca x y) x =
      find_newest_on_walk ufe_ds (?lca x y) x" (is "_ = ?newest_x")
      using ufe_tree_x.awalk_hd_in_verts by auto

    from False ufe_union_if_newest_x.hyps(8) have "?lca x y \<noteq> x"
      using x_awalk_lca[THEN ufe_tree_x.find_newest_on_walk_eq_None_iff]
      sorry

      with x_awalk_lca have newest_on_walk_newest_x:
        "ufe_tree_x.newest_on_walk (the ?newest_x) (?lca x y) px x"
        using ufe_tree_x.newest_on_walk_find_newest_on_walk by blast
      with \<open>?lca x y \<noteq> x\<close> have
        "the ?newest_x < length (unions ufe_ds)"
        using ufe_tree_x.newest_on_walk_lt_length_unions by blast
      then have nth_unions_union:
        "unions (ufe_union ufe_ds a b) ! the ?newest_x =
        unions ufe_ds ! the ?newest_x"
        unfolding unions_ufe_union by simp

      obtain u v where uv: "unions ufe_ds ! the ?newest_x = (u, v)"
        by force
      with \<open>?lca x y \<noteq> x\<close> newest_on_walk_newest_x have
        "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds u" "ufe_rep_of ufe_ds v = ufe_rep_of ufe_ds y"
        using ufe_tree_x.rep_of_eq_if_newest_on_walk  ufe_union_if_newest_x.hyps(3)
        by force+

    from ufe_union_if_newest_x.hyps(8) show ?thesis
      unfolding explain_ufe_union ufa_lca_union
      apply (subst explain.simps(2)[unfolded Let_def])
      defer
      apply (simp add: find_newest_on_walk_union nth_unions_union)
      sledgehammer
      apply (simp_all add: ufa_lca_union)



  note explain.simps(2)[OF \<open>unions (ufe_union ufe_ds a b) \<noteq> []\<close>]
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

  note find_newest_on_walk_union =
    ufe_ds.find_newest_on_walk_ufe_union[OF ufe_union.hyps(2-4)]

  show ?case
  proof(cases "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y")
    case rep_of_eq: True
    then have explain_union:
      "explain (unions (ufe_union ufe_ds a b)) x y = explain (unions ufe_ds) x y"
      unfolding explain_simp by simp

    from rep_of_eq ufa_lca_union have ufa_lca_union:
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufa_lca (uf_ds ufe_ds) x y" (is "_ = ?lca")
      using ufe_union.hyps(4) by fastforce

    interpret ufe_tree_x: ufe_tree where ufe_ds = ufe_ds and x = x
      by (use x_in_Field_\<alpha> in unfold_locales)

    from rep_of_eq y_in_Field_\<alpha> have "ufe_tree_x.lca ?lca x y"
      using ufe_ds.\<alpha>_rep_of ufe_ds.in_vertsI
      by (intro ufe_tree_x.lca_ufa_lca) blast+
    then obtain px py where x_awalk_lca:
      "ufe_tree_x.awalk ?lca px x" "ufe_tree_x.awalk ?lca py y"
      by (meson ufe_tree_x.lca_reachableD ufe_tree_x.reachable_awalk)
    with rep_of_eq have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x) ?lca px x"
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x) ?lca py y"
      using ufe_tree_x.union_awalk_if_awalk ufe_union.hyps(2-4) by auto
    from this[THEN find_newest_on_walk_union] rep_of_eq have find_newest_on_walk_union:
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca x =
        find_newest_on_walk ufe_ds ?lca x"
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca y =
        find_newest_on_walk ufe_ds ?lca y"
      using \<open>ufe_tree_x.awalk ?lca py y\<close> by fastforce+

    consider
      (eq) "x = y" |
      (newest_x) "x \<noteq> y" "find_newest_on_walk ufe_ds ?lca x \<ge> find_newest_on_walk ufe_ds ?lca y" |
      (newest_y) "x \<noteq> y" "\<not> find_newest_on_walk ufe_ds ?lca x \<ge> find_newest_on_walk ufe_ds ?lca y"
      by fastforce
    then show ?thesis
    proof cases
      case eq
      then show ?thesis
        by simp
    next
      case newest_x
      then have "?lca \<noteq> x"
        using x_awalk_lca[THEN ufe_tree_x.find_newest_on_walk_eq_None_iff]
        by force
      with x_awalk_lca have newest_on_walk_newest_x:
        "ufe_tree_x.newest_on_walk (the (find_newest_on_walk ufe_ds ?lca x)) ?lca px x"
        (is "ufe_tree_x.newest_on_walk ?newest_x _ _ _")
        using ufe_tree_x.newest_on_walk_find_newest_on_walk by blast
      with \<open>?lca \<noteq> x\<close> have
        "the (find_newest_on_walk ufe_ds ?lca x) < length (unions ufe_ds)"
        using ufe_tree_x.newest_on_walk_lt_length_unions by blast
      then have nth_unions_union:
        "unions (ufe_union ufe_ds a b) ! the (find_newest_on_walk ufe_ds ?lca x) =
        unions ufe_ds ! the (find_newest_on_walk ufe_ds ?lca x)"
        unfolding unions_ufe_union by simp

      obtain u v where uv: "unions ufe_ds ! ?newest_x = (u, v)"
        by force
      then have
        "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds u" "ufe_rep_of ufe_ds v = ufe_rep_of ufe_ds y"
      proof -
        have "ufe_rep_of ufe_ds (ufa_lca (uf_ds ufe_ds) x y) = ufe_rep_of ufe_ds x"
          using ufe_tree_x.rep_of_ufa_lca x_awalk_lca(2) by blast
        note ufe_tree_x.rep_of_eq_if_newest_on_walk[
            OF newest_on_walk_newest_x \<open>?lca \<noteq> x\<close> uv, unfolded this]
        with rep_of_eq show
          "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds u" "ufe_rep_of ufe_ds v = ufe_rep_of ufe_ds y"
          by metis+
      qed
      then have
        "explain (unions (ufe_union ufe_ds a b)) x u = explain (unions ufe_ds) x u"
        "explain (unions (ufe_union ufe_ds a b)) v y = explain (unions ufe_ds) v y"
        by (simp_all add: explain_simp)
      with newest_x uv show ?thesis
        unfolding explain_union ufe_union.IH[OF x_in_Field_\<alpha> y_in_Field_\<alpha> rep_of_eq]
        unfolding ufa_lca_union Let_def find_newest_on_walk_union nth_unions_union
        by simp
    next
      case newest_y
      then have "?lca \<noteq> y"
        using x_awalk_lca[THEN ufe_tree_x.find_newest_on_walk_eq_None_iff]
        by force
      with x_awalk_lca have newest_on_walk_newest_x:
        "ufe_tree_x.newest_on_walk (the (find_newest_on_walk ufe_ds ?lca y)) ?lca py y"
        (is "ufe_tree_x.newest_on_walk ?newest_y _ _ _")
        using ufe_tree_x.newest_on_walk_find_newest_on_walk by blast
      with \<open>?lca \<noteq> y\<close> have
        "the (find_newest_on_walk ufe_ds ?lca y) < length (unions ufe_ds)"
        using ufe_tree_x.newest_on_walk_lt_length_unions by blast
      then have nth_unions_union:
        "unions (ufe_union ufe_ds a b) ! the (find_newest_on_walk ufe_ds ?lca y) =
        unions ufe_ds ! the (find_newest_on_walk ufe_ds ?lca y)"
        unfolding unions_ufe_union by simp

      obtain u v where uv: "unions ufe_ds ! ?newest_y = (u, v)"
        by force
      then have
        "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds v" "ufe_rep_of ufe_ds u = ufe_rep_of ufe_ds y"
      proof -
        have "ufe_rep_of ufe_ds (ufa_lca (uf_ds ufe_ds) x y) = ufe_rep_of ufe_ds x"
          using ufe_tree_x.rep_of_ufa_lca x_awalk_lca(2) by blast
        note ufe_tree_x.rep_of_eq_if_newest_on_walk[
            OF newest_on_walk_newest_x \<open>?lca \<noteq> y\<close> uv, unfolded this]
        with rep_of_eq show
          "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds v" "ufe_rep_of ufe_ds u = ufe_rep_of ufe_ds y"
          by metis+
      qed
      then have
        "explain (unions (ufe_union ufe_ds a b)) x v = explain (unions ufe_ds) x v"
        "explain (unions (ufe_union ufe_ds a b)) u y = explain (unions ufe_ds) u y"
        by (simp_all add: explain_simp)
      with newest_y uv show ?thesis
        unfolding explain_union ufe_union.IH[OF x_in_Field_\<alpha> y_in_Field_\<alpha> rep_of_eq]
        unfolding Let_def
        unfolding ufa_lca_union Let_def find_newest_on_walk_union nth_unions_union
        by simp
    qed
  next
    case rep_of_neq: False
    then have "x \<noteq> y"
      by blast      

    from rep_of_neq ufa_lca_union have ufa_lca_union:
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b" (is "_ = ?rep_b")
      using ufe_union.hyps(4) by auto

    interpret ufe_ds_union: union_find_explain_ds where ufe_ds = "ufe_union ufe_ds a b"
      by (intro ufe_ds.ufe_explain_ds_union ufe_union.hyps(2,3))
    interpret ufe_tree_union: ufe_tree where ufe_ds = "ufe_union ufe_ds a b" and x = ?rep_b
      using ufe_ds.rep_of_in_Field_\<alpha>_if_in_Field_\<alpha>[OF ufe_union.hyps(3)]
      by unfold_locales force

    from rep_of_neq x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3) have
      "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds a \<and> ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds b \<or>
      ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds b \<and> ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds a"
      using ufe_ds.rep_of_union[OF ufe_union.hyps(2,3)]
      unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union.hyps(4)] by metis
    moreover from calculation have lca_rep_b: "ufe_tree_union.lca ?rep_b x y"
      apply (subst (2) ufa_lca_union[symmetric], intro ufe_tree_union.lca_ufa_lca)
      sorry
    ultimately obtain p where
      "ufe_tree_union.awalk ?rep_b p x \<or> ufe_tree_union.awalk ?rep_b p y"
      using ufe_tree_union.lca_reachableD(1) ufe_tree_union.reachable_awalk by blast
    with rep_of_neq lca_rep_b find_newest_on_walk_union have newest_eq_Some_length_unions:
      "find_newest_on_walk (ufe_union ufe_ds a b) ?rep_b x = Some (length (unions ufe_ds)) \<or>
      find_newest_on_walk (ufe_union ufe_ds a b) ?rep_b y = Some (length (unions ufe_ds))"
      (is "?newest_x = _ \<or> ?newest_y = _")
      by (metis ufe_tree_union.lca_reachableD(1,2) ufe_tree_union.reachable_awalk)
    have newest_leq_Some_length_unions:
      "find_newest_on_walk (ufe_union ufe_ds a b) ?rep_b x \<le> Some (length (unions ufe_ds))"
        (is "?newest_x \<le> _")
      "find_newest_on_walk (ufe_union ufe_ds a b) ?rep_b y \<le> Some (length (unions ufe_ds))"
        (is "?newest_y \<le> _")
      sorry
    then have newest_lt_Some_length_unions:
      "?newest_x < Some (length (unions ufe_ds)) \<or> ?newest_y < Some (length (unions ufe_ds))"
      by (metis \<open>x \<noteq> y\<close> order_le_less ufa_lca_union ufe_ds_union.in_vertsI
          ufe_ds_union.rep_of_Pair_in_\<alpha>_if_in_Field_\<alpha> ufe_ds_union.ufa_tree_of_eq_if_in_verts
          ufe_ds_union.union_find_explain_ds_axioms
          ufe_tree.intro ufe_tree.neq_find_newest_on_path
          ufe_tree_axioms.intro ufe_union.prems(1) ufe_union.prems(2) ufe_union.prems(3))
    have nth_unions_union_length_unions:
      "unions (ufe_union ufe_ds a b) ! length (unions ufe_ds) = (a, b)"
      using unions_ufe_union by force
    show ?thesis
    proof(cases "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds b")
      case True
 
      from True rep_of_neq explain_simp have explain_union_x_y:
        "explain (unions (ufe_union ufe_ds a b)) x y =
        {(a, b)} \<union> explain (unions ufe_ds) x b \<union> explain (unions ufe_ds) a y"
        unfolding unions_ufe_union by simp

      from True rep_of_neq have "ufe_rep_of ufe_ds y \<noteq> ufe_rep_of ufe_ds b"
        by fastforce
      with find_newest_on_walk_union lca_rep_b ufe_union.hyps(3) have
        "?newest_y = Some (length (unions ufe_ds))"
        using ufe_ds.rep_of_rep_of
        by (metis ufe_tree_union.lca_reachableD(2) ufe_tree_union.reachable_awalk)
      with newest_lt_Some_length_unions have "\<not> ?newest_x \<ge> ?newest_y"
        by simp

      from True have explain_union_x_b:
        "explain (unions (ufe_union ufe_ds a b)) x b = explain (unions ufe_ds) x b"
        unfolding explain_simp[of x b] by simp

      from \<open>ufe_rep_of ufe_ds y \<noteq> ufe_rep_of ufe_ds b\<close> have explain_union_a_y:
        "explain (unions (ufe_union ufe_ds a b)) a y = explain (unions ufe_ds) a y"
        unfolding explain_simp[of a y] sorry

      from \<open>\<not> ?newest_x \<ge> ?newest_y\<close> \<open>?newest_y = Some (length (unions ufe_ds))\<close> \<open>x \<noteq> y\<close>
      show ?thesis
        unfolding ufa_lca_union explain_union_x_y
        using explain_union_x_b explain_union_a_y nth_unions_union_length_unions by force
    next
      case False
 
      from False rep_of_neq explain_simp have explain_union_x_y:
        "explain (unions (ufe_union ufe_ds a b)) x y =
        {(a, b)} \<union> explain (unions ufe_ds) x a \<union> explain (unions ufe_ds) b y"
        unfolding unions_ufe_union by simp

      from False rep_of_neq have "ufe_rep_of ufe_ds y \<noteq> ufe_rep_of ufe_ds a"
        sorry
      with False find_newest_on_walk_union lca_rep_b ufe_union.hyps(3) have
        "?newest_x = Some (length (unions ufe_ds))"
        using ufe_ds.rep_of_rep_of
        by (metis ufe_tree_union.lca_reachableD(1) ufe_tree_union.reachable_awalk)
      with newest_lt_Some_length_unions have "?newest_x \<ge> ?newest_y"
        by simp

      from False have explain_union_x_a:
        "explain (unions (ufe_union ufe_ds a b)) x a = explain (unions ufe_ds) x a"
        unfolding explain_simp[of x a] sorry

      from \<open>ufe_rep_of ufe_ds y \<noteq> ufe_rep_of ufe_ds a\<close> have explain_union_b_y:
        "explain (unions (ufe_union ufe_ds a b)) b y = explain (unions ufe_ds) b y"
        unfolding explain_simp[of b y] sorry

      from \<open>?newest_x \<ge> ?newest_y\<close> \<open>?newest_x = Some (length (unions ufe_ds))\<close> \<open>x \<noteq> y\<close>
      show ?thesis
        unfolding ufa_lca_union explain_union_x_y
        using explain_union_x_a explain_union_b_y nth_unions_union_length_unions by force
    qed
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