theory Explain_Efficient_Correctness
  imports Find_Newest_On_Path
begin

lemma (in ufe_invars) neq_find_newest_on_path_ufa_lca_if_neq:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "x \<noteq> y"
  defines "lca_x_y \<equiv> ufe_lca ufe_ds x y"
  shows "find_newest_on_path ufe_ds lca_x_y x \<noteq> find_newest_on_path ufe_ds lca_x_y y"
proof -
  from assms interpret ufe_tree where pivot = x
    by unfold_locales
  from assms have "y \<in> verts (ufe_tree_of ufe_ds x)"
    using in_verts_if_ufa_rep_of_eq by simp
  note lca_ulca = lca_ufa_lca[OF pivot_in_verts this]
  then obtain px py where
    px: "awalk lca_x_y px x" and py: "awalk lca_x_y py y"
    unfolding lca_x_y_def by (meson lca_reachableD reachable_awalk)
  note find_newest_on_path_dom = this[THEN find_newest_on_path_dom]
  note find_newest_on_path_psimps = this[THEN find_newest_on_path.psimps]
  consider (lca_x) "x = lca_x_y" | (lca_y) "y = lca_x_y" | (not_lca) "lca_x_y \<noteq> x" "lca_x_y \<noteq> y"
    using \<open>x \<noteq> y\<close> by auto
  then show ?thesis
  proof cases
    case lca_x
    then have "find_newest_on_path ufe_ds lca_x_y x = None"
      using find_newest_on_path_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_x have "find_newest_on_path ufe_ds lca_x_y y \<noteq> None"
      using find_newest_on_path_eq_Max_au_of[OF py] by blast      
    ultimately show ?thesis
      by force
  next
    case lca_y
    then have "find_newest_on_path ufe_ds lca_x_y y = None"
      using find_newest_on_path_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_y have "find_newest_on_path ufe_ds lca_x_y x \<noteq> None"
      using find_newest_on_path_eq_Max_au_of[OF px] by blast      
    ultimately show ?thesis
      by force
  next
    case not_lca
    from not_lca px py have "px \<noteq> []" "py \<noteq> []"
      using awalk_empty_ends px by blast+
    from not_lca px py obtain ix iy where
      ix: "ix \<in> set px" "find_newest_on_path ufe_ds lca_x_y x = Some (au_of ix)" and
      iy: "iy \<in> set py" "find_newest_on_path ufe_ds lca_x_y y = Some (au_of iy)"
      using newest_on_pathE[unfolded newest_on_path_def]
      by (simp add: find_newest_on_path_eq_Max_au_of) metis
    moreover note ps[unfolded lca_x_y_def] = px py
    note disjoint_awalk_if_awalk_lca[OF lca_ulca \<open>x \<noteq> y\<close> this]
    with ix iy have "ix \<noteq> iy"
      by blast
    moreover from px py ix iy have
      "ix \<in> arcs (ufe_tree_of ufe_ds x)" "iy \<in> arcs (ufe_tree_of ufe_ds x)"
      by blast+
    ultimately show ?thesis
      using inj_on_au_of_arcs ix iy by (fastforce dest: inj_onD)
  qed
qed

context ufe_invars
begin

context
  fixes a b
  assumes eff_union: "eff_union (uf_ds ufe_ds) a b"
begin

lemma
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  defines "ufe_ds' \<equiv> ufe_union ufe_ds a b"
  defines "newest_x \<equiv> find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x"
  defines "newest_y \<equiv> find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y"
  shows ufe_lca_ufe_union_eq_if_ufe_rep_of_eq:
    "ufe_lca ufe_ds' x y = ufe_lca ufe_ds x y"
    and find_newest_on_path_ufe_union_ufe_lca:
    "find_newest_on_path ufe_ds' (ufe_lca ufe_ds x y) x = newest_x"
    "find_newest_on_path ufe_ds' (ufe_lca ufe_ds x y) y = newest_y"
    and find_newest_on_path_ufe_union_ufe_lca_lt_Some_length_unions:
    "newest_x < Some (length (unions ufe_ds))"
    "newest_y < Some (length (unions ufe_ds))"
    and find_newest_on_path_ufe_union_ufe_lca_neq:
    "x \<noteq> y \<Longrightarrow> newest_x \<noteq> newest_y"
    and unions_nth_find_newest_on_path_ufe_union_ufe_lca:
    "newest_x > newest_y \<Longrightarrow>
      unions ufe_ds' ! the newest_x = unions ufe_ds ! the newest_x"
    "newest_x < newest_y \<Longrightarrow>
      unions ufe_ds' ! the newest_y = unions ufe_ds ! the newest_y"
proof -
  from assms interpret ufe_tree: ufe_tree
    where ufe_ds = ufe_ds and pivot = x
    by unfold_locales blast
  from eff_union assms interpret ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars_ufe_union by blast
  from assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and pivot = x
    by unfold_locales simp

  from eff_union assms show lca_eq:
    "ufe_lca ufe_ds' x y = ufe_lca ufe_ds x y"
    using ufa_lca_ufa_union ufa_rep_of_ufa_union
    by simp

  from eff_union assms have ufe_rep_of_union_eq:
    "ufe_rep_of ufe_ds' x = ufe_rep_of ufe_ds' y"
    using uf_ds_ufe_union ufa_rep_of_ufa_union by simp
  from assms have "y \<in> verts (ufe_tree_of ufe_ds x)"
    using ufe_tree.in_verts_if_ufa_rep_of_eq by metis
  with assms ufe_tree.pivot_in_verts obtain px py where
    px: "ufe_tree.awalk (ufe_lca ufe_ds' x y) px x" and
    py: "ufe_tree.awalk (ufe_lca ufe_ds' x y) py y"
    unfolding lca_eq
    using ufe_tree.lca_ufa_lca ufe_tree.lca_reachableD ufe_tree.reachable_awalk
    by metis
  moreover note find_newest_on_path_ufe_union[OF eff_union]
  moreover from assms ufe_rep_of_union_eq have
    "ufe_rep_of ufe_ds (ufe_lca ufe_ds' x y) = ufe_rep_of ufe_ds x"
    unfolding lca_eq
    using ufe_tree.ufa_rep_of_ufa_lca ufe_tree.in_verts_if_ufa_rep_of_eq by metis
  ultimately show newest_eq:
    "find_newest_on_path ufe_ds' (ufe_lca ufe_ds x y) x = newest_x"
    "find_newest_on_path ufe_ds' (ufe_lca ufe_ds x y) y = newest_y"
    using assms lca_eq ufe_tree.ufe_union_awalk_if_awalk[OF eff_union]
    by metis+

  note px py
  from this[THEN ufe_tree.find_newest_on_path_lt_Some_length_unions] show newest_lt:
    "newest_x < Some (length (unions ufe_ds))"
    "newest_y < Some (length (unions ufe_ds))"
    unfolding lca_eq newest_eq newest_x_def newest_y_def by blast+

  note neq_find_newest_on_path_ufa_lca_if_neq[OF assms(1-3)]
  then show "newest_x \<noteq> newest_y" if "x \<noteq> y"
    using that lca_eq newest_eq unfolding newest_x_def newest_y_def by simp

  from newest_lt show
    "newest_y < newest_x \<Longrightarrow>
      unions ufe_ds' ! the newest_x = unions ufe_ds ! the newest_x"
    "newest_y > newest_x \<Longrightarrow>
      unions ufe_ds' ! the newest_y = unions ufe_ds ! the newest_y"
    unfolding ufe_ds'_def
    by (cases newest_x; cases newest_y; simp add: nth_append)+
qed

end

lemma explain'_pinduct[consumes 4, case_names eq newest_x newest_y]:
  assumes "explain'_dom ufe_ds (x, y)"
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "\<And>x. x \<in> Field (ufe_\<alpha> ufe_ds) \<Longrightarrow> P x x"
  assumes "\<And>x y ax bx.
    \<lbrakk> explain'_dom ufe_ds (x, y)
    ; x \<in> Field (ufe_\<alpha> ufe_ds); y \<in> Field (ufe_\<alpha> ufe_ds)
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; x \<noteq> y
    ; find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x \<ge>
      find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y
    ; unions ufe_ds ! the (find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x) = (ax, bx)
    ; P x ax; P bx y
    \<rbrakk> \<Longrightarrow> P x y"
  assumes "\<And>x y ay by.
    \<lbrakk> explain'_dom ufe_ds (x, y)
    ; x \<in> Field (ufe_\<alpha> ufe_ds); y \<in> Field (ufe_\<alpha> ufe_ds)
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; x \<noteq> y
    ; \<not> find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x \<ge>
      find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y
    ; unions ufe_ds ! the (find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y) = (ay, by)
    ; P x by; P ay y
    \<rbrakk> \<Longrightarrow> P x y"
  shows "P x y"
  using assms(1-4)
proof(induction rule: explain'.pinduct)
  case (1 x y)
  then interpret ufe_tree where pivot = x
    by unfold_locales

  from 1 have in_verts_ufe_tree:
    "x \<in> verts (ufe_tree_of ufe_ds x)"
    "y \<in> verts (ufe_tree_of ufe_ds x)"
    using in_verts_if_ufa_rep_of_eq by metis+
  then obtain px py where
    px: "awalk (ufe_lca ufe_ds x y) px x" and
    py: "awalk (ufe_lca ufe_ds x y) py y"
    using lca_ufa_lca lca_reachableD by (metis reachable_awalk)

  consider
    (eq) "x = y" |
    (newest_x) ax bx where "x \<noteq> y"
      "find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x \<ge>
        find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y"
      "unions ufe_ds ! the (find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x) = (ax, bx)" |
    (newest_y) ay "by" where "x \<noteq> y"
      "\<not> find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x \<ge>
        find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y"
      "unions ufe_ds ! the (find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y) = (ay, by)"
    by (metis surj_pair)
  then show ?case
  proof cases
    case eq
    with 1 assms(5) show ?thesis
      by simp
  next
    case newest_x
    with neq_find_newest_on_path_ufa_lca_if_neq[OF "1.prems"] have
      "ufe_lca ufe_ds x y \<noteq> x"
      using less_eq_option_None_is_None by fastforce
    note newest_on_path_find_newest_on_path[OF px this]
    with \<open>ufe_lca ufe_ds x y \<noteq> x\<close> newest_x "1.prems" have
      "ax \<in> Field (ufe_\<alpha> ufe_ds)" "bx \<in> Field (ufe_\<alpha> ufe_ds)"
      "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds ax"
      "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds bx"
      using newest_on_path_valid_union ufe_rep_of_eq_if_newest_on_path
      by simp_all
    moreover note IH = "1.IH"(1,2)[OF \<open>x \<noteq> y\<close> HOL.refl HOL.refl HOL.refl
        newest_x(2) newest_x(3)[symmetric] HOL.refl]
    ultimately show ?thesis
      using "1.prems"
      by (intro assms(6)[OF "1.hyps" "1.prems" newest_x]) metis+
  next
    case newest_y
    with neq_find_newest_on_path_ufa_lca_if_neq[OF "1.prems"] have
      "ufe_lca ufe_ds x y \<noteq> y"
      using less_eq_option_None_is_None by fastforce
    note newest_on_path_find_newest_on_path[OF py this]
    with \<open>ufe_lca ufe_ds x y \<noteq> y\<close> newest_y "1.prems" have
      "ay \<in> Field (ufe_\<alpha> ufe_ds)" "by \<in> Field (ufe_\<alpha> ufe_ds)"
      "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds by"
      "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds ay"
      using newest_on_path_valid_union ufe_rep_of_eq_if_newest_on_path
      by simp_all
    moreover note IH = "1.IH"(3,4)[OF \<open>x \<noteq> y\<close> HOL.refl HOL.refl HOL.refl
        newest_y(2) newest_y(3)[symmetric] HOL.refl]
    ultimately show ?thesis
      using "1.prems"
      by (intro assms(7)[OF "1.hyps" "1.prems" newest_y]) metis+
  qed
qed

lemma explain'_dom_ufe_union:
  assumes "explain'_dom ufe_ds (x, y)"
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "eff_union (uf_ds ufe_ds) a b"
  shows "explain'_dom (ufe_union ufe_ds a b) (x, y)"
  using assms
proof(induction rule: explain'_pinduct)
  case (eq x)
  then show ?case
    using explain'.domintros by blast
next
  case (newest_x x y ax bx)
  note
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    find_newest_on_path_ufe_union_ufe_lca
    find_newest_on_path_ufe_union_ufe_lca_neq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note [simp] = this[OF newest_x.prems]
  from newest_x have
    "find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x >
      find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y"
    using neq_find_newest_on_path_ufa_lca_if_neq by (metis less_le)
  with newest_x show ?case
    by (intro explain'.domintros[where x = x and y = y])
      (simp_all del: ufe_union_sel)
next
  case (newest_y x y ay "by")
  note
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    find_newest_on_path_ufe_union_ufe_lca
    find_newest_on_path_ufe_union_ufe_lca_neq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note [simp] = this[OF newest_y.prems]
  from newest_y have
    "find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x <
      find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y"
    by order
  with newest_y show ?case
    by (intro explain'.domintros[where x = x and y = y])
      (simp_all del: ufe_union_sel)
qed

lemma leq_Some_if_lt_Suc_Some:
  assumes "x < Some (Suc n)"
  shows "x \<le> Some n"
  using assms by (cases x) auto

lemma explain'_dom_if_ufe_rep_of_eq:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "explain'_dom ufe_ds (x, y)"
  using assms
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case (ufe_init x y)
  then have "x = y"
    using ufe_rep_of_ufe_init by simp
  then show ?case
    using explain'.domintros by blast
next
  case (ufe_union ufe_ds a b x y)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by blast
  interpret ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
    by (intro ufe_invars_ufe_union ufe_union.hyps)
  from ufe_union.prems interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and pivot = x
    by unfold_locales

  from ufe_union.prems have in_verts_ufe_tree_union:
    "x \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) x)"
    "y \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) x)"
    using ufe_tree_union.in_verts_if_ufa_rep_of_eq by metis+

  then obtain px py where
    px: "ufe_tree_union.awalk (ufe_lca (ufe_union ufe_ds a b) x y) px x" and
    py: "ufe_tree_union.awalk (ufe_lca (ufe_union ufe_ds a b) x y) py y"
    using ufe_tree_union.lca_ufa_lca ufe_tree_union.lca_reachableD
    by (metis ufe_tree_union.reachable_awalk)

  from ufe_union have in_Field_ufe_\<alpha>:
    "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
    by simp_all
  from ufe_union.hyps(2) this ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    with ufe_union have "explain'_dom ufe_ds (x, y)"
      by simp
    with ufe_union.prems show ?thesis
      by (intro explain'_dom_ufe_union 1 ufe_union.hyps) simp_all
  next
    case 2
    note find_newest_on_path_ufe_union[OF ufe_union.hyps(2) px]
    with 2 in_Field_ufe_\<alpha> ufe_union.prems ufe_union.hyps have newest_x_eq:
      "find_newest_on_path (ufe_union ufe_ds a b) (ufe_lca (ufe_union ufe_ds a b) x y) x =
      Some (length (unions ufe_ds))"
      unfolding uf_ds_ufe_union by (metis ufa_lca_ufa_union ufa_rep_of_ufa_rep_of)
    moreover have
      "find_newest_on_path (ufe_union ufe_ds a b) (ufe_lca (ufe_union ufe_ds a b) x y) x \<ge>
      find_newest_on_path (ufe_union ufe_ds a b) (ufe_lca (ufe_union ufe_ds a b) x y) y"
    proof -
      from 2 have "x \<noteq> y"
        by blast
      note ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq[OF ufe_union.prems this]
      moreover note ufe_tree_union.find_newest_on_path_lt_Some_length_unions[OF py]
      ultimately show ?thesis
        using newest_x_eq leq_Some_if_lt_Suc_Some by simp
    qed
    ultimately show ?thesis
      using 2 in_Field_ufe_\<alpha> ufe_union.hyps(2)
      apply(intro explain'.domintros[where x = x and y = y] ufe_union.IH[THEN explain'_dom_ufe_union])
      by fastforce+
  next
    case 3
    note find_newest_on_path_ufe_union[OF ufe_union.hyps(2) py]
    with 3 in_Field_ufe_\<alpha> ufe_union.prems ufe_union.hyps have newest_y_eq:
      "find_newest_on_path (ufe_union ufe_ds a b) (ufe_lca (ufe_union ufe_ds a b) x y) y =
      Some (length (unions ufe_ds))"
      unfolding uf_ds_ufe_union by (metis ufa_lca_ufa_union ufa_rep_of_ufa_rep_of)
    moreover have
      "\<not> find_newest_on_path (ufe_union ufe_ds a b) (ufe_lca (ufe_union ufe_ds a b) x y) x \<ge>
      find_newest_on_path (ufe_union ufe_ds a b) (ufe_lca (ufe_union ufe_ds a b) x y) y"
    proof -
      from 3 have "x \<noteq> y"
        by blast
      note ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq[OF ufe_union.prems this]
      moreover note ufe_tree_union.find_newest_on_path_lt_Some_length_unions[OF px]
      ultimately show ?thesis
        using newest_y_eq leq_Some_if_lt_Suc_Some
        by (metis length_append_singleton order_antisym_conv unions_ufe_union)
    qed
    ultimately show ?thesis
      using 3 in_Field_ufe_\<alpha> ufe_union.hyps(2)
      apply(intro explain'.domintros[where x = x and y = y] explain'_dom_ufe_union ufe_union.IH)
      by fastforce+
  qed
qed

lemma explain'_ufe_union:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "eff_union (uf_ds ufe_ds) a b"
  shows "explain' (ufe_union ufe_ds a b) x y = explain' ufe_ds x y"
  using explain'_dom_if_ufe_rep_of_eq[OF assms(1-3)] assms
proof(induction rule: explain'_pinduct)
  case (eq x)
  then show ?case
    by simp
next
  case (newest_x x y ax bx)
  moreover from newest_x.hyps have
    "find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y <
    find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x"
    using neq_find_newest_on_path_ufa_lca_if_neq[OF newest_x.hyps(2-4)]
    by force
  moreover from newest_x interpret ufe_invars_union: ufe_invars
    where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars_ufe_union by blast
  from newest_x have "explain'_dom (ufe_union ufe_ds a b) (x, y)"
    by (intro ufe_invars_union.explain'_dom_if_ufe_rep_of_eq)
      (force simp: ufa_rep_of_ufa_union)+
  moreover note
    find_newest_on_path_ufe_union_ufe_lca
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note this[OF newest_x.prems newest_x.hyps(2-4)]
  ultimately show ?case
    by (auto simp: explain'.psimps Let_def)
next
  case (newest_y x y ay "by")
  moreover from newest_y have
    "find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) y >
    find_newest_on_path ufe_ds (ufe_lca ufe_ds x y) x"
    by order
  moreover from newest_y interpret ufe_invars_union: ufe_invars
    where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars_ufe_union by blast
  from newest_y have "explain'_dom (ufe_union ufe_ds a b) (x, y)"
    by (intro ufe_invars_union.explain'_dom_if_ufe_rep_of_eq)
      (force simp: ufa_rep_of_ufa_union)+
  moreover note
    find_newest_on_path_ufe_union_ufe_lca
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note this[OF newest_y.prems newest_y.hyps(2-4)]
  ultimately show ?case
    by (auto simp: explain'.psimps Let_def)
qed

lemma explain_eq_explain':
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "explain (uf_ds ufe_init) (unions ufe_ds) x y = explain' ufe_ds x y"
  using assms                                                 
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init
  then have "x = y"
    using ufe_rep_of_ufe_init by fastforce
  then show ?case
    by simp
next
  case (ufe_union ufe_ds a b x y)

  from ufe_union interpret ufe_invars: ufe_invars ufe_init ufe_ds
    by blast
  from ufe_union have in_Field_ufe_\<alpha>:
    "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
    by simp_all
  then interpret ufe_tree: ufe_tree where ufe_ds = ufe_ds and pivot = x
    by unfold_locales

  let ?ufe_ds' = "ufe_union ufe_ds a b"
  let ?newest_x = "find_newest_on_path ?ufe_ds' (ufe_lca ?ufe_ds' x y) x"
  let ?newest_y = "find_newest_on_path ?ufe_ds' (ufe_lca ?ufe_ds' x y) y"
  from ufe_union interpret ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars.ufe_invars_ufe_union by metis
  from ufe_union interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and pivot = x
    by unfold_locales
  from ufe_union.prems(2,3) ufe_tree_union.pivot_in_verts have
    "y \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) x)"
    using ufe_tree_union.in_verts_if_ufa_rep_of_eq by metis
  with ufe_tree_union.pivot_in_verts obtain px py where
    px: "ufe_tree_union.awalk (ufe_lca (ufe_union ufe_ds a b) x y) px x" and
    py: "ufe_tree_union.awalk (ufe_lca (ufe_union ufe_ds a b) x y) py y"
    using ufe_tree_union.lca_ufa_lca ufe_tree_union.lca_reachableD ufe_tree_union.reachable_awalk
    by metis
  note this[THEN ufe_tree_union.find_newest_on_path_lt_Some_length_unions]
  then have find_newest_on_path_le:
    "?newest_x \<le> Some (length (unions ufe_ds))"
    "?newest_y \<le> Some (length (unions ufe_ds))"
    using leq_Some_if_lt_Suc_Some by simp_all
  from ufe_union.prems px py have find_newest_on_path_neq:
    "?newest_x \<noteq> ?newest_y" if "x \<noteq> y"
    using that ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast

  have explain'_dom_x_y:
    "explain'_dom (ufe_union ufe_ds a b) (x, y)"
     by (intro ufe_invars_union.explain'_dom_if_ufe_rep_of_eq ufe_union.prems)

  from ufe_union.hyps(2) in_Field_ufe_\<alpha> ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    with ufe_union have
      "explain (uf_ds ufe_init) (unions (ufe_union ufe_ds a b)) x y =
      explain (uf_ds ufe_init) (unions ufe_ds) x y"
      using ufe_invars.uf_ds_ufe_ds_eq_ufa_unions
      by (cases "x = y") (simp_all add: Let_def)
    also have "\<dots> = explain' ufe_ds x y"
      by (intro ufe_union.IH in_Field_ufe_\<alpha> 1)
    also have "\<dots> = explain' (ufe_union ufe_ds a b) x y"
      by (intro ufe_invars.explain'_ufe_union[symmetric] in_Field_ufe_\<alpha> ufe_union.hyps 1)
    finally show ?thesis .
  next
    case 2
    let ?P = "\<lambda>p1 p2. TransP (TransP p1 (AssmP (length (unions ufe_ds)))) p2"
    from 2 have "explain (uf_ds ufe_init) (unions (ufe_union ufe_ds a b)) x y =
      ?P (explain (uf_ds ufe_init) (unions ufe_ds) x a)
        (explain (uf_ds ufe_init) (unions ufe_ds) b y)"
      by (simp add: Let_def ufe_invars.uf_ds_ufe_ds_eq_ufa_unions)
    also from 2 ufe_union.hyps have "\<dots> =
      ?P (explain' ufe_ds x a) (explain' ufe_ds b y)"
      using in_Field_ufe_\<alpha> by (simp add: ufe_union.IH)
    also from 2 ufe_union.hyps have "\<dots> =
      ?P (explain' (ufe_union ufe_ds a b) x a) (explain' (ufe_union ufe_ds a b) b y)"
      using in_Field_ufe_\<alpha>
      by (force simp: ufe_invars.explain'_ufe_union)
    also have "\<dots> = explain' (ufe_union ufe_ds a b) x y"
    proof -
      from 2 ufe_union in_Field_ufe_\<alpha> have
      "ufe_lca (ufe_union ufe_ds a b) x y = ufe_rep_of ufe_ds b"
        unfolding uf_ds_ufe_union using ufa_lca_ufa_union by metis
      moreover from this 2 in_Field_ufe_\<alpha> have
        "?newest_x = Some (length (unions ufe_ds))"
        using ufe_invars.find_newest_on_path_ufe_union[OF _ px] ufe_union.hyps(2)
        by (metis ufa_rep_of_ufa_rep_of)
      moreover from this 2 have
        "?newest_y < Some (length (unions ufe_ds))"
        using find_newest_on_path_le find_newest_on_path_neq by fastforce
      moreover from calculation have
        "?newest_y \<le> ?newest_x"
        by order
      moreover from 2 have "x \<noteq> y"
        by blast
      ultimately show ?thesis
        unfolding explain'.psimps[OF explain'_dom_x_y] by simp
    qed
    finally show ?thesis .      
  next
    case 3
    let ?P = "\<lambda>p1 p2. TransP (TransP p1 (SymP (AssmP (length (unions ufe_ds))))) p2"
    from 3 have "explain (uf_ds ufe_init) (unions (ufe_union ufe_ds a b)) x y =
      ?P (explain (uf_ds ufe_init) (unions ufe_ds) x b)
        (explain (uf_ds ufe_init) (unions ufe_ds) a y)"
      by (simp add: Let_def ufe_invars.uf_ds_ufe_ds_eq_ufa_unions)
    also from 3 ufe_union.hyps have "\<dots> =
      ?P (explain' ufe_ds x b) (explain' ufe_ds a y)"
      using in_Field_ufe_\<alpha> by (simp add: ufe_union.IH)
    also from 3 ufe_union.hyps have "\<dots> =
      ?P (explain' (ufe_union ufe_ds a b) x b) (explain' (ufe_union ufe_ds a b) a y)"
      using in_Field_ufe_\<alpha>
      by (force simp: ufe_invars.explain'_ufe_union)
    also have "\<dots> = explain' (ufe_union ufe_ds a b) x y"
    proof -
      from 3 ufe_union in_Field_ufe_\<alpha> have
      "ufe_lca (ufe_union ufe_ds a b) x y = ufe_rep_of ufe_ds b"
        unfolding uf_ds_ufe_union using ufa_lca_ufa_union by metis
      moreover from this 3 in_Field_ufe_\<alpha> have
        "?newest_y = Some (length (unions ufe_ds))"
        using ufe_invars.find_newest_on_path_ufe_union[OF _ py] ufe_union.hyps(2)
        by (metis ufa_rep_of_ufa_rep_of)
      moreover from this 3 have
        "?newest_x < Some (length (unions ufe_ds))"
        using find_newest_on_path_le find_newest_on_path_neq by fastforce
      moreover from calculation have
        "\<not> ?newest_y \<le> ?newest_x"
        by order
      moreover from 3 have "x \<noteq> y"
        by blast
      ultimately show ?thesis
        unfolding explain'.psimps[OF explain'_dom_x_y] by simp
    qed
    finally show ?thesis .   
  qed
qed

end

definition ufe_union_size where
  "ufe_union_size ufe_ds x y \<equiv>
    let
      rep_x = ufe_rep_of ufe_ds x;
      rep_y = ufe_rep_of ufe_ds y
    in
      if rep_x \<noteq> rep_y then
        if ufa_size (uf_ds ufe_ds) rep_x < ufa_size (uf_ds ufe_ds) rep_y
          then ufe_union ufe_ds x y
          else ufe_union ufe_ds y x
      else ufe_ds"

definition "ufe_unions_size \<equiv> foldl (\<lambda>ufe_ds (x, y). ufe_union_size ufe_ds x y)"

lemma (in ufe_invars) ufe_invars_ufe_union_size:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  defines "ufe_ds' \<equiv> ufe_union_size ufe_ds x y"
  shows "ufe_invars ufe_init ufe_ds'"
  using assms(1,2) unfolding ufe_ds'_def ufe_union_size_def
  by (auto simp: Let_def ufe_invars_axioms intro!: ufe_invars_ufe_union)

lemma (in ufe_init_invars) ufe_invars_ufe_unions_size:
  assumes "valid_unions (uf_ds ufe_init) us"
  shows "ufe_invars ufe_init (ufe_unions_size ufe_init us)"
  using assms
proof(induction us rule: rev_induct)
  case Nil
  have "ufe_invars ufe_init ufe_init"
    by (unfold_locales) simp_all
  with Nil show ?case
    unfolding ufe_unions_size_def ufe_union_size_def by simp
next
  case (snoc u us)
  then interpret ufe_invars ufe_init "ufe_unions_size ufe_init us"
    by simp
   
  from snoc show ?case
    using ufe_invars_ufe_union_size unfolding ufe_unions_size_def
    by (auto simp: case_prod_beta ufe_invars.in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init)
qed

end
