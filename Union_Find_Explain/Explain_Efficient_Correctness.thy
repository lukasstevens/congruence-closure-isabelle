theory Explain_Efficient_Correctness
  imports Find_Newest_On_Path
begin
             
lemma (in ufe_invars) neq_find_newest_on_path_ufa_lca_if_neq:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "x \<noteq> y"
  defines "lca_x_y \<equiv> ufa_lca (uf_ds ufe_ds) x y"
  shows "find_newest_on_path ufe_ds lca_x_y x \<noteq> find_newest_on_path ufe_ds lca_x_y y"
proof -
  from assms interpret ufe_tree where x = x
    by unfold_locales
  from assms have "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
    using in_verts_if_rep_of_eq by simp
  note lca_ulca = lca_ufa_lca[OF x_in_verts this]
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
    moreover
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
      "ix \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)" "iy \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
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
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  defines "ufe_lca_union \<equiv> ufa_lca (uf_ds (ufe_union ufe_ds a b))"
  defines "find_newest_union \<equiv> find_newest_on_path (ufe_union ufe_ds a b)"
  shows ufe_lca_ufe_union_eq_if_ufe_rep_of_eq:
    "ufe_lca_union x y = ufa_lca (uf_ds ufe_ds) x y"
    and find_newest_on_path_ufe_union_ufe_lca:
    "find_newest_union (ufe_lca_union x y) x =
      find_newest_on_path ufe_ds (ufe_lca_union x y) x"
    "find_newest_union (ufe_lca_union x y) y =
      find_newest_on_path ufe_ds (ufe_lca_union x y) y"
    and find_newest_on_path_ufe_union_ufe_lca_lt_Some_length_unions:
    "find_newest_union (ufe_lca_union x y) x < Some (length (unions ufe_ds))"
    "find_newest_union (ufe_lca_union x y) y < Some (length (unions ufe_ds))"
    and find_newest_on_path_ufe_union_ufe_lca_neq:
    "x \<noteq> y \<Longrightarrow>
      find_newest_union (ufe_lca_union x y) x \<noteq> find_newest_union (ufe_lca_union x y) y"
    and unions_nth_find_newest_on_path_ufe_union_ufe_lca:
    "find_newest_union (ufe_lca_union x y) y < find_newest_union (ufe_lca_union x y) x \<Longrightarrow>
      unions (ufe_union ufe_ds a b) ! the (find_newest_union (ufe_lca_union x y) x) =
        unions ufe_ds ! the (find_newest_union (ufe_lca_union x y) x)"
    "find_newest_union (ufe_lca_union x y) y > find_newest_union (ufe_lca_union x y) x \<Longrightarrow>
      unions (ufe_union ufe_ds a b) ! the (find_newest_union (ufe_lca_union x y) y) =
        unions ufe_ds ! the (find_newest_union (ufe_lca_union x y) y)"
proof -
  from assms interpret ufe_tree: ufe_tree
    where ufe_ds = ufe_ds and x = x
    by unfold_locales blast
  from eff_union assms interpret ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars_ufe_union by blast
  from assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and x = x
    by unfold_locales simp

  from eff_union assms show lca_eq:
    "ufe_lca_union x y = ufa_lca (uf_ds ufe_ds) x y"
    using ufa_lca_ufa_union ufa_rep_of_ufa_union
    by simp

  from eff_union assms have ufe_rep_of_union_eq:
    "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y"
    using uf_ds_ufe_union ufa_rep_of_ufa_union by simp
  from assms have "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
    using ufe_tree.in_verts_if_rep_of_eq by metis
  with assms ufe_tree.x_in_verts obtain px py where
    px: "ufe_tree.awalk (ufe_lca_union x y) px x" and
    py: "ufe_tree.awalk (ufe_lca_union x y) py y"
    unfolding lca_eq
    using ufe_tree.lca_ufa_lca ufe_tree.lca_reachableD ufe_tree.reachable_awalk
    by metis
  moreover note find_newest_on_path_ufe_union[OF eff_union]
  moreover from assms ufe_rep_of_union_eq have
    "ufe_rep_of ufe_ds (ufe_lca_union x y) = ufe_rep_of ufe_ds x"
    unfolding lca_eq
    using ufe_tree.ufa_rep_of_ufa_lca ufe_tree.in_verts_if_rep_of_eq by metis
  ultimately show newest_eq:
    "find_newest_union (ufe_lca_union x y) x = find_newest_on_path ufe_ds (ufe_lca_union x y) x"
    "find_newest_union (ufe_lca_union x y) y = find_newest_on_path ufe_ds (ufe_lca_union x y) y"
    using assms ufe_tree.ufe_union_awalk_if_awalk[OF eff_union]
    by metis+

  note px py
  from this[THEN ufe_tree.find_newest_on_path_lt_Some_length_unions] show newest_lt:
    "find_newest_union (ufe_lca_union x y) x < Some (length (unions ufe_ds))"
    "find_newest_union (ufe_lca_union x y) y < Some (length (unions ufe_ds))"
    unfolding newest_eq by blast+

  note neq_find_newest_on_path_ufa_lca_if_neq[OF assms(1-3)]
  then show
    "find_newest_union (ufe_lca_union x y) x \<noteq> find_newest_union (ufe_lca_union x y) y"
    if "x \<noteq> y"
    using that lca_eq newest_eq by simp

  from newest_lt show
    "find_newest_union (ufe_lca_union x y) y < find_newest_union (ufe_lca_union x y) x \<Longrightarrow>
      unions (ufe_union ufe_ds a b) ! the (find_newest_union (ufe_lca_union x y) x) =
        unions ufe_ds ! the (find_newest_union (ufe_lca_union x y) x)"
    "find_newest_union (ufe_lca_union x y) y > find_newest_union (ufe_lca_union x y) x \<Longrightarrow>
      unions (ufe_union ufe_ds a b) ! the (find_newest_union (ufe_lca_union x y) y) =
        unions ufe_ds ! the (find_newest_union (ufe_lca_union x y) y)"
    by (cases "find_newest_union (ufe_lca_union x y) x";
        cases "find_newest_union (ufe_lca_union x y) y";
        simp add: nth_append)+
qed

end

lemma explain'_induct[consumes 3, case_names eq newest_x newest_y]:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "\<And>x. x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)) \<Longrightarrow> P x x"
  assumes "\<And>x y ax bx.
    \<lbrakk> x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)); y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; x \<noteq> y
    ; find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x >
      find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y
    ; unions ufe_ds ! the (find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x) = (ax, bx)
    ; P x ax; P bx y
    \<rbrakk> \<Longrightarrow> P x y"
  assumes "\<And>x y ay by.
    \<lbrakk> x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)); y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; x \<noteq> y
    ; find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x <
      find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y
    ; unions ufe_ds ! the (find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y) = (ay, by)
    ; P x by; P ay y
    \<rbrakk> \<Longrightarrow> P x y"
  shows "P x y"
  using assms
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    by (simp add: ufe_rep_of_ufe_init)
next
  case (ufe_union ufe_ds a b x y)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by blast
  let ?lca = "ufa_lca (uf_ds (ufe_union ufe_ds a b))"
  let ?newest_union = "find_newest_on_path (ufe_union ufe_ds a b)"

  from ufe_union.prems have
    x_in_Field_\<alpha>: "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
    using eff_unionD[OF ufe_union.hyps(2)] Field_ufa_\<alpha>_uf_ds_ufe_union
    by metis+

  with ufe_union interpret ufe_invars_union: ufe_invars
    where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars_ufe_union by metis

  note * =
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    find_newest_on_path_ufe_union_ufe_lca
    find_newest_on_path_ufe_union_ufe_lca_lt_Some_length_unions
    find_newest_on_path_ufe_union_ufe_lca_neq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  have IH: "P x y"
    if "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
      "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y" "x \<noteq> y" for x y
    apply(intro ufe_union.IH[OF that(1-3) ufe_union.prems(4-6),
            of "\<lambda>_ _ ax _. ax" "\<lambda>_ _ _ bx. bx" "\<lambda>_ _ ay _. ay" "\<lambda>_ _ _ by. by"])
    using *[OF ufe_union.hyps(2)]
    using ufa_rep_of_ufa_union[OF eff_unionD(1,2)[OF ufe_union.hyps(2)]]
    using Field_ufa_\<alpha>_ufa_union uf_ds_ufe_union
    by - metis+

  from ufe_union.prems(1) interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and x = x
    by unfold_locales

  from ufe_tree_union.x_in_verts ufe_union.prems(2,3) obtain px py where
    px: "ufe_tree_union.awalk (?lca x y) px x" and
    py: "ufe_tree_union.awalk (?lca x y) py y"
    using ufe_tree_union.lca_reachableD ufe_tree_union.lca_ufa_lca
    by (metis ufe_tree_union.in_verts_if_rep_of_eq ufe_tree_union.reachable_awalk)

  from ufe_union.hyps(2-) x_in_Field_\<alpha> y_in_Field_\<alpha> ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    with IH show ?thesis
      using ufe_union.prems(4) x_in_Field_\<alpha> y_in_Field_\<alpha> by fastforce
  next
    case 2
    then have "x \<noteq> y"
      by blast
    moreover from 2 x_in_Field_\<alpha> y_in_Field_\<alpha> eff_unionD(1,2)[OF ufe_union.hyps(2)] have
      "P x a" "P b y"
      using ufe_union.prems(1,2,4) IH by metis+
    moreover have
      "?newest_union (?lca x y) x = Some (length (unions ufe_ds))"
      "?newest_union (?lca x y) y < Some (length (unions ufe_ds))"
    proof -
      note ufa_lca_ufa_union[OF ufe_union.hyps(2-) x_in_Field_\<alpha> y_in_Field_\<alpha>]
      with 2 ufe_union.prems(3) have "?lca x y = ufe_rep_of ufe_ds b"
        by simp
      moreover note px py
      note this[THEN find_newest_on_path_ufe_union[OF ufe_union.hyps(2-)]]
      ultimately show 
        "?newest_union (?lca x y) x = Some (length (unions ufe_ds))"
        using 2 ufe_union.hyps(2) by simp
      moreover from 2 ufe_union.prems(2,3) have
        "?newest_union (?lca x y) x \<noteq> ?newest_union (?lca x y) y"
        using ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast
      moreover have
        "?newest_union (?lca x y) y \<le> Some (length (unions ufe_ds))"
        using ufe_tree_union.find_newest_on_path_lt_Some_length_unions[OF py]
        by (cases "?newest_union (?lca x y) y") simp_all
      ultimately show "?newest_union (?lca x y) y < Some (length (unions ufe_ds))"
        by simp
    qed
    ultimately show ?thesis
      using 2 ufe_union.prems(1-3)
      by (intro ufe_union.prems(5)[OF _ _ _ _ _ _ \<open>P x a\<close> \<open>P b y\<close>]) simp_all
  next
    case 3
    then have "x \<noteq> y"
      by blast
    moreover from 3 x_in_Field_\<alpha> y_in_Field_\<alpha> eff_unionD(1,2)[OF ufe_union.hyps(2)] have
      "P x b" "P a y"
      using ufe_union.prems(1,2,4) IH by metis+
    moreover have
      "?newest_union (?lca x y) y = Some (length (unions ufe_ds))"
      "?newest_union (?lca x y) x < Some (length (unions ufe_ds))"
    proof -
      note ufa_lca_ufa_union[OF ufe_union.hyps(2-) x_in_Field_\<alpha> y_in_Field_\<alpha>]
      with 3 ufe_union.prems(3) have "?lca x y = ufe_rep_of ufe_ds b"
        by simp
      moreover note px py
      note this[THEN find_newest_on_path_ufe_union[OF ufe_union.hyps(2-)]]
      ultimately show 
        "?newest_union (?lca x y) y = Some (length (unions ufe_ds))"
        using 3 ufe_union.hyps(2) by simp
      moreover from 3 ufe_union.prems(2,3) have
        "?newest_union (?lca x y) x \<noteq> ?newest_union (?lca x y) y"
        using ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast
      moreover have
        "?newest_union (?lca x y) x \<le> Some (length (unions ufe_ds))"
        using ufe_tree_union.find_newest_on_path_lt_Some_length_unions[OF px]
        by (cases "?newest_union (?lca x y) x") simp_all
      ultimately show "?newest_union (?lca x y) x < Some (length (unions ufe_ds))"
        by simp
    qed
    ultimately show ?thesis
      using 3 ufe_union.prems(1-3)
      by (intro ufe_union.prems(6)[OF _ _ _ _ _ _ \<open>P x b\<close> \<open>P a y\<close>]) simp_all
  qed
qed

lemma explain'_dom_if_ufe_rep_of_eq:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "explain'_dom ufe_ds (x, y)"
  using assms
proof(induction rule: explain'_induct)
  case (eq x)
  then show ?case
    using explain'.domintros by blast
next
  case (newest_x x y ax bx)
  then have
    "find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y \<le>
    find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x"
    by order
  with newest_x show ?case
    by (intro explain'.domintros[where x = x and y = y]) fastforce+
next
  case (newest_y x y ay "by")
  then have
    "\<not> find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y \<le>
    find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x"
    by order
  with newest_y show ?case
    by (intro explain'.domintros[where x = x and y = y]) fastforce+
qed

lemma explain'_ufe_union:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "eff_union (uf_ds ufe_ds) a b"
  shows "explain' (ufe_union ufe_ds a b) x y = explain' ufe_ds x y"
  using assms
proof(induction rule: explain'_induct)
  case (eq x)
  then show ?case
    by simp
next
  case (newest_x x y ax bx)
  moreover from newest_x have
    "find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y \<le>
    find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x"
    by order
  moreover from newest_x have "explain'_dom ufe_ds (x, y)"
    using explain'_dom_if_ufe_rep_of_eq by blast
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
  note this[OF newest_x.prems newest_x.hyps(1-3)]
  ultimately show ?case
    by (auto simp: explain'.psimps Let_def)
next
  case (newest_y x y ay "by")
  moreover from newest_y have
    "\<not> find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y \<le>
    find_newest_on_path ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x"
    by order
  moreover from newest_y have "explain'_dom ufe_ds (x, y)"
    using explain'_dom_if_ufe_rep_of_eq by blast
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
  note this[OF newest_y.prems newest_y.hyps(1-3)]
  ultimately show ?case
    by (auto simp: explain'.psimps Let_def)
qed

lemma explain_eq_explain':
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows
    "explain (uf_ds ufe_init) (unions ufe_ds) x y = explain' ufe_ds x y"
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
  from ufe_union have in_Field_ufa_\<alpha>:
    "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
    by simp_all
  then interpret ufe_tree: ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales

  from ufe_union interpret ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
    using ufe_invars.ufe_invars_ufe_union by metis
  from ufe_union interpret ufe_tree_union: ufe_tree where ufe_ds = "ufe_union ufe_ds a b" and x = x
    by unfold_locales
  from ufe_union.prems(2,3) ufe_tree_union.x_in_verts have
    "y \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x)"
    using ufe_tree_union.in_verts_if_rep_of_eq by metis
  with ufe_tree_union.x_in_verts obtain px py where
    px: "ufe_tree_union.awalk (ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y) px x" and
    py: "ufe_tree_union.awalk (ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y) py y"
      (is "ufe_tree_union.awalk ?lca _ _")
    using ufe_tree_union.lca_ufa_lca ufe_tree_union.lca_reachableD ufe_tree_union.reachable_awalk
    by metis
  note this[THEN ufe_tree_union.find_newest_on_path_lt_Some_length_unions]
  moreover have "t < Some (Suc n) \<Longrightarrow> t \<le> Some n" for t n
    by (cases t) simp_all
  ultimately have find_newest_on_path_le:
    "find_newest_on_path (ufe_union ufe_ds a b) ?lca x \<le> Some (length (unions ufe_ds))"
    "find_newest_on_path (ufe_union ufe_ds a b) ?lca y \<le> Some (length (unions ufe_ds))"
    by simp_all
  from ufe_union.prems px py have find_newest_on_path_neq:
    "find_newest_on_path (ufe_union ufe_ds a b) ?lca x \<noteq>
      find_newest_on_path (ufe_union ufe_ds a b) ?lca y"
    if "x \<noteq> y"
    using that ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast

  from ufe_union.hyps(2) in_Field_ufa_\<alpha> ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    with ufe_union have
      "explain (uf_ds ufe_init) (unions (ufe_union ufe_ds a b)) x y =
      explain (uf_ds ufe_init) (unions ufe_ds) x y"
      using ufe_invars.uf_ds_ufe_ds_eq_ufa_unions
      by (cases "x = y") (simp_all add: Let_def)
    moreover have "explain' (ufe_union ufe_ds a b) x y = explain' ufe_ds x y"
      by (intro ufe_invars.explain'_ufe_union in_Field_ufa_\<alpha> ufe_union.hyps 1)
    moreover have
      "explain (uf_ds ufe_init) (unions ufe_ds) x y = explain' ufe_ds x y"
      by (intro ufe_union.IH in_Field_ufa_\<alpha> 1)
    ultimately show ?thesis
      by simp
  next
    case 2
    with ufe_union in_Field_ufa_\<alpha> have
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b"
      using ufa_lca_ufa_union by (metis uf_ds_ufe_union)
    moreover from this 2 in_Field_ufa_\<alpha> have
      "find_newest_on_path (ufe_union ufe_ds a b) ?lca x = Some (length (unions ufe_ds))"
      using ufe_invars.find_newest_on_path_ufe_union_if_rep_of_neq[OF ufe_union.hyps(2) _ _ px]
      by (metis uf_ds_ufe_union ufa_rep_of_ufa_rep_of)
    moreover from this 2 have
      "find_newest_on_path (ufe_union ufe_ds a b) ?lca y < Some (length (unions ufe_ds))"
      using find_newest_on_path_le find_newest_on_path_neq by fastforce
    moreover from calculation have
      "find_newest_on_path (ufe_union ufe_ds a b) ?lca y \<le>
        find_newest_on_path (ufe_union ufe_ds a b) ?lca x"
      by order
    moreover have "explain'_dom (ufe_union ufe_ds a b) (x, y)"
      by (intro ufe_invars_union.explain'_dom_if_ufe_rep_of_eq ufe_union.prems)
    moreover from ufe_union.hyps 2 in_Field_ufa_\<alpha> have
      "explain' (ufe_union ufe_ds a b) x a = explain' ufe_ds x a"
      "explain' (ufe_union ufe_ds a b) b y = explain' ufe_ds b y"
      using ufe_invars.explain'_ufe_union by simp_all
    moreover note "2"(2) "2"(3)[symmetric]
    note this[THEN ufe_union.IH[rotated -1]]
    ultimately show ?thesis
      using "2"(1) "2"(2,3)[symmetric] in_Field_ufa_\<alpha> ufe_union.hyps
      by (auto simp: ufe_invars.uf_ds_ufe_ds_eq_ufa_unions explain'.psimps)       
  next
    case 3
    with ufe_union in_Field_ufa_\<alpha> have
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b"
      using ufa_lca_ufa_union by (metis uf_ds_ufe_union)
    moreover from this 3 in_Field_ufa_\<alpha> have
      "find_newest_on_path (ufe_union ufe_ds a b) ?lca y = Some (length (unions ufe_ds))"
      using ufe_invars.find_newest_on_path_ufe_union_if_rep_of_neq[OF ufe_union.hyps(2) _ _ py]
      by (metis uf_ds_ufe_union ufa_rep_of_ufa_rep_of)
    moreover from this 3 have
      "find_newest_on_path (ufe_union ufe_ds a b) ?lca x < Some (length (unions ufe_ds))"
      using find_newest_on_path_le find_newest_on_path_neq by fastforce
    moreover from calculation have
      "\<not> find_newest_on_path (ufe_union ufe_ds a b) ?lca y \<le>
        find_newest_on_path (ufe_union ufe_ds a b) ?lca x"
      by order
    moreover have "explain'_dom (ufe_union ufe_ds a b) (x, y)"
      by (intro ufe_invars_union.explain'_dom_if_ufe_rep_of_eq ufe_union.prems)
    moreover from ufe_union.hyps 3 in_Field_ufa_\<alpha> have
      "explain' (ufe_union ufe_ds a b) x b = explain' ufe_ds x b"
      "explain' (ufe_union ufe_ds a b) a y = explain' ufe_ds a y"
      using ufe_invars.explain'_ufe_union by simp_all
    moreover note "3"(2) "3"(3)[symmetric]
    note this[THEN ufe_union.IH[rotated -1]]
    ultimately show ?thesis
      using "3"(1) "3"(2,3)[symmetric] in_Field_ufa_\<alpha> ufe_union.hyps
      by (auto simp: ufe_invars.uf_ds_ufe_ds_eq_ufa_unions explain'.psimps)   
  qed
qed

lemma proves_eq_explain:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "unions ufe_ds \<turnstile>\<^sub>= explain (uf_ds ufe_init) (unions ufe_ds) x y : (x, y)"
  using assms proves_eq_explain[OF eff_unions]
  by (metis uf_ds_ufe_ds_eq_ufa_unions ufa_\<alpha>_uf_ds_ufe_init)

end

definition ufe_union_rank where
  "ufe_union_rank ufe_ds x y \<equiv>
    let
      rep_x = ufe_rep_of ufe_ds x;
      rep_y = ufe_rep_of ufe_ds y
    in
      if rep_x \<noteq> rep_y then
        if ufa_rank (uf_ds ufe_ds) rep_x < ufa_rank (uf_ds ufe_ds) rep_y
          then ufe_union ufe_ds x y
          else ufe_union ufe_ds y x
      else ufe_ds"

definition "ufe_unions_rank \<equiv> foldl (\<lambda>ufe_ds (x, y). ufe_union_rank ufe_ds x y)"

lemma (in ufe_invars) ufe_invars_ufe_union_rank:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  defines "ufe_ds' \<equiv> ufe_union_rank ufe_ds x y"
  shows "ufe_invars ufe_init ufe_ds'"
  using assms(1,2) unfolding ufe_ds'_def ufe_union_rank_def
  by (auto simp: Let_def ufe_invars_axioms intro!: ufe_invars_ufe_union)

lemma (in ufe_init_invars) ufe_invars_ufe_unions_rank:
  assumes "valid_unions (uf_ds ufe_init) us"
  shows "ufe_invars ufe_init (ufe_unions_rank ufe_init us)"
  using assms
proof(induction us rule: rev_induct)
  case Nil
  have "ufe_invars ufe_init ufe_init"
    by (unfold_locales) simp_all
  with Nil show ?case
    unfolding ufe_unions_rank_def ufe_union_rank_def by simp
next
  case (snoc u us)
  then interpret ufe_invars ufe_init "ufe_unions_rank ufe_init us"
    by simp
   
  from snoc show ?case
    using ufe_invars_ufe_union_rank unfolding ufe_unions_rank_def
    by (auto simp: case_prod_beta ufe_invars.in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init)
qed

end
