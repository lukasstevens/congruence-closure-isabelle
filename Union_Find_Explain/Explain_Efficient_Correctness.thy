theory Explain_Efficient_Correctness
  imports Find_Newest_On_Path
begin

lemma neq_find_newest_on_path_ufa_lca_if_neq:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  assumes "x \<noteq> y"
  defines "lca_x_y \<equiv> ufe_lca ufe x y"
  shows "find_newest_on_path ufe lca_x_y x \<noteq> find_newest_on_path ufe lca_x_y y"
proof -
  interpret ufe_forest ufe .
  from assms have "lca lca_x_y x y"
    using verts_ufa_forest_of unfolding lca_x_y_def
    by (intro lca_ufa_lca) blast+
  then obtain px py where
    px: "awalk lca_x_y px x" and py: "awalk lca_x_y py y"
    by (meson lca_reachableD reachable_awalk)
  note find_newest_on_path_dom = this[THEN find_newest_on_path_dom]
  note find_newest_on_path_psimps = this[THEN find_newest_on_path.psimps]
  consider (lca_x) "x = lca_x_y" | (lca_y) "y = lca_x_y" | (not_lca) "lca_x_y \<noteq> x" "lca_x_y \<noteq> y"
    using \<open>x \<noteq> y\<close> by auto
  then show ?thesis
  proof cases
    case lca_x
    then have "find_newest_on_path ufe lca_x_y x = None"
      using find_newest_on_path_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_x have "find_newest_on_path ufe lca_x_y y \<noteq> None"
      using find_newest_on_path_eq_Max_au_of[OF py] by blast      
    ultimately show ?thesis
      by force
  next
    case lca_y
    then have "find_newest_on_path ufe lca_x_y y = None"
      using find_newest_on_path_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_y have "find_newest_on_path ufe lca_x_y x \<noteq> None"
      using find_newest_on_path_eq_Max_au_of[OF px] by blast      
    ultimately show ?thesis
      by force
  next
    case not_lca
    from not_lca px py have "px \<noteq> []" "py \<noteq> []"
      using awalk_empty_ends px by blast+
    from not_lca px py obtain ix iy where
      ix: "ix \<in> set px" "find_newest_on_path ufe lca_x_y x = Some (au_of ix)" and
      iy: "iy \<in> set py" "find_newest_on_path ufe lca_x_y y = Some (au_of iy)"
      using newest_on_pathE[unfolded newest_on_path_def]
      by (simp add: find_newest_on_path_eq_Max_au_of) metis
    moreover note disjoint_awalk_if_awalk_lca[OF \<open>lca lca_x_y x y\<close> \<open>x \<noteq> y\<close> px py]
    with ix iy have "ix \<noteq> iy"
      by blast
    moreover from px py ix iy have
      "ix \<in> arcs (ufe_forest_of ufe)" "iy \<in> arcs (ufe_forest_of ufe)"
      by blast+
    ultimately show ?thesis
      using inj_on_au_of_arcs ix iy by (fastforce dest: inj_onD)
  qed
qed

context
  fixes ufe a b
  assumes eff_union: "eff_union (uf_ds ufe) a b"
begin

lemma
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  defines "ufe' \<equiv> ufe_union ufe a b"
  defines "newest_x \<equiv> find_newest_on_path ufe (ufe_lca ufe x y) x"
  defines "newest_y \<equiv> find_newest_on_path ufe (ufe_lca ufe x y) y"
  shows ufe_lca_ufe_union_eq_if_ufe_rep_of_eq:
    "ufe_lca ufe' x y = ufe_lca ufe x y"
    and find_newest_on_path_ufe_union_ufe_lca:
    "find_newest_on_path ufe' (ufe_lca ufe x y) x = newest_x"
    "find_newest_on_path ufe' (ufe_lca ufe x y) y = newest_y"
    and find_newest_on_path_ufe_union_ufe_lca_lt_Some_length_unions:
    "newest_x < Some (length (unions ufe))"
    "newest_y < Some (length (unions ufe))"
    and find_newest_on_path_ufe_union_ufe_lca_neq:
    "x \<noteq> y \<Longrightarrow> newest_x \<noteq> newest_y"
    and unions_nth_find_newest_on_path_ufe_union_ufe_lca:
    "newest_x > newest_y \<Longrightarrow>
      unions ufe' ! the newest_x = unions ufe ! the newest_x"
    "newest_x < newest_y \<Longrightarrow>
      unions ufe' ! the newest_y = unions ufe ! the newest_y"
proof -
  interpret ufe_forest: ufe_forest ufe .

  interpret ufe_union_forest: ufe_forest "ufe_union ufe a b" .

  from eff_union assms(1-3) show lca_eq:
    "ufe_lca ufe' x y = ufe_lca ufe x y"
    using ufa_lca_ufa_union ufa_rep_of_ufa_union
    by (simp add: ufe'_def uf_ds_ufe_union_eq)

  from eff_union assms have ufe_rep_of_union_eq:
    "ufe_rep_of ufe' x = ufe_rep_of ufe' y"
    using ufa_rep_of_ufa_union by (simp add: uf_ds_ufe_union_eq)
  from assms have "ufe_forest.lca (ufe_lca ufe' x y) x y"
    using lca_eq ufe_forest.lca_ufa_lca verts_ufa_forest_of
    by simp
  then obtain px py where
    px: "ufe_forest.awalk (ufe_lca ufe' x y) px x" and
    py: "ufe_forest.awalk (ufe_lca ufe' x y) py y"
    using ufe_forest.lca_reachableD by (metis ufe_forest.reachable_awalk)
  moreover note find_newest_on_path_ufe_union[OF eff_union]
  moreover from assms ufe_rep_of_union_eq have
    "ufe_rep_of ufe (ufe_lca ufe' x y) = ufe_rep_of ufe x"
    using px ufe_forest.ufa_rep_of_eq_if_awalk by blast
  ultimately show newest_eq:
    "find_newest_on_path ufe' (ufe_lca ufe x y) x = newest_x"
    "find_newest_on_path ufe' (ufe_lca ufe x y) y = newest_y"
    using assms lca_eq ufe_forest.ufe_union_awalk_if_awalk[OF eff_union]
    by metis+

  note px py
  from this[THEN ufe_forest.find_newest_on_path_lt_Some_length_unions] show newest_lt:
    "newest_x < Some (length (unions ufe))"
    "newest_y < Some (length (unions ufe))"
    unfolding lca_eq newest_eq newest_x_def newest_y_def by blast+

  note neq_find_newest_on_path_ufa_lca_if_neq[OF assms(1-3)]
  then show "newest_x \<noteq> newest_y" if "x \<noteq> y"
    using that lca_eq newest_eq unfolding newest_x_def newest_y_def by simp

  from eff_union newest_lt show
    "newest_y < newest_x \<Longrightarrow>
      unions ufe' ! the newest_x = unions ufe ! the newest_x"
    "newest_y > newest_x \<Longrightarrow>
      unions ufe' ! the newest_y = unions ufe ! the newest_y"
    unfolding ufe'_def
    by (cases newest_x; cases newest_y; simp add: nth_append)+
qed

end

lemma explain'_pinduct[consumes 4, case_names eq newest_x newest_y]:
  assumes "explain'_dom ufe (x, y)"
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  assumes "\<And>x. x \<in> Field (ufe_\<alpha> ufe) \<Longrightarrow> P x x"
  assumes "\<And>x y ax bx.
    \<lbrakk> explain'_dom ufe (x, y)
    ; x \<in> Field (ufe_\<alpha> ufe); y \<in> Field (ufe_\<alpha> ufe)
    ; ufe_rep_of ufe x = ufe_rep_of ufe y
    ; x \<noteq> y
    ; find_newest_on_path ufe (ufe_lca ufe x y) x \<ge>
      find_newest_on_path ufe (ufe_lca ufe x y) y
    ; unions ufe ! the (find_newest_on_path ufe (ufe_lca ufe x y) x) = (ax, bx)
    ; P x ax; P bx y
    \<rbrakk> \<Longrightarrow> P x y"
  assumes "\<And>x y ay by.
    \<lbrakk> explain'_dom ufe (x, y)
    ; x \<in> Field (ufe_\<alpha> ufe); y \<in> Field (ufe_\<alpha> ufe)
    ; ufe_rep_of ufe x = ufe_rep_of ufe y
    ; x \<noteq> y
    ; \<not> find_newest_on_path ufe (ufe_lca ufe x y) x \<ge>
      find_newest_on_path ufe (ufe_lca ufe x y) y
    ; unions ufe ! the (find_newest_on_path ufe (ufe_lca ufe x y) y) = (ay, by)
    ; P x by; P ay y
    \<rbrakk> \<Longrightarrow> P x y"
  shows "P x y"
  using assms(1-4)
proof(induction rule: explain'.pinduct)
  case (1 x y)
  interpret ufe_forest ufe .

  from "1.prems" have "lca (ufe_lca ufe x y) x y"
    using verts_ufa_forest_of
    by (intro lca_ufa_lca) auto

  then obtain px py where
    px: "awalk (ufe_lca ufe x y) px x" and
    py: "awalk (ufe_lca ufe x y) py y"
    using lca_ufa_lca lca_reachableD by (metis reachable_awalk)

  consider
    (eq) "x = y" |
    (newest_x) ax bx where "x \<noteq> y"
      "find_newest_on_path ufe (ufe_lca ufe x y) x \<ge>
        find_newest_on_path ufe (ufe_lca ufe x y) y"
      "unions ufe ! the (find_newest_on_path ufe (ufe_lca ufe x y) x) = (ax, bx)" |
    (newest_y) ay "by" where "x \<noteq> y"
      "\<not> find_newest_on_path ufe (ufe_lca ufe x y) x \<ge>
        find_newest_on_path ufe (ufe_lca ufe x y) y"
      "unions ufe ! the (find_newest_on_path ufe (ufe_lca ufe x y) y) = (ay, by)"
    by (metis surj_pair)
  then show ?case
  proof cases
    case eq
    with 1 assms(5) show ?thesis
      by simp
  next
    case newest_x

    with neq_find_newest_on_path_ufa_lca_if_neq[OF "1.prems"] have
      "ufe_lca ufe x y \<noteq> x"
      using less_eq_option_None_is_None by fastforce
    note newest_on_path_find_newest_on_path[OF px this] this newest_x(3)
    note newest_on_path_valid_union[OF this] ufe_rep_of_eq_if_newest_on_path[OF this]
    with \<open>ufe_lca ufe x y \<noteq> x\<close> px py newest_x "1.prems" have
      "ax \<in> Field (ufe_\<alpha> ufe)" "bx \<in> Field (ufe_\<alpha> ufe)"
      "ufe_rep_of ufe x = ufe_rep_of ufe ax"
      "ufe_rep_of ufe y = ufe_rep_of ufe bx"
      using ufa_rep_of_eq_if_awalk by simp_all
    moreover note IH = "1.IH"(1,2)[OF \<open>x \<noteq> y\<close> HOL.refl HOL.refl HOL.refl
        newest_x(2) newest_x(3)[symmetric] HOL.refl]
    ultimately show ?thesis
      using "1.prems"
      by (intro assms(6)[OF "1.hyps" "1.prems" newest_x]) metis+
  next
    case newest_y
    with neq_find_newest_on_path_ufa_lca_if_neq[OF "1.prems"] have
      "ufe_lca ufe x y \<noteq> y"
      using less_eq_option_None_is_None by fastforce
    note newest_on_path_find_newest_on_path[OF py this] this newest_y(3)
    note newest_on_path_valid_union[OF this] ufe_rep_of_eq_if_newest_on_path[OF this]
    with \<open>ufe_lca ufe x y \<noteq> y\<close> px py newest_y "1.prems" have
      "ay \<in> Field (ufe_\<alpha> ufe)" "by \<in> Field (ufe_\<alpha> ufe)"
      "ufe_rep_of ufe x = ufe_rep_of ufe by"
      "ufe_rep_of ufe y = ufe_rep_of ufe ay"
      using ufa_rep_of_eq_if_awalk by simp_all
    moreover note IH = "1.IH"(3,4)[OF \<open>x \<noteq> y\<close> HOL.refl HOL.refl HOL.refl
        newest_y(2) newest_y(3)[symmetric] HOL.refl]
    ultimately show ?thesis
      using "1.prems"
      by (intro assms(7)[OF "1.hyps" "1.prems" newest_y]) metis+
  qed
qed

lemma explain'_dom_ufe_union:
  assumes "explain'_dom ufe (x, y)"
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  assumes "eff_union (uf_ds ufe) a b"
  shows "explain'_dom (ufe_union ufe a b) (x, y)"
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
    "find_newest_on_path ufe (ufe_lca ufe x y) x >
      find_newest_on_path ufe (ufe_lca ufe x y) y"
    using neq_find_newest_on_path_ufa_lca_if_neq by (metis less_le)
  with newest_x show ?case
    by (intro explain'.domintros[where x = x and y = y])
      (simp_all del: unions_ufe_union_eq_if_eff_union)
next
  case (newest_y x y ay "by")
  note
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    find_newest_on_path_ufe_union_ufe_lca
    find_newest_on_path_ufe_union_ufe_lca_neq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note [simp] = this[OF newest_y.prems]
  from newest_y have
    "find_newest_on_path ufe (ufe_lca ufe x y) x <
      find_newest_on_path ufe (ufe_lca ufe x y) y"
    by order
  with newest_y show ?case
    by (intro explain'.domintros[where x = x and y = y])
      (simp_all del: unions_ufe_union_eq_if_eff_union)
qed

lemma leq_Some_if_lt_Suc_Some:
  assumes "x < Some (Suc n)"
  shows "x \<le> Some n"
  using assms by (cases x) auto

lemma explain'_dom_if_ufe_rep_of_eq:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  shows "explain'_dom ufe (x, y)"
  using assms
proof(induction ufe arbitrary: x y rule: ufe_induct)
  case (init ufe x y)
  then have "x = y"
    by (meson IdD in_mono ufa_\<alpha>I)
  then show ?case
    using explain'.domintros by blast
next
  case (ufe_union ufe a b x y)

  interpret ufe_union_forest: ufe_forest "ufe_union ufe a b" .

  from ufe_union.prems have in_verts_ufe_union_forest:
    "x \<in> verts (ufe_forest_of (ufe_union ufe a b))"
    "y \<in> verts (ufe_forest_of (ufe_union ufe a b))"
    unfolding verts_ufa_forest_of by blast+

  with ufe_union.prems obtain px py where
    px: "ufe_union_forest.awalk (ufe_lca (ufe_union ufe a b) x y) px x" and
    py: "ufe_union_forest.awalk (ufe_lca (ufe_union ufe a b) x y) py y"
    using ufe_union_forest.lca_ufa_lca ufe_union_forest.lca_reachableD
    by (metis ufe_union_forest.reachable_awalk)

  from ufe_union.prems ufe_union.hyps have in_Field_ufe_\<alpha>:
    "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
    "a \<in> Field (ufe_\<alpha> ufe)" "b \<in> Field (ufe_\<alpha> ufe)"
    by simp_all
  from ufe_union.hyps this(1,2) ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    then show ?thesis
      by (intro explain'_dom_ufe_union ufe_union.IH ufe_union.hyps in_Field_ufe_\<alpha>)
  next
    case 2
    then have "explain'_dom ufe (x, a)" "explain'_dom ufe (b, y)"
      by (intro ufe_union.IH in_Field_ufe_\<alpha>; simp)+
    note this[THEN explain'_dom_ufe_union[OF _ _ _ _ ufe_union.hyps]]
    moreover note find_newest_on_path_ufe_union[OF ufe_union.hyps px]
    with 2 ufe_union.prems ufe_union.hyps have newest_x_eq:
      "find_newest_on_path (ufe_union ufe a b) (ufe_lca (ufe_union ufe a b) x y) x =
      Some (length (unions ufe))"
      using ufa_lca_ufa_union[OF ufe_union.hyps in_Field_ufe_\<alpha>(1,2)]
      by (metis eff_unionD uf_ds_ufe_union_eq_if_eff_union ufa_rep_of_ufa_rep_of)
    moreover have
      "find_newest_on_path (ufe_union ufe a b) (ufe_lca (ufe_union ufe a b) x y) x \<ge>
      find_newest_on_path (ufe_union ufe a b) (ufe_lca (ufe_union ufe a b) x y) y"
    proof -
      from 2 have "x \<noteq> y"
        by blast
      note neq_find_newest_on_path_ufa_lca_if_neq[OF ufe_union.prems this]
      moreover note ufe_union_forest.find_newest_on_path_lt_Some_length_unions[OF py]
      ultimately show ?thesis
        using ufe_union.hyps newest_x_eq leq_Some_if_lt_Suc_Some 
        by simp
    qed
    ultimately show ?thesis
      using 2 in_Field_ufe_\<alpha> ufe_union.hyps
      by (intro explain'.domintros[where x = x and y = y]) fastforce+
  next
    case 3
    then have "explain'_dom ufe (x, b)" "explain'_dom ufe (a, y)"
      by (intro ufe_union.IH in_Field_ufe_\<alpha>; simp)+
    note this[THEN explain'_dom_ufe_union[OF _ _ _ _ ufe_union.hyps]]
    moreover note find_newest_on_path_ufe_union[OF ufe_union.hyps py]
    with 3 ufe_union.prems ufe_union.hyps have newest_y_eq:
      "find_newest_on_path (ufe_union ufe a b) (ufe_lca (ufe_union ufe a b) x y) y =
      Some (length (unions ufe))"
      using ufa_lca_ufa_union[OF ufe_union.hyps in_Field_ufe_\<alpha>(1,2)]
      by (simp add: uf_ds_ufe_union_eq)
    moreover have
      "\<not> find_newest_on_path (ufe_union ufe a b) (ufe_lca (ufe_union ufe a b) x y) x \<ge>
      find_newest_on_path (ufe_union ufe a b) (ufe_lca (ufe_union ufe a b) x y) y"
    proof -
      from 3 have "x \<noteq> y"
        by blast
      note neq_find_newest_on_path_ufa_lca_if_neq[OF ufe_union.prems this]
      moreover note ufe_union_forest.find_newest_on_path_lt_Some_length_unions[OF px]
      ultimately show ?thesis
        using ufe_union.hyps newest_y_eq leq_Some_if_lt_Suc_Some
        using order_antisym_conv by auto
    qed
    ultimately show ?thesis
      using 3 in_Field_ufe_\<alpha> ufe_union.hyps
      by (intro explain'.domintros[where x = x and y = y]) fastforce+
  qed
qed

lemma explain'_ufe_union:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  assumes "eff_union (uf_ds ufe) a b"
  shows "explain' (ufe_union ufe a b) x y = explain' ufe x y"
  using explain'_dom_if_ufe_rep_of_eq[OF assms(1-3)] assms
proof(induction rule: explain'_pinduct)
  case (eq x)
  then show ?case
    by simp
next
  case (newest_x x y ax bx)
  moreover from newest_x.hyps have
    "find_newest_on_path ufe (ufe_lca ufe x y) y <
    find_newest_on_path ufe (ufe_lca ufe x y) x"
    using neq_find_newest_on_path_ufa_lca_if_neq[OF newest_x.hyps(2-4)]
    by force
  moreover from newest_x have "explain'_dom (ufe_union ufe a b) (x, y)"
    by (intro explain'_dom_if_ufe_rep_of_eq)
      (simp_all add: uf_ds_ufe_union_eq ufa_rep_of_ufa_union)
  moreover note
    find_newest_on_path_ufe_union_ufe_lca
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note this[OF newest_x.prems newest_x.hyps(2-4)]
  ultimately show ?case
    using explain'.psimps by fastforce
next
  case (newest_y x y ay "by")
  moreover from newest_y have
    "find_newest_on_path ufe (ufe_lca ufe x y) y >
    find_newest_on_path ufe (ufe_lca ufe x y) x"
    by order
  moreover from newest_y have "explain'_dom (ufe_union ufe a b) (x, y)"
    by (intro explain'_dom_if_ufe_rep_of_eq)
      (simp_all add: uf_ds_ufe_union_eq ufa_rep_of_ufa_union)
  moreover note
    find_newest_on_path_ufe_union_ufe_lca
    ufe_lca_ufe_union_eq_if_ufe_rep_of_eq
    unions_nth_find_newest_on_path_ufe_union_ufe_lca
  note this[OF newest_y.prems newest_y.hyps(2-4)]
  ultimately show ?case
    using explain'.psimps by fastforce
qed

lemma explain_eq_explain':
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  shows "explain ufe x y = explain' ufe x y"
  using assms                                                 
proof(induction arbitrary: x y rule: ufe_induct)
  case init
  then have "x = y"
    by (meson IdD subset_iff ufa_\<alpha>I)
  then show ?case
    by simp
next
  case (ufe_union ufe a b x y)
  interpret ufe_forest: ufe_forest ufe .
  interpret ufe_union_forest: ufe_forest "ufe_union ufe a b" .
  
  from ufe_union have in_Field_ufe_\<alpha>:
    "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
    by simp_all

  let ?ufe' = "ufe_union ufe a b"
  let ?newest_x = "find_newest_on_path ?ufe' (ufe_lca ?ufe' x y) x"
  let ?newest_y = "find_newest_on_path ?ufe' (ufe_lca ?ufe' x y) y"

  from ufe_union.prems obtain px py where
    px: "ufe_union_forest.awalk (ufe_lca (ufe_union ufe a b) x y) px x" and
    py: "ufe_union_forest.awalk (ufe_lca (ufe_union ufe a b) x y) py y"
    using ufe_union_forest.lca_ufa_lca ufe_union_forest.lca_reachableD ufe_union_forest.reachable_awalk
    unfolding verts_ufa_forest_of by metis
  note this[THEN ufe_union_forest.find_newest_on_path_lt_Some_length_unions]
  then have find_newest_on_path_le:
    "?newest_x \<le> Some (length (unions ufe))"
    "?newest_y \<le> Some (length (unions ufe))"
    using leq_Some_if_lt_Suc_Some by (simp_all add: ufe_union.hyps)
  from ufe_union.prems px py have find_newest_on_path_neq:
    "?newest_x \<noteq> ?newest_y" if "x \<noteq> y"
    using that neq_find_newest_on_path_ufa_lca_if_neq by blast

  have explain'_dom_x_y:
    "explain'_dom (ufe_union ufe a b) (x, y)"
     by (intro explain'_dom_if_ufe_rep_of_eq ufe_union.prems)

  from ufe_union.hyps in_Field_ufe_\<alpha> ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    with ufe_union have
      "explain (ufe_union ufe a b) x y = explain ufe x y"
      by (simp add: explain.simps)
    also have "\<dots> = explain' ufe x y"
      by (intro ufe_union.IH in_Field_ufe_\<alpha> 1)
    also have "\<dots> = explain' (ufe_union ufe a b) x y"
      using ufe_union.hyps 1
      by (intro explain'_ufe_union[symmetric] in_Field_ufe_\<alpha> eff_unionI) simp_all
    finally show ?thesis .
  next
    case 2
    let ?P = "\<lambda>p1 p2. TransP (TransP p1 (AssmP (length (unions ufe)))) p2"
    from 2 have "explain (ufe_union ufe a b) x y =
      ?P (explain ufe x a) (explain ufe b y)"
      by (simp add: explain.simps ufe_union.hyps)
    also from 2 ufe_union.hyps have "\<dots> =
      ?P (explain' ufe x a) (explain' ufe b y)"
      using in_Field_ufe_\<alpha> by (simp add: ufe_union.IH)
    also from 2 ufe_union.hyps have "\<dots> =
      ?P (explain' (ufe_union ufe a b) x a) (explain' (ufe_union ufe a b) b y)"
      using in_Field_ufe_\<alpha> \<open>eff_union (uf_ds ufe) a b\<close>
      by (simp add: explain'_ufe_union)
    also have "\<dots> = explain' (ufe_union ufe a b) x y"
    proof -
      from 2 ufe_union in_Field_ufe_\<alpha> have
      "ufe_lca (ufe_union ufe a b) x y = ufe_rep_of ufe b"
        unfolding uf_ds_ufe_union_eq_if_eff_union[OF ufe_union.hyps]
        using ufa_lca_ufa_union \<open>eff_union (uf_ds ufe) a b\<close> by metis
      moreover from this 2 in_Field_ufe_\<alpha> have
        "?newest_x = Some (length (unions ufe))"
        using find_newest_on_path_ufe_union[OF \<open>eff_union (uf_ds ufe) a b\<close> px]
        by (metis ufa_rep_of_ufa_rep_of)
      moreover from this 2 have
        "?newest_y < Some (length (unions ufe))"
        using find_newest_on_path_le find_newest_on_path_neq by fastforce
      moreover from calculation have
        "?newest_y \<le> ?newest_x"
        by order
      moreover from 2 have "x \<noteq> y"
        by blast
      ultimately show ?thesis
        unfolding explain'.psimps[OF explain'_dom_x_y]
        by (simp add: ufe_union.hyps)
    qed
    finally show ?thesis .      
  next
    case 3
    let ?P = "\<lambda>p1 p2. TransP (TransP p1 (SymP (AssmP (length (unions ufe))))) p2"
    from 3 have "explain (ufe_union ufe a b) x y =
      ?P (explain ufe x b) (explain ufe a y)"
      by (simp add: explain.simps ufe_union.hyps)
    also from 3 ufe_union.hyps have "\<dots> =
      ?P (explain' ufe x b) (explain' ufe a y)"
      using in_Field_ufe_\<alpha> by (simp add: ufe_union.IH)
    also from 3 ufe_union.hyps have "\<dots> =
      ?P (explain' (ufe_union ufe a b) x b) (explain' (ufe_union ufe a b) a y)"
      using in_Field_ufe_\<alpha> \<open>eff_union (uf_ds ufe) a b\<close>
      by (simp add: explain'_ufe_union)
    also have "\<dots> = explain' (ufe_union ufe a b) x y"
    proof -
      from 3 ufe_union in_Field_ufe_\<alpha> have
      "ufe_lca (ufe_union ufe a b) x y = ufe_rep_of ufe b"
        unfolding uf_ds_ufe_union_eq_if_eff_union[OF ufe_union.hyps]
        using ufa_lca_ufa_union \<open>eff_union (uf_ds ufe) a b\<close> by metis
      moreover from this 3 in_Field_ufe_\<alpha> have
        "?newest_y = Some (length (unions ufe))"
        using find_newest_on_path_ufe_union[OF \<open>eff_union (uf_ds ufe) a b\<close> py]
        by (metis ufa_rep_of_ufa_rep_of)
      moreover from this 3 have
        "?newest_x < Some (length (unions ufe))"
        using find_newest_on_path_le find_newest_on_path_neq by fastforce
      moreover from calculation have
        "\<not> ?newest_y \<le> ?newest_x"
        by order
      moreover from 3 have "x \<noteq> y"
        by blast
      ultimately show ?thesis
        unfolding explain'.psimps[OF explain'_dom_x_y]
        by (simp add: ufe_union.hyps)
    qed
    finally show ?thesis .   
  qed
qed

definition ufe_union_size where
  "ufe_union_size ufe x y \<equiv>
    let
      rep_x = ufe_rep_of ufe x;
      rep_y = ufe_rep_of ufe y
    in
      if rep_x = rep_y then ufe
      else
        if ufa_size (uf_ds ufe) rep_x < ufa_size (uf_ds ufe) rep_y
          then ufe_union ufe x y
          else ufe_union ufe y x"

lemma ufe_\<alpha>_ufe_union_size:
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  shows "ufe_\<alpha> (ufe_union_size ufe x y) = per_union (ufe_\<alpha> ufe) x y"
proof -
  from assms have "per_union (ufe_\<alpha> ufe) x y = ufe_\<alpha> ufe"
    if "ufe_rep_of ufe x = ufe_rep_of ufe y"
    using that 
    by (simp add: part_equiv_ufa_\<alpha> per_union_cmp ufa_\<alpha>I)
  then show ?thesis
    using assms unfolding ufe_union_size_def
    by (simp add: Let_def ufe_\<alpha>_ufe_union_eq_per_union del: ufa_size_ufa_rep_of)
qed

end
