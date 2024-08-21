theory Find_Newest_On_Path
  imports UFE_Tree
begin

lemma find_newest_on_path_dom_parent_of:
  assumes "find_newest_on_path_dom ufe_ds (y, x)" "x \<noteq> y"
  shows "find_newest_on_path_dom ufe_ds (y, ufe_parent_of ufe_ds x)"
  using assms find_newest_on_path.domintros
  by (induction rule: find_newest_on_path.pinduct) blast

lemma find_newest_on_path_eq_if_eq[simp]:
  assumes "y = x"
  shows "find_newest_on_path ufe_ds y x = None"
  using assms
  by (metis find_newest_on_path.domintros find_newest_on_path.pelims)

context ufe_tree
begin

lemma find_newest_on_path_dom:
  assumes "awalk y p z"
  shows "find_newest_on_path_dom ufe_ds (y, z)"
proof -
  from assms have "z \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
    by blast
  then have "z \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
    by blast
  show ?thesis
  proof(cases "p = []")
    case True
    then show ?thesis
      using assms awalk_empty_ends find_newest_on_path.domintros by blast
  next
    case False
    with \<open>z \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))\<close> assms show ?thesis
    proof(induction arbitrary: p rule: ufa_rep_of_induct)
      case (rep i)
      then show ?case
        using awalk_and_parent_of_reflD(2) by blast
    next
      case (not_rep i)
      then have "awalk y (butlast p) (ufe_parent_of ufe_ds i)"
        using awalk_not_Nil_butlastD(1) awalk_Nil_iff
        by (simp add: awlast_butlast_eq_parent_of_if_awalk)
      with not_rep have
        "find_newest_on_path_dom ufe_ds (y, ufe_parent_of ufe_ds i)"
        by (metis awalk_empty_ends find_newest_on_path.domintros)
      then show ?case
        using find_newest_on_path.domintros by blast
    qed
  qed
qed

lemma find_newest_on_path_eq_Max_au_of:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "find_newest_on_path ufe_ds y z = Some (Max (au_of ` set p))"
proof -
  from find_newest_on_path_dom[OF assms(1)] assms show ?thesis
  proof(induction arbitrary: p rule: find_newest_on_path.pinduct)
    case (1 y z)
    then have "z \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
      using in_Field_ufa_\<alpha>_if_in_verts awalk_last_in_verts by blast
    with "1.prems" obtain au_z where au_z:
      "au_ds ufe_ds z = Some au_z"
      using lookup_au_ds_eq_None_iff ufa_parent_of_ufa_rep_of
      by (metis awalk_and_parent_of_reflD(1) not_None_eq)
    then show ?case
    proof(cases "y = ufe_parent_of ufe_ds z")
      case True
      with "1.prems" have p_eq: "p = [(ufe_parent_of ufe_ds z, z)]" (is "_ = [?a]")
        using awalk_parent_of unique_awalk_All by blast
      with "1.prems" au_z show ?thesis
        unfolding au_of_def find_newest_on_path.psimps[OF "1.hyps"]
        by (auto simp: combine_options_def split: option.splits)
    next
      case False 
      from 1 have "p \<noteq> []"
        by auto
      with 1 have
        awalk_butlast: "awalk y (butlast p) (ufe_parent_of ufe_ds z)" and
        awalk_last: "awalk (ufe_parent_of ufe_ds z) [last p] z"
        using awalk_not_Nil_butlastD
        by (metis awlast_butlast_eq_parent_of_if_awalk)+
      with awalk_verts_append[where ?p="butlast p" and ?q="[last p]"]
      have awalk_verts_p:
        "awalk_verts y p = awalk_verts y (butlast p) @ [z]"
        using \<open>awalk y p z\<close> \<open>p \<noteq> []\<close> by auto

      from \<open>z \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))\<close> have
        "ufe_parent_of ufe_ds z \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
        by blast
      with False obtain au_p_z where au_p_z:
        "au_ds ufe_ds (ufe_parent_of ufe_ds z) = Some au_p_z"
        using lookup_au_ds_eq_None_iff ufa_parent_of_ufa_rep_of
        by (metis awalk_and_parent_of_reflD(1) awalk_butlast domD domIff)
      
      from \<open>y \<noteq> z\<close> au_z au_p_z have
        "find_newest_on_path ufe_ds y z =
        combine_options max (Some au_z) (find_newest_on_path ufe_ds y (ufe_parent_of ufe_ds z))"
      proof -
        have "find_newest_on_path_dom ufe_ds (y, ufe_parent_of ufe_ds z)"
          using awalk_butlast find_newest_on_path_dom by blast
        with False au_p_z have
          "find_newest_on_path ufe_ds y (ufe_parent_of ufe_ds z) \<noteq> None"
          by (auto simp: find_newest_on_path.psimps combine_options_def split: option.splits)
        with "1.prems" au_z show ?thesis 
          unfolding find_newest_on_path.psimps[OF "1.hyps"(1)] by fastforce
      qed
      also have "\<dots> = Some (max au_z (Max (au_of ` set (butlast p))))"
      proof -
        note "1.IH"[OF \<open>y \<noteq> z\<close> \<open>awalk y (butlast p) (ufe_parent_of ufe_ds z)\<close>
            \<open>y \<noteq> ufe_parent_of ufe_ds z\<close>]
        then show ?thesis
          unfolding newest_on_path_def by simp
      qed
      also have "\<dots> = Some (Max (au_of ` set p))"
      proof -
        from \<open>p \<noteq> []\<close> have "p = butlast p @ [last p]"
          by simp
        from 1 have "distinct p"
          using distinct_awalk_verts distinct_verts_imp_distinct by blast
        then have "distinct (map au_of (butlast p @ [last p]))"
          using \<open>p = butlast p @ [last p]\<close> 
          using distinct_map inj_on_au_of_awalk[OF \<open>awalk y p z\<close>] by metis
        then have "au_of (last p) \<notin> au_of ` set (butlast p)"
          by fastforce
        from Max.insert_not_elem[OF _ this] False
        have "Max (insert (au_of (last p)) (au_of ` set (butlast p)))
          = max (au_of (last p)) (Max (au_of ` set (butlast p)))"
          using awalk_butlast awalk_ends by blast
        then have "\<dots> = Max (au_of ` set p)"
          using \<open>au_of (last p) \<notin> au_of ` set (butlast p)\<close>
          by (subst (3) \<open>p = butlast p @ [last p]\<close>) simp
        with au_z show ?thesis
          by (metis au_of_def awalk_Cons_iff awalk_ends awalk_last option.sel)
      qed
      finally show ?thesis .
    qed
  qed
qed

lemma find_newest_on_path_eq_None_iff:
  assumes "awalk y p z"
  shows "find_newest_on_path ufe_ds y z = None \<longleftrightarrow> y = z"
  using find_newest_on_path_dom[OF assms] assms
proof(induction rule: find_newest_on_path.pinduct)
  case (1 y z)
  then show ?case
    using find_newest_on_path_eq_Max_au_of by (cases "y = z") simp_all
qed
  
theorem newest_on_path_find_newest_on_path:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "newest_on_path (the (find_newest_on_path ufe_ds y z)) y p z"
  using find_newest_on_path_eq_Max_au_of[OF assms] \<open>awalk y p z\<close>
  unfolding newest_on_path_def
  by simp

end

lemma (in ufe_tree) find_newest_on_path_lt_Some_length_unions:
  assumes "awalk y p z"
  shows "find_newest_on_path ufe_ds y z < Some (length (unions ufe_ds))"
proof(cases "y = z")
  case True
  then show ?thesis by simp
next
  case False
  with assms have "newest_on_path (the (find_newest_on_path ufe_ds y z)) y p z"
    using newest_on_path_find_newest_on_path by blast
  with False newest_on_path_lt_length_unions show ?thesis
    by (cases "find_newest_on_path ufe_ds y z") auto
qed

lemma ufe_rep_of_ufe_union_eq_cases:
  assumes "eff_union (uf_ds ufe_ds) a b"
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y"
  obtains
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y" |
    "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds a" "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds b" |
    "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds b" "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds a"
  using assms
  by (metis eff_unionD(1,2) uf_ds_ufe_union ufa_rep_of_ufa_union)

lemma (in ufe_invars) find_newest_on_path_ufe_union_if_rep_of_neq:
  assumes "eff_union (uf_ds ufe_ds) a b"
  assumes "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  assumes "uf_ds (ufe_union ufe_ds a b) = ufa_union (uf_ds ufe_ds) a b"
  assumes awalk_pxy:
    "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z) x pxy y"
  shows "find_newest_on_path (ufe_union ufe_ds a b) x y = Some (length (unions ufe_ds))"
proof -
  from assms ufe_invars_ufe_union interpret ufe_invars_union: ufe_invars
    where ufe_ds = "ufe_union ufe_ds a b"
    by blast
  from assms have "z \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
    unfolding pre_digraph.awalk_def
    by (metis in_ufa_\<alpha>_if_in_verts in_vertsI part_equiv_trans_sym(1) part_equiv_ufa_\<alpha>)

  with assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and x = z
    by unfold_locales blast

  from assms awalk_pxy have
    "x \<in> Field (ufa_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    "y \<in> Field (ufa_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    by blast+
  with assms have
    x_in_Field_\<alpha>: "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
    using Field_ufa_\<alpha>_uf_ds_ufe_union by blast+

  from x_in_Field_\<alpha> interpret ufe_tree_x: ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales
  from y_in_Field_\<alpha> interpret ufe_tree_y: ufe_tree where ufe_ds = ufe_ds and x = y
    by unfold_locales
  interpret ufe_tree_z: ufe_tree where ufe_ds = ufe_ds and x = z
    using assms ufe_tree_union.x_in_Field_\<alpha> Field_ufa_\<alpha>_uf_ds_ufe_union
    by unfold_locales blast+

  from assms have
    rep_a_in_Field_\<alpha>: "ufe_rep_of ufe_ds a \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
      (is "?rep_a \<in> _") and
    rep_b_in_Field_\<alpha>: "ufe_rep_of ufe_ds b \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
      (is "?rep_b \<in> _")
    by blast+
  note this[THEN ufe_tree_x.awalk_from_rep_union[OF eff_unionD[OF assms(1)]]]
  then have awalk_from_rep_union_rep_a:
    "awalk_from_rep (uf_ds (ufe_union ufe_ds a b)) (ufe_rep_of ufe_ds a) =
    awalk_from_rep (uf_ds ufe_ds) (ufe_rep_of ufe_ds b) @ [(?rep_b, ?rep_a)]"
    using assms awalk_from_rep_rep_of by simp

  from awalk_pxy have
    "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y"
    by fastforce
  note rep_of_union_eq_assms = x_in_Field_\<alpha> y_in_Field_\<alpha> this assms(1-4)
  then consider
    "ufe_rep_of ufe_ds x = ?rep_a" "ufe_rep_of ufe_ds y = ?rep_b" |
    "ufe_rep_of ufe_ds x = ?rep_b" "ufe_rep_of ufe_ds y = ?rep_a"
    using ufe_rep_of_ufe_union_eq_cases by blast
  then show ?thesis
  proof cases
    case 1
    then have
      "ufe_tree_x.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufe_tree_x.awalk_awalk_from_rep by fastforce
    note ufe_tree_x.union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x)
        ?rep_a (awalk_from_rep (uf_ds ufe_ds) x) x"
      by fastforce
    then have union_awalk_awalk_from_rep_x:
      "ufe_tree_union.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy ufe_tree_union.awalkE')
    moreover
    from 1 have
      "ufe_tree_y.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufe_tree_y.awalk_awalk_from_rep by fastforce
    note ufe_tree_y.union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) y)
        ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
      by fastforce
    then have union_awalk_awalk_from_rep_y:
      "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy ufe_tree_union.awalkE')
    moreover
    have "ufe_tree_union.awalk ?rep_b [(?rep_b, ?rep_a)] ?rep_a"
    proof -
      from calculation have "?rep_a \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
        by blast
      note ufe_tree_union.awalk_awalk_from_rep[OF this]
      then show ?thesis
        using assms awalk_from_rep_union_rep_a awalk_from_rep_rep_of
        by simp
    qed
    ultimately have
      "ufe_tree_union.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
      using awalk_pxy ufe_tree_union.awalk_Cons_iff ufe_tree_union.awalk_appendI
      by auto
    then have
      "ufe_tree_y.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
      using 1 union_awalk_awalk_from_rep_y ufe_tree_union.unique_awalk_All
      by (metis ufe_tree_y.awalk_awalk_from_rep ufe_tree_y.x_in_verts)
    with 1 have "ufe_tree_y.awalk x pxy y"
      using ufe_tree_x.awlast_awalk_from_rep[OF ufe_tree_x.x_in_verts]
      by (simp add: ufe_tree_y.awalk_Cons_iff awalk_verts_with_proj_eq)
    with \<open>ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y\<close> show ?thesis
      by auto
  next
    case 2
    then have x_awalk_awalk_from_rep_x:
      "ufe_tree_x.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufe_tree_x.awalk_awalk_from_rep by fastforce
    note ufe_tree_x.union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x)
        ?rep_b (awalk_from_rep (uf_ds ufe_ds) x) x"
      by fastforce
    then have union_awalk_awalk_from_rep_x:
      "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy ufe_tree_union.awalkE')
    moreover
    from 2 have y_awalk_awalk_from_rep_y:
      "ufe_tree_y.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufe_tree_y.awalk_awalk_from_rep by fastforce
    note ufe_tree_y.union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) y)
        ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
      by fastforce
    then have union_awalk_awalk_from_rep_y:
      "ufe_tree_union.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy ufe_tree_union.awalkE')
    moreover
    from 2 have "ufe_tree_union.awalk ?rep_b [(?rep_b, ?rep_a)] ?rep_a"
    proof -
      from calculation have "?rep_a \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
        by blast
      note ufe_tree_union.awalk_awalk_from_rep[OF this]
      then show ?thesis
        using assms(1,3) awalk_from_rep_rep_of awalk_from_rep_union_rep_a by auto
    qed
    ultimately have union_awalk_rep_b_y:
      "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
      "ufe_tree_union.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) y) y"
      using awalk_pxy ufe_tree_union.awalk_Cons_iff ufe_tree_union.awalk_appendI
      by auto

    have "awalk_from_rep (uf_ds ufe_ds) x = []"
    proof(rule ccontr)
      assume "awalk_from_rep (uf_ds ufe_ds) x \<noteq> []"
      then obtain es where "awalk_from_rep (uf_ds ufe_ds) x = (?rep_b, ?rep_a) # es"
        using union_awalk_rep_b_y y_awalk_awalk_from_rep_y 
        by (metis (no_types, lifting) Cons_eq_append_conv ufe_tree_union.unique_awalk_All)
      with union_awalk_rep_b_y have "awalk_from_rep (uf_ds ufe_ds) y = es @ pxy"
        using ufe_tree_union.unique_awalk_All by auto
      with y_awalk_awalk_from_rep_y have
        "ufe_tree_y.awalk (ufe_tree_y.awlast ?rep_a es) pxy y"
        by simp
      moreover from union_awalk_awalk_from_rep_y have
        "ufe_tree_union.awalk (ufe_tree_y.awlast ?rep_a es) pxy y"
        using \<open>awalk_from_rep (uf_ds ufe_ds) y = es @ pxy\<close> 
        by (metis awalk_verts_with_proj_eq ufe_tree_union.awalk_append_iff)
      ultimately have "ufe_tree_y.awalk x pxy y"
        using ufe_tree_union.awalk_ends[OF awalk_pxy] by metis
      then have "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
        using ufe_tree_y.awalk_hd_in_verts by auto
      with \<open>ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y\<close> show False
        by blast
    qed
    then have "?rep_b = x"
      using x_awalk_awalk_from_rep_x by auto
    with awalk_pxy union_awalk_rep_b_y have "(?rep_b, ?rep_a) \<in> set pxy"
      using ufe_tree_union.unique_awalk_All
      by (metis list.set_intros(1))
    moreover
    have "ufe_tree_union.au_of (?rep_b, ?rep_a) = length (unions ufe_ds)"
      using assms(3) unfolding ufe_tree_union.au_of_def
      by simp
    moreover have "ufe_tree_union.au_of e < length (unions (ufe_union ufe_ds a b))"
      if "e \<in> set pxy" for e
      using that awalk_pxy ufe_tree_union.au_of_lt_length_unions
      by (meson subsetD ufe_tree_union.awalkE')
    then have "ufe_tree_union.au_of e \<le> length (unions ufe_ds)"
      if "e \<in> set pxy" for e
      using that assms(3) by (simp add: less_Suc_eq order_le_less)
    ultimately have "Max (ufe_tree_union.au_of ` set pxy) = length (unions ufe_ds)"
      by (intro Max_eqI) (auto simp: rev_image_eqI)
    moreover note ufe_tree_union.find_newest_on_path_eq_Max_au_of[OF awalk_pxy]
    ultimately show ?thesis
      using \<open>ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y\<close> by auto
  qed
qed


lemma (in ufe_invars) find_newest_on_path_ufe_union:
  assumes "eff_union (uf_ds ufe_ds) a b"
  assumes awalk_pxy:
    "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z) x pxy y"
  shows "find_newest_on_path (ufe_union ufe_ds a b) x y = 
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y then find_newest_on_path ufe_ds x y
    else Some (length (unions ufe_ds)))"
proof -
  from assms ufe_invars_ufe_union interpret ufe_invars_union: ufe_invars
    where ufe_ds = "ufe_union ufe_ds a b" 
    by blast
  from assms have "z \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
    unfolding pre_digraph.awalk_def
    by (metis in_ufa_\<alpha>_if_in_verts in_vertsI part_equiv_trans_sym(1) part_equiv_ufa_\<alpha>)

  with assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and x = z
    by unfold_locales blast

  from assms awalk_pxy have
    "x \<in> Field (ufa_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    "y \<in> Field (ufa_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    by blast+
  with assms have
    x_in_Field_\<alpha>: "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
    using Field_ufa_\<alpha>_uf_ds_ufe_union by blast+

  from x_in_Field_\<alpha> interpret ufe_tree_x: ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales
  from y_in_Field_\<alpha> interpret ufe_tree_y: ufe_tree where ufe_ds = ufe_ds and x = y
    by unfold_locales
  interpret ufe_tree_z: ufe_tree where ufe_ds = ufe_ds and x = z
    using assms ufe_tree_union.x_in_Field_\<alpha> Field_ufa_\<alpha>_uf_ds_ufe_union
    by unfold_locales blast+

  have ?thesis if "x \<noteq> y" "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  proof -
    from awalk_pxy have "x \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
      by blast
    note ufa_tree_of_eq_if_in_verts[OF this]
    with assms(2) that awalk_pxy have "ufe_tree_x.awalk x pxy y"
      by (intro ufe_tree_x.awalk_if_ufe_union_awalk[OF assms(1)]) simp_all
    with that have
      "find_newest_on_path ufe_ds x y = Some (Max (ufe_tree_x.au_of ` set pxy))"
      using ufe_tree_x.find_newest_on_path_eq_Max_au_of by blast
    moreover from that awalk_pxy have
      "find_newest_on_path (ufe_union ufe_ds a b) x y =
      Some (Max (ufe_tree_union.au_of ` set pxy))"
      using ufe_tree_union.find_newest_on_path_eq_Max_au_of by blast
    moreover have "ufe_tree_x.au_of e = ufe_tree_union.au_of e" if "e \<in> set pxy" for e
    proof -
      from assms have "ufe_rep_of ufe_ds a \<notin> dom (au_ds ufe_ds)"
        using lookup_au_ds_eq_None_iff ufa_rep_of_in_Field_ufa_\<alpha>I ufa_rep_of_ufa_rep_of
        by blast
      moreover note ufe_tree_x.head_in_dom_lookup_if_in_arcs
      with that have "head (ufa_tree_of (uf_ds ufe_ds) x) e \<in> dom (au_ds ufe_ds)"
        using \<open>ufe_tree_x.awalk x pxy y\<close> by blast
      ultimately show ?thesis
        using assms(2) lookup_au_ds_eq_None_iff[where z="ufe_rep_of ufe_ds b"]
        unfolding ufe_tree_x.au_of_def ufe_tree_union.au_of_def au_ds_ufe_union                  
        by auto
    qed
    ultimately show ?thesis
      using that by simp
  qed
  moreover have ?thesis if "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    using assms awalk_pxy that find_newest_on_path_ufe_union_if_rep_of_neq by auto
  ultimately show ?thesis
    by force
qed

end