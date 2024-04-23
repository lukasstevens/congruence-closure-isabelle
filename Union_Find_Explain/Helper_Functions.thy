section \<open>Correctness proofs for the helper functions\<close>
theory Helper_Functions
  imports Explain_Definition UFE_Tree 
begin 

subsection \<open>Proofs about the domain of the helper functions\<close>

theorem (in ufa_tree) lca_ufa_lca:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "z \<in> verts (ufa_tree_of uf x)"
  shows "lca (ufa_lca uf y z) y z"
proof -
  from assms have "uf_rep_of uf y = uf_rep_of uf z"
    by simp
  note assms[THEN awalk_awalk_from_rep, folded this]
  note lca_last_longest_common_prefix_awalk_verts[OF this]
  with \<open>uf_rep_of uf y = uf_rep_of uf z\<close> show ?thesis
    unfolding ufa_lca_def
    unfolding assms[THEN awalk_verts_from_rep_eq_awalk_verts]
    by simp
qed

theorem (in ufa_tree) rep_of_ufa_lca:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "z \<in> verts (ufa_tree_of uf x)"
  shows "uf_rep_of uf (ufa_lca uf y z) = uf_rep_of uf y"
proof -
  note lca_ufa_lca[OF assms]
  then have "ufa_lca uf y z \<in> verts (ufa_tree_of uf x)"
    using lca_reachableD(2) reachable_in_verts(1) by blast
  with assms show ?thesis
    by simp
qed


context union_find_parent_unions
begin

lemma ufa_lca_union:
  assumes "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of uf a \<noteq> uf_rep_of uf b"
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_union uf a b) x = uf_rep_of (uf_union uf a b) y"
  shows "ufa_lca (uf_union uf a b) x y =
    (if uf_rep_of uf x = uf_rep_of uf y then ufa_lca uf x y else uf_rep_of uf b)"
proof -
  interpret ufp_unions_union: union_find_parent_unions where
    uf = "uf_union uf a b" and us = "us @ [(a, b)]"
    using assms union_find_parent_unions_union by blast

  interpret ufa_tree_x: ufa_tree where x = x
    using assms by unfold_locales
  interpret ufa_tree_y: ufa_tree where x = y
    using assms by unfold_locales

  note awalk_verts_from_rep_union_eq = 
    assms(4,5)[THEN ufa_tree_x.awalk_verts_from_rep_union[OF assms(1-3)]]
  
  show ?thesis
  proof(cases "uf_rep_of uf x = uf_rep_of uf y")
    case True
    with \<open>x \<in> Field (uf_\<alpha> uf)\<close> \<open>y \<in> Field (uf_\<alpha> uf)\<close>
    have "x \<in> verts (ufa_tree_of uf x)" "y \<in> verts (ufa_tree_of uf x)"
      using \<alpha>_rep_of in_vertsI by blast+
    note this[THEN ufa_tree_x.awalk_verts_from_rep_eq_Cons]
    with True obtain px py where
      "awalk_verts_from_rep uf x = uf_rep_of uf y # px"
      "awalk_verts_from_rep uf y = uf_rep_of uf y # py"
      by metis
    then have
      "longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y) \<noteq> []"
      by simp
  
    with True show ?thesis
      unfolding ufa_lca_def awalk_verts_from_rep_union_eq
      by auto
  next
    case False
    with assms consider
      "uf_rep_of uf x = uf_rep_of uf a" "uf_rep_of uf y = uf_rep_of uf b" |
      "uf_rep_of uf x = uf_rep_of uf b" "uf_rep_of uf y = uf_rep_of uf a"
      by (metis rep_of_union)
    then show ?thesis
    proof(cases)
      case 1
      from 1 obtain px where awalk_verts_from_rep_x:
        "awalk_verts_from_rep uf x = uf_rep_of uf a # px"
        using ufa_tree_x.awalk_verts_from_rep_eq_Cons[OF ufa_tree_x.x_in_verts]
        by metis
      from 1 obtain py where awalk_verts_from_rep_y:
        "awalk_verts_from_rep uf y = uf_rep_of uf b # py"
        using ufa_tree_y.awalk_verts_from_rep_eq_Cons[OF ufa_tree_y.x_in_verts]
        by metis

      have "longest_common_prefix (awalk_verts_from_rep uf x) py = []"
      proof(rule ccontr)
        assume "longest_common_prefix (awalk_verts_from_rep uf x) py \<noteq> []"
        then obtain py' where "py = uf_rep_of uf a # py'"
          unfolding awalk_verts_from_rep_x by (cases py) force+
        with assms(1) show "False"
          using ufa_tree_y.awalk_awalk_from_rep
              ufa_tree_y.awalk_verts_from_rep_eq_awalk_verts
              ufa_tree_y.not_rep_if_in_tl_awalk_verts
              ufa_tree_y.x_in_verts
          using awalk_verts_from_rep_y
          by (metis list.sel(3) list.set_intros(1) parent_of_rep_of )
      qed

      with assms 1 show ?thesis
        unfolding ufa_lca_def awalk_verts_from_rep_union_eq awalk_verts_from_rep_y
        by auto
    next
      case 2
      from 2 obtain px where awalk_verts_from_rep_x:
        "awalk_verts_from_rep uf x = uf_rep_of uf b # px"
        using ufa_tree_x.awalk_verts_from_rep_eq_Cons[OF ufa_tree_x.x_in_verts]
        by metis
      from 2 obtain py where awalk_verts_from_rep_y:
        "awalk_verts_from_rep uf y = uf_rep_of uf a # py"
        using ufa_tree_y.awalk_verts_from_rep_eq_Cons[OF ufa_tree_y.x_in_verts]
        by metis

      have "longest_common_prefix px (awalk_verts_from_rep uf y) = []"
      proof(rule ccontr)
        assume "longest_common_prefix px (awalk_verts_from_rep uf y) \<noteq> []"
        then obtain px' where "px = uf_rep_of uf a # px'"
          unfolding awalk_verts_from_rep_y by (cases px) force+
        with assms(1) show "False"
          using ufa_tree_x.awalk_awalk_from_rep
              ufa_tree_x.awalk_verts_from_rep_eq_awalk_verts
              ufa_tree_x.not_rep_if_in_tl_awalk_verts
              ufa_tree_x.x_in_verts
          using awalk_verts_from_rep_x
          by (metis list.sel(3) list.set_intros(1) parent_of_rep_of )
      qed

      with assms 2 show ?thesis
        unfolding ufa_lca_def awalk_verts_from_rep_union_eq awalk_verts_from_rep_x
        by auto
    qed
  qed
qed

end

subsection \<open>Correctness of \<open>find_newest_on_walk\<close>.\<close>

context union_find_explain_adts
begin

lemma find_newest_on_walk_dom_parent_of:
  assumes "find_newest_on_walk_dom ufe_ds (y, x)" "x \<noteq> y"
  shows "find_newest_on_walk_dom ufe_ds (y, ufe_parent_of ufe_ds x)"
  using assms find_newest_on_walk.domintros
  by (induction rule: find_newest_on_walk.pinduct) blast

lemma find_newest_on_walk_eq_if_eq[simp]:
  assumes "y = x"
  shows "find_newest_on_walk ufe_ds y x = None"
  using assms
  by (metis find_newest_on_walk.domintros find_newest_on_walk.pelims)

end

context ufe_tree
begin

lemma find_newest_on_walk_dom:
  assumes "awalk y p z"
  shows "find_newest_on_walk_dom ufe_ds (y, z)"
proof -
  from assms have "z \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
    by blast
  from wf_parent_of_rel assms show ?thesis
  proof(induction arbitrary: p rule: wf_induct_rule)
    case (less x)
    then show ?case
    proof(cases "p = []")
      case True
      with less show ?thesis
        using awalk_ends find_newest_on_walk.domintros by metis
    next
      case False
      with less have
        "(ufe_parent_of ufe_ds x, x) \<in> uf_parent_of_rel (uf_ds ufe_ds)"
        unfolding uf_parent_of_rel_def
        using awalk_and_parent_of_reflD(2) in_Field_\<alpha>_if_in_verts by auto
      from False less.IH[OF this] less.prems have
        "find_newest_on_walk_dom ufe_ds (y, ufe_parent_of ufe_ds x)"
        using awalk_not_Nil_butlastD(1) awlast_butlast_eq_parent_of_if_awalk by auto
      then show ?thesis
        using find_newest_on_walk.domintros by blast
    qed
  qed
qed

lemma find_newest_on_walk_eq_Max_au_of:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "find_newest_on_walk ufe_ds y z = Some (Max (au_of ` set p))"
proof -
  from find_newest_on_walk_dom[OF assms(1)] assms show ?thesis
  proof(induction arbitrary: p rule: find_newest_on_walk.pinduct)
    case (1 y z)
    then have "z \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
      using in_Field_\<alpha>_if_in_verts awalk_last_in_verts by blast
    with "1.prems" obtain au_z where au_z:
      "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) z = Some au_z"
      using lookup_au_ds_eq_None_iff refl_parent_of_iff_refl_rep_of
      by (metis awalk_and_parent_of_reflD(1) not_None_eq)
    then show ?case
    proof(cases "y = ufe_parent_of ufe_ds z")
      case True
      with "1.prems" have p_eq: "p = [(ufe_parent_of ufe_ds z, z)]" (is "_ = [?a]")
        using awalk_parent_of unique_awalk_All by blast
      with "1.prems" au_z show ?thesis
        unfolding au_of_def find_newest_on_walk.psimps[OF "1.hyps"]
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

      from \<open>z \<in> Field (uf_\<alpha> (uf_ds ufe_ds))\<close> have
        "ufe_parent_of ufe_ds z \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
        by blast
      with False obtain au_p_z where au_p_z:
        "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) (ufe_parent_of ufe_ds z) =
        Some au_p_z"
        using lookup_au_ds_eq_None_iff refl_parent_of_iff_refl_rep_of
        by (metis awalk_and_parent_of_reflD(1) awalk_butlast domD domIff)
      
      from \<open>y \<noteq> z\<close> au_z au_p_z have
        "find_newest_on_walk ufe_ds y z =
        combine_options max (Some au_z) (find_newest_on_walk ufe_ds y (ufe_parent_of ufe_ds z))"
      proof -
        have "find_newest_on_walk_dom ufe_ds (y, ufe_parent_of ufe_ds z)"
          using awalk_butlast find_newest_on_walk_dom by blast
        with False au_p_z have
          "find_newest_on_walk ufe_ds y (ufe_parent_of ufe_ds z) \<noteq> None"
          by (auto simp: find_newest_on_walk.psimps combine_options_def split: option.splits)
        with "1.prems" au_z show ?thesis 
          unfolding find_newest_on_walk.psimps[OF "1.hyps"(1)] by fastforce
      qed
      also have "\<dots> = Some (max au_z (Max (au_of ` set (butlast p))))"
      proof -
        note "1.IH"[OF \<open>y \<noteq> z\<close> \<open>awalk y (butlast p) (ufe_parent_of ufe_ds z)\<close>
            \<open>y \<noteq> ufe_parent_of ufe_ds z\<close>]
        then show ?thesis
          unfolding newest_on_walk_def by simp
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

lemma find_newest_on_walk_eq_None_iff:
  assumes "awalk y p z"
  shows "find_newest_on_walk ufe_ds y z = None \<longleftrightarrow> y = z"
  using find_newest_on_walk_dom[OF assms] assms
proof(induction rule: find_newest_on_walk.pinduct)
  case (1 y z)
  then show ?case
    using find_newest_on_walk_eq_Max_au_of by (cases "y = z") simp_all
qed
  
theorem newest_on_walk_find_newest_on_walk:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "newest_on_walk (the (find_newest_on_walk ufe_ds y z)) y p z"
  using find_newest_on_walk_eq_Max_au_of[OF assms] \<open>awalk y p z\<close>
  unfolding newest_on_walk_def
  by simp


end

lemma (in ufe_tree) find_newest_on_walk_lt_Some_length_unions:
  assumes "awalk y p z"
  shows "find_newest_on_walk ufe_ds y z < Some (length (unions ufe_ds))"
proof(cases "y = z")
  case True
  then show ?thesis by simp
next
  case False
  with assms have "newest_on_walk (the (find_newest_on_walk ufe_ds y z)) y p z"
    using newest_on_walk_find_newest_on_walk by blast
  with False newest_on_walk_lt_length_unions show ?thesis
    by (cases "find_newest_on_walk ufe_ds y z") auto
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

lemma (in union_find_explain_ds) find_newest_on_walk_ufe_union:
  assumes "a \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds a \<noteq> ufe_rep_of ufe_ds b" (is "?rep_a \<noteq> ?rep_b")
  assumes awalk_pxy: "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z) x pxy y"
  shows "find_newest_on_walk (ufe_union ufe_ds a b) x y = 
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y then find_newest_on_walk ufe_ds x y
    else Some (length (unions ufe_ds)))"
proof -
  from assms ufe_explain_ds_union interpret ufe_ds_union: union_find_explain_ds
    where ufe_ds = "ufe_union ufe_ds a b" 
    by blast
  from assms have "z \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
    unfolding pre_digraph.awalk_def
    apply(safe intro!: ufe_ds_union.in_vertsI dest!: ufe_ds_union.in_verts_ufa_tree_ofD)
    by (metis ufe_ds_union.\<alpha>_rep_of Field_iff)

  with assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and x = z
    by unfold_locales blast

  from assms awalk_pxy have
    "x \<in> Field (uf_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    "y \<in> Field (uf_\<alpha> (uf_ds (ufe_union ufe_ds a b)))"
    using ufe_ds_union.in_Field_\<alpha>_if_in_verts
    by blast+
  then have
    x_in_Field_\<alpha>: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
    y_in_Field_\<alpha>: "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    by auto

  from x_in_Field_\<alpha> interpret ufe_tree_x: ufe_tree where ufe_ds = ufe_ds and x = x
    by unfold_locales
  from y_in_Field_\<alpha> interpret ufe_tree_y: ufe_tree where ufe_ds = ufe_ds and x = y
    by unfold_locales
  interpret ufe_tree_z: ufe_tree where ufe_ds = ufe_ds and x = z
    using ufe_tree_union.x_in_Field_\<alpha> by unfold_locales fastforce

  have ?thesis if "x \<noteq> y" "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  proof -
    from awalk_pxy have "x \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
      by blast
    note ufe_ds_union.ufa_tree_of_eq_if_in_verts[OF this]
    with that awalk_pxy have "ufe_tree_x.awalk x pxy y"
      using ufe_union_sel_if_rep_of_neq(1)[OF assms(3)]
      by (intro ufe_tree_x.awalk_if_union_awalk[OF assms(1,2)]) simp_all
    with that have "find_newest_on_walk ufe_ds x y = Some (Max (ufe_tree_x.au_of ` set pxy))"
      using ufe_tree_x.find_newest_on_walk_eq_Max_au_of by blast
    moreover from that awalk_pxy have
      "find_newest_on_walk (ufe_union ufe_ds a b) x y =
      Some (Max (ufe_tree_union.au_of ` set pxy))"
      using ufe_tree_union.find_newest_on_walk_eq_Max_au_of by blast
    moreover have "ufe_tree_x.au_of e = ufe_tree_union.au_of e" if "e \<in> set pxy" for e
    proof -
      note mm_relI[OF mm_invar_au_ds, transfer_rule]
      from assms have "ufe_rep_of ufe_ds a \<notin> dom (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds))"
        unfolding domIff
        by (meson lookup_au_ds_eq_None_iff rep_of_in_Field_\<alpha>_if_in_Field_\<alpha> rep_of_rep_of)
      moreover note ufe_tree_x.head_in_dom_lookup_if_in_arcs
      with that have "head (ufa_tree_of (uf_ds ufe_ds) x) e \<in> dom (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds))"
        using \<open>ufe_tree_x.awalk x pxy y\<close> by blast
      ultimately show ?thesis
        unfolding ufe_tree_x.au_of_def ufe_tree_union.au_of_def au_ds_ufe_union
        by (transfer fixing: ufe_ds a b x z uf_adt e) (use that in \<open>auto split: if_splits\<close>)
    qed
    ultimately show ?thesis
      using that by simp
  qed
  moreover have ?thesis if "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  proof -
    from assms have
      rep_a_in_Field_\<alpha>: "?rep_a \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
      rep_b_in_Field_\<alpha>: "?rep_b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
      by blast+
    note this[THEN ufe_tree_x.awalk_from_rep_union[OF assms(1-3)]]
    moreover from assms(1) have "awalk_from_rep (uf_ds ufe_ds) (ufe_rep_of ufe_ds a) = []"
      using awalk_from_rep_rep_of by blast
    ultimately have awalk_from_rep_rep_a:
      "awalk_from_rep (uf_ds (ufe_union ufe_ds a b)) ?rep_a = [(?rep_b, ?rep_a)]"
      using rep_of_rep_of assms(1,3) by simp
    
    from awalk_pxy have rep_of_union_eq:
      "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) z"
      "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y"
      by auto
    note rep_of_union_eq_assms[unfolded ufe_union_sel_if_rep_of_neq[OF assms(3)]] = 
      x_in_Field_\<alpha> y_in_Field_\<alpha> this(2) assms(1-3)
    from rep_of_union_eq_assms show ?thesis
    proof(cases rule: rep_of_union_eq_cases)
      case 2
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
        using ufe_ds_union.ufa_tree_of_eq_if_in_verts
        by (metis awalk_pxy ufe_tree_union.awalkE')
      moreover
      from 2 have
        "ufe_tree_y.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
        using ufe_tree_y.awalk_awalk_from_rep by fastforce
      note ufe_tree_y.union_awalk_if_awalk[OF _ _this]
      with assms have
        "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) y)
          ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
        by fastforce
      then have union_awalk_awalk_from_rep_y:
        "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
        using ufe_ds_union.ufa_tree_of_eq_if_in_verts
        by (metis awalk_pxy ufe_tree_union.awalkE')
      moreover
      from 2 awalk_from_rep_rep_a have "ufe_tree_union.awalk ?rep_b [(?rep_b, ?rep_a)] ?rep_a"
      proof -
        from calculation have "?rep_a \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
          by blast
        note ufe_tree_union.awalk_awalk_from_rep[OF this]
        with awalk_from_rep_rep_a show ?thesis
          using assms(1-3) rep_a_in_Field_\<alpha> rep_of_union by fastforce
      qed
      ultimately have
        "ufe_tree_union.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
        using awalk_pxy by (simp add: ufe_tree_union.awalk_Cons_iff)
      then have
        "ufe_tree_y.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
        using 2 union_awalk_awalk_from_rep_y ufe_tree_union.unique_awalk_All
        by (metis ufe_tree_y.awalk_awalk_from_rep ufe_tree_y.x_in_verts)
      with 2 have "ufe_tree_y.awalk x pxy y"
        using ufe_tree_x.awlast_awalk_from_rep[OF ufe_tree_x.x_in_verts]
        by (simp add: ufe_tree_y.awalk_Cons_iff awalk_verts_with_proj_eq)
      with that show ?thesis
        by auto
    next
      case 3
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
        using ufe_ds_union.ufa_tree_of_eq_if_in_verts
        by (metis awalk_pxy ufe_tree_union.awalkE')
      moreover
      from 3 have y_awalk_awalk_from_rep_y:
        "ufe_tree_y.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
        using ufe_tree_y.awalk_awalk_from_rep by fastforce
      note ufe_tree_y.union_awalk_if_awalk[OF _ _this]
      with assms have
        "pre_digraph.awalk (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) y)
          ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
        by fastforce
      then have union_awalk_awalk_from_rep_y:
        "ufe_tree_union.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
        using ufe_ds_union.ufa_tree_of_eq_if_in_verts
        by (metis awalk_pxy ufe_tree_union.awalkE')
      moreover
      from 3 awalk_from_rep_rep_a have "ufe_tree_union.awalk ?rep_b [(?rep_b, ?rep_a)] ?rep_a"
      proof -
        from calculation have "?rep_a \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) z)"
          by blast
        note ufe_tree_union.awalk_awalk_from_rep[OF this]
        with awalk_from_rep_rep_a show ?thesis
          using assms(1-3) rep_a_in_Field_\<alpha> rep_of_union by fastforce
      qed
      ultimately have union_awalk_rep_b_y:
        "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
        "ufe_tree_union.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) y) y"
        using awalk_pxy
        by (simp_all add: ufe_tree_union.awalk_Cons_iff)
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
        with that show False
          by blast
      qed
      then have "?rep_b = x"
        using x_awalk_awalk_from_rep_x by auto
      with awalk_pxy union_awalk_rep_b_y have "(?rep_b, ?rep_a) \<in> set pxy"
        using ufe_tree_union.unique_awalk_All
        by (metis list.set_intros(1))
      moreover have "ufe_tree_union.au_of (?rep_b, ?rep_a) = length (unions ufe_ds)"
        using assms(3) unfolding ufe_tree_union.au_of_def
        by (simp add: \<alpha>_lookup \<alpha>_update mm_invar_au_ds)
      moreover have "ufe_tree_union.au_of e < length (unions (ufe_union ufe_ds a b))"
        if "e \<in> set pxy" for e
        using that awalk_pxy ufe_tree_union.au_of_lt_length_unions
        by (meson subsetD ufe_tree_union.awalkE')
      then have "ufe_tree_union.au_of e \<le> length (unions ufe_ds)"
        if "e \<in> set pxy" for e
        using that assms(3) by (simp add: less_Suc_eq order_le_less)
      ultimately have "Max (ufe_tree_union.au_of ` set pxy) = length (unions ufe_ds)"
        by (intro Max_eqI) (auto simp: rev_image_eqI)
      moreover note ufe_tree_union.find_newest_on_walk_eq_Max_au_of[OF awalk_pxy]
      ultimately show ?thesis
        using that by auto
    qed (use that in blast)
  qed
  ultimately show ?thesis
    by (cases "x = y") simp_all
qed

end