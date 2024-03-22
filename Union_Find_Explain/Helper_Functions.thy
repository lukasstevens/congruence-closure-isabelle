section \<open>Correctness proofs for the helper functions\<close>
theory Helper_Functions
  imports Explain_Definition UFE_Tree 
begin 

subsection \<open>Proofs about the domain of the helper functions\<close>

theorem (in ufa_tree) lca_ufa_lca:    
  assumes "y \<in> verts (ufa_tree_of uf x)"
    shows "lca (ufa_lca uf x y) x y"
proof -
  from assms have "uf_rep_of uf x = uf_rep_of uf y"
    by simp
  note awalk_awalk_from_rep[OF x_in_verts]
   and awalk_awalk_from_rep[OF assms, folded this]
  note lca_last_longest_common_prefix_awalk_verts[OF this]
  with \<open>uf_rep_of uf x = uf_rep_of uf y\<close> show ?thesis
    unfolding ufa_lca_def
    unfolding awalk_verts_from_rep_eq_awalk_verts[OF x_in_verts]
    unfolding awalk_verts_from_rep_eq_awalk_verts[OF assms]
    by simp
qed

context ufa_tree
begin

lemma
  assumes "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of uf a \<noteq> uf_rep_of uf b"
  assumes "y \<in> verts (ufa_tree_of (uf_union uf a b) x)"
  shows "ufa_lca (uf_union uf a b) x y =
    (if uf_rep_of uf x \<noteq> uf_rep_of uf y then b else ufa_lca uf x y)"
proof -
  interpret ufp_unions_union: union_find_parent_unions where
    uf = "uf_union uf a b" and us = "us @ [(a, b)]"
    using assms union_find_parent_unions_union by blast
  from assms have "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
    using Field_\<alpha>_union ufp_unions_union.in_Field_\<alpha>_if_in_verts by auto

  note awalk_verts_from_rep_union = this[THEN awalk_verts_from_rep_union[OF assms(1-3)]]
  
  show ?thesis
  proof(cases "uf_rep_of uf x = uf_rep_of uf y")
    case True
    with \<open>x \<in> Field (uf_\<alpha> uf)\<close> \<open>y \<in> Field (uf_\<alpha> uf)\<close>
    have "x \<in> verts (ufa_tree_of uf x)" "y \<in> verts (ufa_tree_of uf x)"
      using \<alpha>_rep_of in_vertsI by blast+
    from True this[THEN hd_awalk_verts_from_rep] this[THEN awalk_verts_from_rep_neq_Nil]
    obtain px py where
      "awalk_verts_from_rep uf x = uf_rep_of uf y # px"
      "awalk_verts_from_rep uf y = uf_rep_of uf y # py"
       by (metis list.exhaust_sel)
    then have
      "longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y) \<noteq> []"
      by simp
  
    with True show ?thesis
      unfolding ufa_lca_def awalk_verts_from_rep_union
      by auto
  next
    case False
    then show ?thesis
      unfolding ufa_lca_def awalk_verts_from_rep_union
      apply auto
      sorry
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

end