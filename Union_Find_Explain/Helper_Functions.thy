section \<open>Correctness proofs for the helper functions\<close>
theory Helper_Functions
  imports Explain_Definition 
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

subsection \<open>Correctness of \<open>find_newest_on_walk\<close>.\<close>

lemma (in ufe_tree) find_newest_on_walk_dom_idx:
  assumes "find_newest_on_walk_dom uf (y, x)" "x \<noteq> y"
  shows "find_newest_on_walk_dom uf (y, uf_parent_of uf x)"
  using assms find_newest_on_walk.domintros
  by (induction rule: find_newest_on_walk.pinduct) blast

lemma (in ufe_tree) find_newest_on_walk_eq_if_eq[simp]:
  assumes "y = x"
  shows "find_newest_on_walk uf au y x = None"
  using assms
  by (metis find_newest_on_walk.domintros find_newest_on_walk.pelims)

lemma (in ufe_tree) find_newest_on_walk_domain:
  assumes "awalk y p z"
  shows "find_newest_on_walk_dom uf (y, z)"
proof -
  from assms have "z \<in> verts (ufa_tree_of uf x)"
    by blast
  from wf_parent_of assms show ?thesis
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
        "(uf_parent_of uf x, x) \<in> {(uf_parent_of uf x, x) |x. x \<in> Field (uf_\<alpha> uf)}"
        by auto
      from False less.IH[OF this] less.prems have
        "find_newest_on_walk_dom uf (y, uf_parent_of uf x)"
        using awalk_not_Nil_butlastD(1) awlast_butlast_eq_parent_of_if_awalk by auto
      then show ?thesis
        using find_newest_on_walk.domintros by blast
    qed
  qed
qed

theorem (in ufe_tree) newest_on_walk_find_newest_on_walk:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "newest_on_walk (the (find_newest_on_walk uf au y z)) y p z"
proof -
  from assms have "uf_parent_of uf z \<noteq> z"
    using awalk_and_parent_of_reflD(1) by blast
  with assms obtain au_z where "mm_lookup\<^bsub>au_adt\<^esub> au z = Some au_z"
    using awalk_last_in_verts lookup_au_if_not_rep parent_of_refl_iff_rep_of_refl
    by blast
  note find_newest_on_walk_domain[OF assms(1)]
  then show ?thesis 
    using assms \<open>mm_lookup\<^bsub>au_adt\<^esub> au z = Some au_z\<close>
  proof(induction arbitrary: p au_z rule: find_newest_on_walk.pinduct)
    case (1 y z)
    then show ?case
    proof(cases "y = uf_parent_of uf z")
      case True
      with 1 have p_eq: "p = [(uf_parent_of uf z, z)]"
        using awalk_parent_of unique_awalk_All by blast
      with "1.prems" have "find_newest_on_walk uf au y z = Some au_z"
        using find_newest_on_walk.psimps[OF "1.hyps"]
        by auto     
      with 1 p_eq show ?thesis
        unfolding newest_on_walk_def
        by simp
    next
      case False
      from 1 have "p \<noteq> []"
        by auto
      with 1 have
        awalk_butlast: "awalk y (butlast p) (uf_parent_of uf z)" and
        awalk_last: "awalk (uf_parent_of uf z) [last p] z"
        using awalk_not_Nil_butlastD
        by (metis awlast_butlast_eq_parent_of_if_awalk)+
      with awalk_verts_append[where ?p="butlast p" and ?q="[last p]"]
      have awalk_verts_p:
        "awalk_verts y p = awalk_verts y (butlast p) @ [z]"
        using \<open>awalk y p z\<close> \<open>p \<noteq> []\<close> by auto
      moreover
      note "1.IH"[OF \<open>y \<noteq> z\<close> \<open>awalk y (butlast p) (uf_parent_of uf z)\<close> \<open>y \<noteq> uf_parent_of uf z\<close>]
      moreover from \<open>p \<noteq> []\<close> have "p = butlast p @ [last p]"
        by simp
      moreover
      let ?vs = "tl (awalk_verts y (butlast p))"
      have "Max (insert au_z (Option.these (mm_lookup\<^bsub>au_adt\<^esub> au ` set ?vs)))
        = max au_z (Max (Option.these (mm_lookup\<^bsub>au_adt\<^esub> au ` set ?vs)))"
      proof(rule Max.insert_not_elem)
        from False obtain au_parent_z where
          "mm_lookup\<^bsub>au_adt\<^esub> au (uf_parent_of uf z) = Some au_parent_z"
          using lookup_au_if_not_rep parent_of_refl_iff_rep_of_refl
          using awalk_butlast awalk_and_parent_of_reflD(1) by blast
        moreover from False have "uf_parent_of uf z \<in> set ?vs"
          using awalk_butlast
          by (simp add: last_in_awalk_verts(1) not_hd_in_tl)
        ultimately show "Option.these (mm_lookup\<^bsub>au_adt\<^esub> au ` set ?vs) \<noteq> {}"
          unfolding Option.these_def by auto

        from \<open>awalk y p z\<close> awalk_butlast awalk_verts_p
        have "z \<notin> set (awalk_verts y (butlast p))"
          by (metis distinct_awalk_verts not_distinct_conv_prefix)
        then have "z \<notin> set ?vs"
          by (meson in_set_tlD)
        with "1" show "au_z \<notin> Option.these (mm_lookup\<^bsub>au_adt\<^esub> au ` set ?vs)"
          using inj_on_dom_au unfolding Option.these_def
          by auto (metis domI inj_onD)
      qed (simp add: Option.these_def)
      ultimately show ?thesis
        unfolding newest_on_walk_def
        unfolding awalk_verts_p
        using "1.prems" "1.hyps" \<open>mm_lookup\<^bsub>au_adt\<^esub> au z = Some au_z\<close>
        apply (auto simp add: find_newest_on_walk.psimps)
        thm False
      qed
  qed
qed

end