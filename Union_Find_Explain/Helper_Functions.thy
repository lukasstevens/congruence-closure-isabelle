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

context ufe_tree
begin

lemma find_newest_on_walk_dom_parent_of:
  assumes "find_newest_on_walk_dom uf (y, x)" "x \<noteq> y"
  shows "find_newest_on_walk_dom uf (y, uf_parent_of uf x)"
  using assms find_newest_on_walk.domintros
  by (induction rule: find_newest_on_walk.pinduct) blast

lemma find_newest_on_walk_eq_if_eq[simp]:
  assumes "y = x"
  shows "find_newest_on_walk uf au y x = None"
  using assms
  by (metis find_newest_on_walk.domintros find_newest_on_walk.pelims)

lemma find_newest_on_walk_dom:
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

lemma find_newest_on_walk_eq_Max_au_of:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "find_newest_on_walk uf au y z = Some (Max (au_of ` set p))"
proof -
  from find_newest_on_walk_dom[OF assms(1)] assms show ?thesis
  proof(induction arbitrary: p rule: find_newest_on_walk.pinduct)
    case (1 y z)
    then have "z \<in> Field (uf_\<alpha> uf)"
      using in_Field_\<alpha>_if_in_verts awalk_last_in_verts by blast
    with "1.prems" obtain au_z where au_z: "mm_lookup\<^bsub>au_adt\<^esub> au z = Some au_z"
      using lookup_au_if_not_rep parent_of_refl_iff_rep_of_refl
      by (metis awalk_Nil_iff awalk_and_parent_of_reflD(2) option.exhaust)
    then show ?case
    proof(cases "y = uf_parent_of uf z")
      case True
      with "1.prems" have p_eq: "p = [(uf_parent_of uf z, z)]" (is "_ = [?a]")
        using awalk_parent_of unique_awalk_All by blast
      with "1.prems" au_z show ?thesis
        unfolding au_of_def find_newest_on_walk.psimps[OF "1.hyps"]
        by (auto simp: combine_options_def split: option.splits)
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

      from \<open>z \<in> Field (uf_\<alpha> uf)\<close> have "uf_parent_of uf z \<in> Field (uf_\<alpha> uf)"
        by blast
      with False obtain au_p_z where au_p_z:
        "mm_lookup\<^bsub>au_adt\<^esub> au (uf_parent_of uf z) = Some au_p_z"
        using lookup_au_if_not_rep parent_of_refl_iff_rep_of_refl
        by (metis awalk_and_parent_of_reflD(1) awalk_butlast domD domIff)
      
      from \<open>y \<noteq> z\<close> au_z au_p_z have "find_newest_on_walk uf au y z
        = combine_options max (Some au_z) (find_newest_on_walk uf au y (uf_parent_of uf z))"
      proof -
        have "find_newest_on_walk_dom uf (y, uf_parent_of uf z)"
          using awalk_butlast find_newest_on_walk_dom by blast
        with False au_p_z have "find_newest_on_walk uf au y (uf_parent_of uf z) \<noteq> None"
          by (auto simp: find_newest_on_walk.psimps combine_options_def split: option.splits)
        with "1.prems" au_z show ?thesis 
          unfolding find_newest_on_walk.psimps[OF "1.hyps"(1)] by fastforce
      qed
      also have "\<dots> = Some (max au_z (Max (au_of ` set (butlast p))))"
      proof -
        note "1.IH"[OF \<open>y \<noteq> z\<close> \<open>awalk y (butlast p) (uf_parent_of uf z)\<close> \<open>y \<noteq> uf_parent_of uf z\<close>]
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
  shows "find_newest_on_walk uf au y z = None \<longleftrightarrow> y = z"
  using find_newest_on_walk_dom[OF assms] assms
proof(induction rule: find_newest_on_walk.pinduct)
  case (1 y z)
  then show ?case
    using find_newest_on_walk_eq_Max_au_of by (cases "y = z") simp_all
qed
  
theorem newest_on_walk_find_newest_on_walk:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "newest_on_walk (the (find_newest_on_walk uf au y z)) y p z"
  using find_newest_on_walk_eq_Max_au_of[OF assms] \<open>awalk y p z\<close>
  unfolding newest_on_walk_def
  by simp

end

end