section \<open>Correctness proofs for the helper functions\<close>
theory Helper_Functions
  imports Path 
begin 

subsection \<open>Proofs about the domain of the helper functions\<close>

theorem (in ufa_tree) lca_ufa_lca:    
  assumes "y \<in> verts (ufa_tree_of l x)"
    shows "lca (ufa_lca l x y) x y"
proof -
  from assms have "rep_of l x = rep_of l y"
    using in_verts_ufa_tree_ofD(2) by simp
  note awalk_awalk_from_rep[OF x_in_verts]
   and awalk_awalk_from_rep[OF assms, folded this]
  note lca_last_longest_common_prefix_awalk_verts[OF this]
  with \<open>rep_of l x = rep_of l y\<close> show ?thesis
    unfolding ufa_lca_def
    unfolding awalk_verts_from_rep_eq_awalk_verts[OF x_in_verts]
    unfolding awalk_verts_from_rep_eq_awalk_verts[OF assms]
    by simp
qed

subsection \<open>Correctness of \<open>find_newest_on_walk\<close>.\<close>

lemma find_newest_on_walk_dom_idx:
  assumes "find_newest_on_walk_dom l (y, x)" "x \<noteq> y"
  shows "find_newest_on_walk_dom l (y, l ! x)"
  using assms find_newest_on_walk.domintros
  by (induction rule: find_newest_on_walk.pinduct) blast

lemma find_newest_on_walk_eq_if_eq[simp]:
  assumes "y = x"
  shows "find_newest_on_walk l au' y x = -1"
  using assms
  by (metis find_newest_on_walk.domintros find_newest_on_walk.pelims)

lemma (in ufa_tree) find_newest_on_walk_domain:
  assumes "awalk y p z"
  shows "find_newest_on_walk_dom l (y, z)"
proof -
  from assms have "z \<in> verts (ufa_tree_of l x)"
    by blast
  from in_verts_ufa_tree_ofD(1)[OF this(1)] assms show ?thesis
  proof(induction arbitrary: p rule: rep_of_induct)
    case (base i)
    then show ?case
      using find_newest_on_walk.domintros awalk_idx_sameD by blast
  next
    case (step i)
    then show ?case
    proof(cases "i = y")
      case True
      then show ?thesis 
        using find_newest_on_walk.domintros by blast
    next
      case False
      with step have "p \<noteq> []"
        using awalk_ends by blast
      note awalk_not_Nil_butlastD[OF _ this]
       and awlast_butlast_eq_idx_if_awalk[OF _ this]
      with step have "awalk y (butlast p) (l ! i)"
        by metis+
      with step have "find_newest_on_walk_dom l (y, l ! i)"
        by blast
      then show ?thesis       
        using find_newest_on_walk.domintros by blast
    qed
  qed
qed

theorem (in ufe_tree) newest_on_walk_find_newest_on_walk:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "newest_on_walk (find_newest_on_walk l au y z) y p z"
proof -
  from assms have "l ! z \<noteq> z"
    using awalk_idx_sameD(1) by blast
  note find_newest_on_walk_domain[OF assms(1)]
  then show ?thesis 
    using assms
  proof(induction arbitrary: p rule: find_newest_on_walk.pinduct)
    case (1 y z)
    with nth_au_nonneg_if_not_rep have "au ! z \<ge> 0"
      by (metis awalk_idx_sameD(1) awalk_last_in_verts in_verts_ufa_tree_ofD(1))
    then show ?case
    proof(cases "y = l ! z")
      case True
      with 1 have "p = [(l ! z, z)]"
        by (metis awalkE' awalk_idx unique_awalk_All)
      with 1 \<open>au ! z \<ge> 0\<close> show ?thesis
        unfolding newest_on_walk_def
        using find_newest_on_walk.psimps[where ?x=z]
        using find_newest_on_walk.psimps[where ?x="l ! z"]
        by (auto simp: find_newest_on_walk_dom_idx)
    next
      case False
      with 1 have "p \<noteq> []"
        by auto
      with 1 have
        awalk_butlast: "awalk y (butlast p) (l ! z)" and
        awalk_last: "awalk (l ! z) [last p] z"
        using awalk_not_Nil_butlastD awlast_butlast_eq_idx_if_awalk
        by auto
      with awalk_verts_append[where ?p="butlast p" and ?q="[last p]"]
      have awalk_verts_p:
        "awalk_verts y p = awalk_verts y (butlast p) @ [z]"
        using \<open>awalk y p z\<close> \<open>p \<noteq> []\<close> by auto
      moreover
      note "1.IH"[OF \<open>y \<noteq> z\<close> \<open>awalk y (butlast p) (l ! z)\<close> \<open>y \<noteq> l ! z\<close>]
      moreover from \<open>p \<noteq> []\<close> have "p = butlast p @ [last p]"
        by simp
      moreover
      have "Max (insert (au ! z) ((!) au ` set (tl (awalk_verts y (butlast p)))))
        = max (au ! z) (Max ((!) au ` set (tl (awalk_verts y (butlast p)))))"
      proof(rule Max.insert_not_elem)
        from False awalk_butlast
        show "(!) au ` set (tl (awalk_verts y (butlast p))) \<noteq> {}"
          by (cases p) auto

        from \<open>awalk y p z\<close> awalk_butlast awalk_verts_p
        have "z \<notin> set (awalk_verts y (butlast p))"
          by (metis distinct_awalk_verts not_distinct_conv_prefix)
        then have "z \<notin> set (tl (awalk_verts y (butlast p)))"
          by (meson in_set_tlD)
        moreover from \<open>awalk y p z\<close> have "z < length au"
          using length_au
          by (metis awalk_last_in_verts in_verts_ufa_tree_ofD(1))
        moreover from awalk_butlast have
          "\<forall>x \<in> set (tl (awalk_verts y (butlast p))). x < length au"
          using length_au
          by (metis awalkE' awalk_verts_in_verts in_set_tlD in_verts_ufa_tree_ofD(1))
        ultimately show "au ! z \<notin> (!) au ` set (tl (awalk_verts y (butlast p)))"
          using distinct_au[unfolded distinct_conv_nth]
          by auto
      qed simp

      ultimately show ?thesis
        using "1.prems" "1.hyps"
        unfolding newest_on_walk_def
        using find_newest_on_walk.psimps[where ?x=z]
        by auto
    qed
  qed
qed

end