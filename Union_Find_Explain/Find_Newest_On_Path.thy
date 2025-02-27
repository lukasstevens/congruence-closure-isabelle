theory Find_Newest_On_Path
  imports UFE_Forest
begin

lemma find_newest_on_path_dom_parent_of:
  assumes "find_newest_on_path_dom ufe (y, x)" "x \<noteq> y"
  shows "find_newest_on_path_dom ufe (y, ufe_parent_of ufe x)"
  using assms find_newest_on_path.domintros
  by (induction rule: find_newest_on_path.pinduct) blast

lemma find_newest_on_path_eq_if_eq[simp]:
  assumes "y = x"
  shows "find_newest_on_path ufe y x = None"
  using assms
  by (metis find_newest_on_path.domintros find_newest_on_path.pelims)

context ufe_forest
begin

lemma find_newest_on_path_dom:
  assumes "awalk x p y"
  shows "find_newest_on_path_dom ufe (x, y)"
proof -
  from assms have "y \<in> verts (ufe_forest_of ufe)"
    by blast
  then have "y \<in> Field (ufe_\<alpha> ufe)"
    by blast
  show ?thesis
  proof(cases "p = []")
    case True
    then show ?thesis
      using assms awalk_empty_ends find_newest_on_path.domintros by blast
  next
    case False
    with \<open>y \<in> Field (ufe_\<alpha> ufe)\<close> assms show ?thesis
    proof(induction arbitrary: p rule: ufa_rep_of_induct)
      case (rep i)
      then show ?case
        by (meson awalk_and_ufa_rep_of_reflD(2) ufa_rep_of_simp)
    next
      case (not_rep i)
      then have "awalk x (butlast p) (ufe_parent_of ufe i)"
        using awalk_not_Nil_butlastD(1) awalk_Nil_iff
        by (simp add: awlast_butlast_eq_ufa_parent_of_if_awalk)
      with not_rep have
        "find_newest_on_path_dom ufe (x, ufe_parent_of ufe i)"
        by (metis awalk_empty_ends find_newest_on_path.domintros)
      then show ?case
        using find_newest_on_path.domintros by blast
    qed
  qed
qed

lemma find_newest_on_path_eq_Max_au_of:
  assumes "awalk x p y"
      and "x \<noteq> y"
    shows "find_newest_on_path ufe x y = Some (Max (au_of ` set p))"
proof -
  from find_newest_on_path_dom[OF assms(1)] assms show ?thesis
  proof(induction arbitrary: p rule: find_newest_on_path.pinduct)
    case (1 x y)
    then have "y \<in> Field (ufe_\<alpha> ufe)"
      using awalk_last_in_verts by blast
    with "1.prems" obtain au_y where au_y:
      "au_ds ufe y = Some au_y"
      using lookup_au_ds_eq_None_iff ufa_parent_of_ufa_rep_of
      by (metis awalk_and_ufa_rep_of_reflD(1) not_None_eq)
    then show ?case
    proof(cases "x = ufe_parent_of ufe y")
      case True
      with "1.prems" have p_eq: "p = [(ufe_parent_of ufe y, y)]" (is "_ = [?a]")
        using awalk_ufa_parent_of unique_awalk by blast
      with "1.prems" au_y show ?thesis
        unfolding au_of_def find_newest_on_path.psimps[OF "1.hyps"]
        by (auto split: option.splits)
    next
      case False 
      from 1 have "p \<noteq> []"
        by auto
      with 1 have
        awalk_butlast: "awalk x (butlast p) (ufe_parent_of ufe y)" and
        awalk_last: "awalk (ufe_parent_of ufe y) [last p] y"
        using awalk_not_Nil_butlastD
        by (metis awlast_butlast_eq_ufa_parent_of_if_awalk)+
      with awalk_verts_append[where ?p="butlast p" and ?q="[last p]"]
      have awalk_verts_p:
        "awalk_verts x p = awalk_verts x (butlast p) @ [y]"
        using \<open>awalk x p y\<close> \<open>p \<noteq> []\<close> by auto

      from \<open>y \<in> Field (ufe_\<alpha> ufe)\<close> have
        "ufe_parent_of ufe y \<in> Field (ufe_\<alpha> ufe)"
        by blast
      with False obtain au_p_y where au_p_y:
        "au_ds ufe (ufe_parent_of ufe y) = Some au_p_y"
        using lookup_au_ds_eq_None_iff ufa_parent_of_ufa_rep_of
        by (metis awalk_and_ufa_rep_of_reflD(1) awalk_butlast domD domIff)
      
      from \<open>x \<noteq> y\<close> au_y au_p_y have
        "find_newest_on_path ufe x y =
          max (Some au_y) (find_newest_on_path ufe x (ufe_parent_of ufe y))"
      proof -
        have "find_newest_on_path_dom ufe (x, ufe_parent_of ufe y)"
          using awalk_butlast find_newest_on_path_dom by blast
        with False au_p_y have
          "find_newest_on_path ufe x (ufe_parent_of ufe y) \<noteq> None"
          using domIff
          by (fastforce simp: find_newest_on_path.psimps max_def split: option.splits)
        with "1.prems" au_y show ?thesis 
          unfolding find_newest_on_path.psimps[OF "1.hyps"(1)]
          by (auto simp: max_def)
      qed
      also have "\<dots> = Some (max au_y (Max (au_of ` set (butlast p))))"
      proof -
        note "1.IH"[OF \<open>x \<noteq> y\<close> \<open>awalk x (butlast p) (ufe_parent_of ufe y)\<close>
            \<open>x \<noteq> ufe_parent_of ufe y\<close>]
        then show ?thesis
          unfolding newest_on_path_def max_def by simp
      qed
      also have "\<dots> = Some (Max (au_of ` set p))"
      proof -
        from \<open>p \<noteq> []\<close> have "p = butlast p @ [last p]"
          by simp
        from 1 have "distinct p"
          using distinct_awalk_verts distinct_verts_imp_distinct by blast
        then have "distinct (map au_of (butlast p @ [last p]))"
          using \<open>p = butlast p @ [last p]\<close> 
          using distinct_map inj_on_au_of_awalk[OF \<open>awalk x p y\<close>] by metis
        then have "au_of (last p) \<notin> au_of ` set (butlast p)"
          by fastforce
        from Max.insert_not_elem[OF _ this] False
        have "Max (insert (au_of (last p)) (au_of ` set (butlast p)))
          = max (au_of (last p)) (Max (au_of ` set (butlast p)))"
          using awalk_butlast awalk_ends by blast
        then have "\<dots> = Max (au_of ` set p)"
          using \<open>au_of (last p) \<notin> au_of ` set (butlast p)\<close>
          by (subst (3) \<open>p = butlast p @ [last p]\<close>) simp
        with au_y show ?thesis
          by (metis au_of_def awalk_Cons_iff awalk_ends awalk_last option.sel)
      qed
      finally show ?thesis .
    qed
  qed
qed

lemma find_newest_on_path_eq_None_iff:
  assumes "awalk x p y"
  shows "find_newest_on_path ufe x y = None \<longleftrightarrow> x = y"
  using find_newest_on_path_dom[OF assms] assms
proof(induction rule: find_newest_on_path.pinduct)
  case (1 x y)
  then show ?case
    using find_newest_on_path_eq_Max_au_of by (cases "x = y") simp_all
qed
  
theorem newest_on_path_find_newest_on_path:
  assumes "awalk x p y"
      and "x \<noteq> y"
    shows "newest_on_path (the (find_newest_on_path ufe x y)) x p y"
  using find_newest_on_path_eq_Max_au_of[OF assms] \<open>awalk x p y\<close>
  unfolding newest_on_path_def
  by simp

end

lemma (in ufe_forest) find_newest_on_path_lt_Some_length_unions:
  assumes "awalk x p y"
  shows "find_newest_on_path ufe x y < Some (length (unions ufe))"
proof(cases "x = y")
  case True
  then show ?thesis by simp
next
  case False
  with assms have "newest_on_path (the (find_newest_on_path ufe x y)) x p y"
    using newest_on_path_find_newest_on_path by blast
  with False newest_on_path_lt_length_unions show ?thesis
    by (cases "find_newest_on_path ufe x y") auto
qed

lemma ufe_rep_of_ufe_union_eq_cases:
  assumes "eff_union (uf_ds ufe) a b"
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes "ufe_rep_of (ufe_union ufe a b) x = ufe_rep_of (ufe_union ufe a b) y"
  obtains
    "ufe_rep_of ufe x = ufe_rep_of ufe y" |
    "ufe_rep_of ufe x \<noteq> ufe_rep_of ufe y"
    "ufe_rep_of ufe x = ufe_rep_of ufe a" "ufe_rep_of ufe y = ufe_rep_of ufe b" |
    "ufe_rep_of ufe x \<noteq> ufe_rep_of ufe y"
    "ufe_rep_of ufe x = ufe_rep_of ufe b" "ufe_rep_of ufe y = ufe_rep_of ufe a"
  using assms
  by (simp add: uf_ds_ufe_union_eq ufa_rep_of_ufa_union) metis

lemma find_newest_on_path_ufe_union_if_ufe_rep_of_neq:
  assumes "eff_union (uf_ds ufe) a b"
  assumes "ufe_rep_of ufe x \<noteq> ufe_rep_of ufe y"
  assumes "pre_digraph.awalk (ufe_forest_of (ufe_union ufe a b)) x pxy y"
  shows "find_newest_on_path (ufe_union ufe a b) x y = Some (length (unions ufe))"
proof -
  interpret ufe_forest where ufe = ufe .
  interpret ufe_union_forest: ufe_forest
    where ufe = "ufe_union ufe a b" .
  from assms ufa_union_awalk_eq have
    "x = ufe_rep_of ufe b"
    "pxy = (ufe_rep_of ufe b, ufe_rep_of ufe a) # awalk_from_rep (uf_ds ufe) y"
    using uf_ds_ufe_union_eq by metis+
  moreover from assms have
    "awalk (ufe_rep_of ufe y) (awalk_from_rep (uf_ds ufe) y) y"
    by (intro awalk_awalk_from_rep)
      (auto simp: verts_ufa_forest_of simp del: with_proj_simps)
  then have set_awalk_from_rep_subs_arcs:
    "set (awalk_from_rep (uf_ds ufe) y) \<subseteq> arcs (ufe_forest_of ufe)"
    by blast
  then have
    "ufe_union_forest.au_of ` set (awalk_from_rep (uf_ds ufe) y) =
      au_of ` set (awalk_from_rep (uf_ds ufe) y)"
    using ufe_union_au_of_eq_if_in_arcs[OF assms(1)] by force
  moreover have
    "ufe_union_forest.au_of (ufe_rep_of ufe b, ufe_rep_of ufe a) = length (unions ufe)"
    by (subst ufe_union_au_of_eq_if_head_eq[OF assms(1)]) simp_all
  ultimately have "ufe_union_forest.au_of ` set pxy =
    insert (length (unions ufe)) (au_of ` set (awalk_from_rep (uf_ds ufe) y))"
    by simp
  moreover have
    "\<forall>i \<in> au_of ` set (awalk_from_rep (uf_ds ufe) y). i \<le> length (unions ufe)"
    using set_awalk_from_rep_subs_arcs au_of_lt_length_unions
    by (simp add: in_mono order_less_imp_le)
  ultimately have "Max (ufe_union_forest.au_of ` set pxy) = length (unions ufe)"
    using Max_insert2 by (metis List.finite_set finite_imageI) 

  moreover from assms have
    "find_newest_on_path (ufe_union ufe a b) x y =
      Some (Max (ufe_union_forest.au_of ` set pxy))"
    using ufe_union_forest.find_newest_on_path_eq_Max_au_of
    by blast

  ultimately show ?thesis
    by simp
qed

lemma find_newest_on_path_ufe_union:
  assumes "eff_union (uf_ds ufe) a b"
  assumes "pre_digraph.awalk (ufe_forest_of (ufe_union ufe a b)) x pxy y"
  shows "find_newest_on_path (ufe_union ufe a b) x y = 
    (if ufe_rep_of ufe x = ufe_rep_of ufe y
      then find_newest_on_path ufe x y
      else Some (length (unions ufe)))"
proof -
  interpret ufe_forest ufe .
  interpret ufe_union_forest: ufe_forest "ufe_union ufe a b" .

  consider
    (ufe_rep_of_neq) "ufe_rep_of ufe x \<noteq> ufe_rep_of ufe y" |
    (eq) "x = y" |
    (ufe_rep_of_eq) "x \<noteq> y" "ufe_rep_of ufe x = ufe_rep_of ufe y"
    by auto
  then show ?thesis
  proof cases
    case eq
    then show ?thesis
      using find_newest_on_path_eq_if_eq by simp
  next
    case ufe_rep_of_neq
    note find_newest_on_path_ufe_union_if_ufe_rep_of_neq[OF assms(1) this assms(2)]
    with ufe_rep_of_neq show ?thesis
      by simp
  next
    case ufe_rep_of_eq
    with assms have "awalk x pxy y"
      using awalk_if_ufe_union_awalk by blast
    then have pxy_subs_arcs: "set pxy \<subseteq> arcs (ufe_forest_of ufe)"
      by blast

    from assms ufe_rep_of_eq have
      "find_newest_on_path (ufe_union ufe a b) x y =
        Some (Max (ufe_union_forest.au_of ` set pxy))"
      using ufe_union_forest.find_newest_on_path_eq_Max_au_of by blast
    also have "\<dots> = Some (Max (au_of ` set pxy))"
      using pxy_subs_arcs ufe_union_au_of_eq_if_in_arcs[OF assms(1)]
      by (metis (no_types, lifting) image_cong in_mono)
    also have "\<dots> = find_newest_on_path ufe x y"
      using find_newest_on_path_eq_Max_au_of[OF \<open>awalk x pxy y\<close> \<open>x \<noteq> y\<close>]
      by simp
    finally show ?thesis
      using ufe_rep_of_eq by simp
  qed
qed
      
lemma find_newest_on_path_ufe_union_if_reachable:
  assumes "eff_union (uf_ds ufe) a b"
  assumes "x \<rightarrow>\<^sup>*\<^bsub>ufe_forest_of (ufe_union ufe a b)\<^esub> y"
  shows "find_newest_on_path (ufe_union ufe a b) x y = 
    (if ufe_rep_of ufe x = ufe_rep_of ufe y then find_newest_on_path ufe x y
    else Some (length (unions ufe)))"
proof -
  interpret ufe_union_forest: ufe_forest "ufe_union ufe a b" .

  note find_newest_on_path_ufe_union[OF assms(1)]
  with assms show ?thesis
    using ufe_union_forest.reachable_awalk by blast
qed
              
end