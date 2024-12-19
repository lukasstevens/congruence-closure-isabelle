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
  assumes "awalk x p y"
  shows "find_newest_on_path_dom ufe_ds (x, y)"
proof -
  from assms have "y \<in> verts (ufe_tree_of ufe_ds pivot)"
    by blast
  then have "y \<in> Field (ufe_\<alpha> ufe_ds)"
    by blast
  show ?thesis
  proof(cases "p = []")
    case True
    then show ?thesis
      using assms awalk_empty_ends find_newest_on_path.domintros by blast
  next
    case False
    with \<open>y \<in> Field (ufe_\<alpha> ufe_ds)\<close> assms show ?thesis
    proof(induction arbitrary: p rule: ufa_rep_of_induct)
      case (rep i)
      then show ?case
        using awalk_and_ufa_parent_of_reflD(2) by blast
    next
      case (not_rep i)
      then have "awalk x (butlast p) (ufe_parent_of ufe_ds i)"
        using awalk_not_Nil_butlastD(1) awalk_Nil_iff
        by (simp add: awlast_butlast_eq_ufa_parent_of_if_awalk)
      with not_rep have
        "find_newest_on_path_dom ufe_ds (x, ufe_parent_of ufe_ds i)"
        by (metis awalk_empty_ends find_newest_on_path.domintros)
      then show ?case
        using find_newest_on_path.domintros by blast
    qed
  qed
qed

lemma find_newest_on_path_eq_Max_au_of:
  assumes "awalk x p y"
      and "x \<noteq> y"
    shows "find_newest_on_path ufe_ds x y = Some (Max (au_of ` set p))"
proof -
  from find_newest_on_path_dom[OF assms(1)] assms show ?thesis
  proof(induction arbitrary: p rule: find_newest_on_path.pinduct)
    case (1 x y)
    then have "y \<in> Field (ufe_\<alpha> ufe_ds)"
      using in_Field_ufa_\<alpha>_if_in_verts awalk_last_in_verts by blast
    with "1.prems" obtain au_y where au_y:
      "au_ds ufe_ds y = Some au_y"
      using lookup_au_ds_eq_None_iff ufa_parent_of_ufa_rep_of
      by (metis awalk_and_ufa_parent_of_reflD(1) not_None_eq)
    then show ?case
    proof(cases "x = ufe_parent_of ufe_ds y")
      case True
      with "1.prems" have p_eq: "p = [(ufe_parent_of ufe_ds y, y)]" (is "_ = [?a]")
        using awalk_ufa_parent_of unique_awalk_All by blast
      with "1.prems" au_y show ?thesis
        unfolding au_of_def find_newest_on_path.psimps[OF "1.hyps"]
        by (auto split: option.splits)
    next
      case False 
      from 1 have "p \<noteq> []"
        by auto
      with 1 have
        awalk_butlast: "awalk x (butlast p) (ufe_parent_of ufe_ds y)" and
        awalk_last: "awalk (ufe_parent_of ufe_ds y) [last p] y"
        using awalk_not_Nil_butlastD
        by (metis awlast_butlast_eq_ufa_parent_of_if_awalk)+
      with awalk_verts_append[where ?p="butlast p" and ?q="[last p]"]
      have awalk_verts_p:
        "awalk_verts x p = awalk_verts x (butlast p) @ [y]"
        using \<open>awalk x p y\<close> \<open>p \<noteq> []\<close> by auto

      from \<open>y \<in> Field (ufe_\<alpha> ufe_ds)\<close> have
        "ufe_parent_of ufe_ds y \<in> Field (ufe_\<alpha> ufe_ds)"
        by blast
      with False obtain au_p_y where au_p_y:
        "au_ds ufe_ds (ufe_parent_of ufe_ds y) = Some au_p_y"
        using lookup_au_ds_eq_None_iff ufa_parent_of_ufa_rep_of
        by (metis awalk_and_ufa_parent_of_reflD(1) awalk_butlast domD domIff)
      
      from \<open>x \<noteq> y\<close> au_y au_p_y have
        "find_newest_on_path ufe_ds x y =
          max (Some au_y) (find_newest_on_path ufe_ds x (ufe_parent_of ufe_ds y))"
      proof -
        have "find_newest_on_path_dom ufe_ds (x, ufe_parent_of ufe_ds y)"
          using awalk_butlast find_newest_on_path_dom by blast
        with False au_p_y have
          "find_newest_on_path ufe_ds x (ufe_parent_of ufe_ds y) \<noteq> None"
          using domIff
          by (fastforce simp: find_newest_on_path.psimps max_def split: option.splits)
        with "1.prems" au_y show ?thesis 
          unfolding find_newest_on_path.psimps[OF "1.hyps"(1)]
          by (auto simp: max_def)
      qed
      also have "\<dots> = Some (max au_y (Max (au_of ` set (butlast p))))"
      proof -
        note "1.IH"[OF \<open>x \<noteq> y\<close> \<open>awalk x (butlast p) (ufe_parent_of ufe_ds y)\<close>
            \<open>x \<noteq> ufe_parent_of ufe_ds y\<close>]
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
  shows "find_newest_on_path ufe_ds x y = None \<longleftrightarrow> x = y"
  using find_newest_on_path_dom[OF assms] assms
proof(induction rule: find_newest_on_path.pinduct)
  case (1 x y)
  then show ?case
    using find_newest_on_path_eq_Max_au_of by (cases "x = y") simp_all
qed
  
theorem newest_on_path_find_newest_on_path:
  assumes "awalk x p y"
      and "x \<noteq> y"
    shows "newest_on_path (the (find_newest_on_path ufe_ds x y)) x p y"
  using find_newest_on_path_eq_Max_au_of[OF assms] \<open>awalk x p y\<close>
  unfolding newest_on_path_def
  by simp

end

lemma (in ufe_tree) find_newest_on_path_lt_Some_length_unions:
  assumes "awalk x p y"
  shows "find_newest_on_path ufe_ds x y < Some (length (unions ufe_ds))"
proof(cases "x = y")
  case True
  then show ?thesis by simp
next
  case False
  with assms have "newest_on_path (the (find_newest_on_path ufe_ds x y)) x p y"
    using newest_on_path_find_newest_on_path by blast
  with False newest_on_path_lt_length_unions show ?thesis
    by (cases "find_newest_on_path ufe_ds x y") auto
qed

lemma ufe_rep_of_ufe_union_eq_cases:
  assumes "eff_union (uf_ds ufe_ds) a b"
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  assumes "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y"
  obtains
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y" |
    "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds a" "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds b" |
    "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds b" "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds a"
  using assms
  by (simp add: uf_ds_ufe_union_eq ufa_rep_of_ufa_union) metis

lemma find_newest_on_path_ufe_union_if_ufe_rep_of_neq:
  assumes "eff_union (uf_ds ufe_ds) a b"
  assumes "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  fixes pivot defines "T \<equiv> ufe_tree_of (ufe_union ufe_ds a b) pivot"
  assumes awalk_pxy:
    "pre_digraph.awalk T x pxy y"
  shows "find_newest_on_path (ufe_union ufe_ds a b) x y = Some (length (unions ufe_ds))"
proof -
  from assms have "pivot \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) pivot)"
    unfolding pre_digraph.awalk_def
    by (metis in_ufa_\<alpha>_if_in_verts in_vertsI part_equiv_trans_sym(1) part_equiv_ufa_\<alpha>)

  with assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and pivot = pivot
    by unfold_locales blast

  from assms awalk_pxy have
    "x \<in> Field (ufe_\<alpha> (ufe_union ufe_ds a b))"
    "y \<in> Field (ufe_\<alpha> (ufe_union ufe_ds a b))"
    by blast+
  with assms have
    x_in_Field_\<alpha>: "x \<in> Field (ufe_\<alpha> ufe_ds)" and
    y_in_Field_\<alpha>: "y \<in> Field (ufe_\<alpha> ufe_ds)"
    by simp_all

  from x_in_Field_\<alpha> interpret ufe_tree_x: ufe_tree
    where ufe_ds = ufe_ds and pivot = x
    by unfold_locales
  from y_in_Field_\<alpha> interpret ufe_tree_y: ufe_tree
    where ufe_ds = ufe_ds and pivot = y
    by unfold_locales
  interpret ufe_tree_z: ufe_tree where ufe_ds = ufe_ds and pivot = pivot
    using assms ufe_tree_union.pivot_in_Field_ufe_\<alpha>
    by unfold_locales simp_all

  from assms have
    rep_a_in_Field_\<alpha>: "ufe_rep_of ufe_ds a \<in> Field (ufe_\<alpha> ufe_ds)"
      (is "?rep_a \<in> _") and
    rep_b_in_Field_\<alpha>: "ufe_rep_of ufe_ds b \<in> Field (ufe_\<alpha> ufe_ds)"
      (is "?rep_b \<in> _")
    by blast+
  note this[THEN ufe_tree_x.awalk_from_rep_ufa_union[OF eff_unionD[OF assms(1)]]]
  then have awalk_from_rep_union_rep_a:
    "awalk_from_rep (uf_ds (ufe_union ufe_ds a b)) (ufe_rep_of ufe_ds a) =
    awalk_from_rep (uf_ds ufe_ds) (ufe_rep_of ufe_ds b) @ [(?rep_b, ?rep_a)]"
    using assms awalk_from_rep_rep_of
    by (simp add: uf_ds_ufe_union_eq_if_eff_union)

  from awalk_pxy have
    "ufe_rep_of (ufe_union ufe_ds a b) x = ufe_rep_of (ufe_union ufe_ds a b) y"
    unfolding T_def by fastforce
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
    note ufe_tree_x.ufa_union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufe_tree_of (ufe_union ufe_ds a b) x)
        ?rep_a (awalk_from_rep (uf_ds ufe_ds) x) x"
      by (simp add: uf_ds_ufe_union_eq_if_eff_union)
    then have union_awalk_awalk_from_rep_x:
      "ufe_tree_union.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy[unfolded T_def] ufe_tree_union.awalkE')
    moreover
    from 1 have
      "ufe_tree_y.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufe_tree_y.awalk_awalk_from_rep by fastforce
    note ufe_tree_y.ufa_union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufe_tree_of (ufe_union ufe_ds a b) y)
        ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
      by (simp add: uf_ds_ufe_union_eq_if_eff_union)
    then have union_awalk_awalk_from_rep_y:
      "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy[unfolded T_def] ufe_tree_union.awalkE')
    moreover
    have "ufe_tree_union.awalk ?rep_b [(?rep_b, ?rep_a)] ?rep_a"
    proof -
      from calculation have "?rep_a \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) pivot)"
        by blast
      note ufe_tree_union.awalk_awalk_from_rep[OF this]
      then show ?thesis
        using assms awalk_from_rep_union_rep_a awalk_from_rep_rep_of
        by (simp add: uf_ds_ufe_union_eq_if_eff_union)
    qed
    ultimately have
      "ufe_tree_union.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
      using awalk_pxy[unfolded T_def] ufe_tree_union.awalk_Cons_iff ufe_tree_union.awalk_appendI
      by auto
    then have
      "ufe_tree_y.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
      using 1 union_awalk_awalk_from_rep_y ufe_tree_union.unique_awalk_All
      by (metis ufe_tree_y.awalk_awalk_from_rep ufe_tree_y.pivot_in_verts)
    with 1 have "ufe_tree_y.awalk x pxy y"
      using ufe_tree_x.awlast_awalk_from_rep[OF ufe_tree_x.pivot_in_verts]
      by (simp add: ufe_tree_y.awalk_Cons_iff awalk_verts_with_proj_eq)
    with \<open>ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y\<close> show ?thesis
      by auto
  next
    case 2
    then have x_awalk_awalk_from_rep_x:
      "ufe_tree_x.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufe_tree_x.awalk_awalk_from_rep by fastforce
    note ufe_tree_x.ufa_union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufe_tree_of (ufe_union ufe_ds a b) x)
        ?rep_b (awalk_from_rep (uf_ds ufe_ds) x) x"
      by (simp add: uf_ds_ufe_union_eq_if_eff_union)
    then have union_awalk_awalk_from_rep_x:
      "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x) x"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy[unfolded T_def] ufe_tree_union.awalkE')
    moreover
    from 2 have y_awalk_awalk_from_rep_y:
      "ufe_tree_y.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufe_tree_y.awalk_awalk_from_rep by fastforce
    note ufe_tree_y.ufa_union_awalk_if_awalk[OF _ _this]
    with assms have
      "pre_digraph.awalk (ufe_tree_of (ufe_union ufe_ds a b) y)
        ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
      by (simp add: uf_ds_ufe_union_eq_if_eff_union)
    then have union_awalk_awalk_from_rep_y:
      "ufe_tree_union.awalk ?rep_a (awalk_from_rep (uf_ds ufe_ds) y) y"
      using ufa_tree_of_eq_if_in_verts
      by (metis awalk_pxy[unfolded T_def] ufe_tree_union.awalkE')
    moreover
    from 2 have "ufe_tree_union.awalk ?rep_b [(?rep_b, ?rep_a)] ?rep_a"
    proof -
      from calculation have "?rep_a \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) pivot)"
        by blast
      note ufe_tree_union.awalk_awalk_from_rep[OF this]
      then show ?thesis
        using assms(1,3) awalk_from_rep_rep_of awalk_from_rep_union_rep_a
        by (simp add: uf_ds_ufe_union_eq_if_eff_union)
    qed
    ultimately have union_awalk_rep_b_y:
      "ufe_tree_union.awalk ?rep_b (awalk_from_rep (uf_ds ufe_ds) x @ pxy) y"
      "ufe_tree_union.awalk ?rep_b ((?rep_b, ?rep_a) # awalk_from_rep (uf_ds ufe_ds) y) y"
      using awalk_pxy[unfolded T_def] ufe_tree_union.awalk_Cons_iff ufe_tree_union.awalk_appendI
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
        using ufe_tree_union.awalk_ends[OF awalk_pxy[unfolded T_def]] by metis
      then have "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
        using ufe_tree_y.awalk_hd_in_verts by auto
      with \<open>ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y\<close> show False
        by blast
    qed
    then have "?rep_b = x"
      using x_awalk_awalk_from_rep_x by auto
    with awalk_pxy[unfolded T_def] union_awalk_rep_b_y have "(?rep_b, ?rep_a) \<in> set pxy"
      using ufe_tree_union.unique_awalk_All
      by (metis list.set_intros(1))
    moreover
    have "ufe_tree_union.au_of (?rep_b, ?rep_a) = length (unions ufe_ds)"
      using assms unfolding ufe_tree_union.au_of_def
      by simp
    moreover have "ufe_tree_union.au_of e < length (unions (ufe_union ufe_ds a b))"
      if "e \<in> set pxy" for e
      using that awalk_pxy[unfolded T_def] ufe_tree_union.au_of_lt_length_unions
      by (meson subsetD ufe_tree_union.awalkE')
    then have "ufe_tree_union.au_of e \<le> length (unions ufe_ds)"
      if "e \<in> set pxy" for e
      using that assms by (simp add: less_Suc_eq order_le_less)
    ultimately have "Max (ufe_tree_union.au_of ` set pxy) = length (unions ufe_ds)"
      by (intro Max_eqI) (auto simp: rev_image_eqI)
    moreover note ufe_tree_union.find_newest_on_path_eq_Max_au_of[OF awalk_pxy[unfolded T_def]]
    ultimately show ?thesis
      using \<open>ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y\<close> by auto
  qed
qed

lemma find_newest_on_path_ufe_union:
  assumes "eff_union (uf_ds ufe_ds) a b"
  fixes pivot defines "T \<equiv> ufe_tree_of (ufe_union ufe_ds a b) pivot"
  assumes awalk_pxy: "pre_digraph.awalk T x pxy y"
  shows "find_newest_on_path (ufe_union ufe_ds a b) x y = 
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y then find_newest_on_path ufe_ds x y
    else Some (length (unions ufe_ds)))"
proof -
  from assms have "pivot \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) pivot)"
    unfolding pre_digraph.awalk_def
    by (metis in_ufa_\<alpha>_if_in_verts in_vertsI part_equiv_trans_sym(1) part_equiv_ufa_\<alpha>)

  with assms interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and pivot = pivot
    by unfold_locales blast

  from assms awalk_pxy have
    "x \<in> Field (ufe_\<alpha> (ufe_union ufe_ds a b))"
    "y \<in> Field (ufe_\<alpha> (ufe_union ufe_ds a b))"
    by blast+
  with assms have
    x_in_Field_\<alpha>: "x \<in> Field (ufe_\<alpha> ufe_ds)" and
    y_in_Field_\<alpha>: "y \<in> Field (ufe_\<alpha> ufe_ds)"
    by simp_all

  from x_in_Field_\<alpha> interpret ufe_tree_x: ufe_tree 
    where ufe_ds = ufe_ds and pivot = x
    by unfold_locales
  from y_in_Field_\<alpha> interpret ufe_tree_y: ufe_tree
    where ufe_ds = ufe_ds and pivot = y
    by unfold_locales
  interpret ufe_tree_z: ufe_tree
    where ufe_ds = ufe_ds and pivot = pivot
    using assms ufe_tree_union.pivot_in_Field_ufe_\<alpha>
    by unfold_locales simp_all

  have ?thesis if "x \<noteq> y" "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  proof -
    from awalk_pxy have "x \<in> verts T"
      unfolding T_def by blast
    note ufa_tree_of_eq_if_in_verts[OF this[unfolded T_def]]
    with assms(2) that awalk_pxy have "ufe_tree_x.awalk x pxy y"
      by (intro ufe_tree_x.awalk_if_ufe_union_awalk[OF assms(1)]) simp_all
    with that have
      "find_newest_on_path ufe_ds x y = Some (Max (ufe_tree_x.au_of ` set pxy))"
      using ufe_tree_x.find_newest_on_path_eq_Max_au_of by blast
    moreover from that awalk_pxy have
      "find_newest_on_path (ufe_union ufe_ds a b) x y =
      Some (Max (ufe_tree_union.au_of ` set pxy))"
      using ufe_tree_union.find_newest_on_path_eq_Max_au_of unfolding T_def by blast
    moreover have "ufe_tree_x.au_of e = ufe_tree_union.au_of e" if "e \<in> set pxy" for e
    proof -
      from assms have "ufe_rep_of ufe_ds a \<notin> dom (au_ds ufe_ds)"
        using lookup_au_ds_eq_None_iff ufa_rep_of_in_Field_ufa_\<alpha>I ufa_rep_of_ufa_rep_of
        by blast
      moreover note ufe_tree_x.head_in_dom_lookup_if_in_arcs
      with that have "head (ufe_tree_of ufe_ds x) e \<in> dom (au_ds ufe_ds)"
        using \<open>ufe_tree_x.awalk x pxy y\<close> by blast
      ultimately show ?thesis
        using assms lookup_au_ds_eq_None_iff[where z="ufe_rep_of ufe_ds b"]
        unfolding ufe_tree_x.au_of_def ufe_tree_union.au_of_def                  
        by auto
    qed
    ultimately show ?thesis
      using that by simp
  qed
  moreover have ?thesis if "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
    using assms awalk_pxy that
    using find_newest_on_path_ufe_union_if_ufe_rep_of_neq 
    by (simp add: uf_ds_ufe_union_eq)
  ultimately show ?thesis
    by force
qed

lemma find_newest_on_path_ufe_union_if_reachable:
  assumes "eff_union (uf_ds ufe_ds) a b"
  assumes "x \<rightarrow>\<^sup>*\<^bsub>ufe_tree_of (ufe_union ufe_ds a b) pivot\<^esub> y"
  shows "find_newest_on_path (ufe_union ufe_ds a b) x y = 
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y then find_newest_on_path ufe_ds x y
    else Some (length (unions ufe_ds)))"
proof -
  from assms(2) have "x \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) pivot)"
    using reachable_in_vertsE by fast
  with in_ufa_\<alpha>_if_in_verts have "(pivot, x) \<in> ufe_\<alpha> (ufe_union ufe_ds a b)"
    by blast
  then have "pivot \<in> Field (ufe_\<alpha> (ufe_union ufe_ds a b))"
    using FieldI1 by fastforce
  then interpret ufe_tree_union: ufe_tree
    where ufe_ds = "ufe_union ufe_ds a b" and pivot = pivot
    by unfold_locales
  from assms(2) obtain p where "ufe_tree_union.awalk x p y"
    using ufe_tree_union.reachable_awalk by blast
  from find_newest_on_path_ufe_union[OF assms(1) this] show ?thesis .
qed
                     
end