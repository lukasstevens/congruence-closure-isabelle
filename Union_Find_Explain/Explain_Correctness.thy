section \<open>Correctness proofs for Explain\<close>
theory Explain_Correctness
  imports Helper_Functions
begin
             
lemma (in ufe_invars) neq_find_newest_on_path_ufa_lca_if_neq:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "x \<noteq> y"
  defines "lca_x_y \<equiv> ufa_lca (uf_ds ufe_ds) x y"
  shows "find_newest_on_walk ufe_ds lca_x_y x \<noteq> find_newest_on_walk ufe_ds lca_x_y y"
proof -
  from assms interpret ufe_tree where x = x
    by unfold_locales
  from assms have "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
    using in_verts_if_rep_of_eq by simp
  note lca_ulca = lca_ufa_lca[OF x_in_verts this]
  then obtain px py where
    px: "awalk lca_x_y px x" and py: "awalk lca_x_y py y"
    unfolding lca_x_y_def by (meson lca_reachableD reachable_awalk)
  note find_newest_on_walk_dom = this[THEN find_newest_on_walk_dom]
  note find_newest_on_walk_psimps = this[THEN find_newest_on_walk.psimps]
  consider (lca_x) "x = lca_x_y" | (lca_y) "y = lca_x_y" | (not_lca) "lca_x_y \<noteq> x" "lca_x_y \<noteq> y"
    using \<open>x \<noteq> y\<close> by auto
  then show ?thesis
  proof cases
    case lca_x
    then have "find_newest_on_walk ufe_ds lca_x_y x = None"
      using find_newest_on_walk_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_x have "find_newest_on_walk ufe_ds lca_x_y y \<noteq> None"
      using find_newest_on_walk_eq_Max_au_of[OF py] by blast      
    ultimately show ?thesis
      by force
  next
    case lca_y
    then have "find_newest_on_walk ufe_ds lca_x_y y = None"
      using find_newest_on_walk_psimps(1) by auto
    moreover
    from \<open>x \<noteq> y\<close> lca_y have "find_newest_on_walk ufe_ds lca_x_y x \<noteq> None"
      using find_newest_on_walk_eq_Max_au_of[OF px] by blast      
    ultimately show ?thesis
      by force
  next
    case not_lca
    moreover
    from not_lca px py have "px \<noteq> []" "py \<noteq> []"
      using awalk_empty_ends px by blast+
    from not_lca px py obtain ix iy where
      ix: "ix \<in> set px" "find_newest_on_walk ufe_ds lca_x_y x = Some (au_of ix)" and
      iy: "iy \<in> set py" "find_newest_on_walk ufe_ds lca_x_y y = Some (au_of iy)"
      using newest_on_walkE[unfolded newest_on_walk_def]
      by (simp add: find_newest_on_walk_eq_Max_au_of) metis
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
  defines "find_newest_union \<equiv> find_newest_on_walk (ufe_union ufe_ds a b)"
  shows ufe_lca_ufe_union_eq_if_ufe_rep_of_eq:
    "ufe_lca_union x y = ufa_lca (uf_ds ufe_ds) x y"
    and find_newest_on_walk_ufe_union_ufe_lca:
    "find_newest_union (ufe_lca_union x y) x =
      find_newest_on_walk ufe_ds (ufe_lca_union x y) x"
    "find_newest_union (ufe_lca_union x y) y =
      find_newest_on_walk ufe_ds (ufe_lca_union x y) y"
    and find_newest_on_walk_ufe_union_ufe_lca_lt_Some_length_unions:
    "find_newest_union (ufe_lca_union x y) x < Some (length (unions ufe_ds))"
    "find_newest_union (ufe_lca_union x y) y < Some (length (unions ufe_ds))"
    and find_newest_on_walk_ufe_union_ufe_lca_neq:
    "x \<noteq> y \<Longrightarrow>
      find_newest_union (ufe_lca_union x y) x \<noteq> find_newest_union (ufe_lca_union x y) y"
    and unions_nth_find_newest_on_walk_ufe_union_ufe_lca:
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
  moreover note find_newest_on_walk_ufe_union[OF eff_union]
  moreover from assms ufe_rep_of_union_eq have
    "ufe_rep_of ufe_ds (ufe_lca_union x y) = ufe_rep_of ufe_ds x"
    unfolding lca_eq
    using ufe_tree.ufa_rep_of_ufa_lca ufe_tree.in_verts_if_rep_of_eq by metis
  ultimately show newest_eq:
    "find_newest_union (ufe_lca_union x y) x = find_newest_on_walk ufe_ds (ufe_lca_union x y) x"
    "find_newest_union (ufe_lca_union x y) y = find_newest_on_walk ufe_ds (ufe_lca_union x y) y"
    using assms ufe_tree.ufe_union_awalk_if_awalk[OF eff_union]
    by metis+

  note px py
  from this[THEN ufe_tree.find_newest_on_walk_lt_Some_length_unions] show newest_lt:
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


lemma explain_code_induct[consumes 3, case_names eq newest_x newest_y]:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  assumes "\<And>x. x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)) \<Longrightarrow> P x x"
  assumes "\<And>x y ax bx.
    \<lbrakk> x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)); y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; x \<noteq> y
    ; find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x >
      find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y
    ; unions ufe_ds ! the (find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x) = (ax, bx)
    ; P x ax; P bx y
    \<rbrakk> \<Longrightarrow> P x y"
  assumes "\<And>x y ay by.
    \<lbrakk> x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)); y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
    ; x \<noteq> y
    ; find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x <
      find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y
    ; unions ufe_ds ! the (find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y) = (ay, by)
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
  let ?newest_union = "find_newest_on_walk (ufe_union ufe_ds a b)"

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
    find_newest_on_walk_ufe_union_ufe_lca
    find_newest_on_walk_ufe_union_ufe_lca_lt_Some_length_unions
    find_newest_on_walk_ufe_union_ufe_lca_neq
    unions_nth_find_newest_on_walk_ufe_union_ufe_lca
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
      note this[THEN find_newest_on_walk_ufe_union[OF ufe_union.hyps(2-)]]
      ultimately show 
        "?newest_union (?lca x y) x = Some (length (unions ufe_ds))"
        using 2 ufe_union.hyps(2) by simp
      moreover from 2 ufe_union.prems(2,3) have
        "?newest_union (?lca x y) x \<noteq> ?newest_union (?lca x y) y"
        using ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast
      moreover have
        "?newest_union (?lca x y) y \<le> Some (length (unions ufe_ds))"
        using ufe_tree_union.find_newest_on_walk_lt_Some_length_unions[OF py]
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
      note this[THEN find_newest_on_walk_ufe_union[OF ufe_union.hyps(2-)]]
      ultimately show 
        "?newest_union (?lca x y) y = Some (length (unions ufe_ds))"
        using 3 ufe_union.hyps(2) by simp
      moreover from 3 ufe_union.prems(2,3) have
        "?newest_union (?lca x y) x \<noteq> ?newest_union (?lca x y) y"
        using ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast
      moreover have
        "?newest_union (?lca x y) x \<le> Some (length (unions ufe_ds))"
        using ufe_tree_union.find_newest_on_walk_lt_Some_length_unions[OF px]
        by (cases "?newest_union (?lca x y) x") simp_all
      ultimately show "?newest_union (?lca x y) x < Some (length (unions ufe_ds))"
        by simp
    qed
    ultimately show ?thesis
      using 3 ufe_union.prems(1-3)
      by (intro ufe_union.prems(6)[OF _ _ _ _ _ _ \<open>P x b\<close> \<open>P a y\<close>]) simp_all
  qed
qed
  
lemma explain_code:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows
    "explain ufe_init (unions ufe_ds) x y =
    (if x = y then ReflP x
    else 
      let
        lca = ufa_lca (uf_ds ufe_ds) x y;
        newest_x = find_newest_on_walk ufe_ds lca x;
        newest_y = find_newest_on_walk ufe_ds lca y
      in
        if newest_x \<ge> newest_y then
          let (ax, bx) = unions ufe_ds ! the newest_x
          in TransP (TransP (explain ufe_init (unions ufe_ds) x ax) (AssmP (the newest_x)))
            (explain ufe_init (unions ufe_ds) bx y)
        else
          let (ay, by) = unions ufe_ds ! the newest_y
          in TransP (TransP (explain ufe_init (unions ufe_ds) x by) (SymP (AssmP (the newest_y))))
            (explain ufe_init (unions ufe_ds) ay y))"
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
  note this[THEN ufe_tree_union.find_newest_on_walk_lt_Some_length_unions]
  moreover have "t < Some (Suc n) \<Longrightarrow> t \<le> Some n" for t n
    by (cases t) simp_all
  ultimately have find_newest_on_walk_le:
    "find_newest_on_walk (ufe_union ufe_ds a b) ?lca x \<le> Some (length (unions ufe_ds))"
    "find_newest_on_walk (ufe_union ufe_ds a b) ?lca y \<le> Some (length (unions ufe_ds))"
    by simp_all
  from ufe_union.prems px py have find_newest_on_walk_neq:
    "find_newest_on_walk (ufe_union ufe_ds a b) ?lca x \<noteq>
      find_newest_on_walk (ufe_union ufe_ds a b) ?lca y"
    if "x \<noteq> y"
    using that ufe_invars_union.neq_find_newest_on_path_ufa_lca_if_neq by blast

  from ufe_union.hyps(2) in_Field_ufa_\<alpha> ufe_union.prems(3) show ?case
  proof(cases rule: ufe_rep_of_ufe_union_eq_cases)
    case 1
    with ufe_union have
      "explain ufe_init (unions (ufe_union ufe_ds a b)) x y =
      explain ufe_init (unions ufe_ds) x y"
      using ufe_invars.ufe_ds_eq_ufe_unions
      by (cases "x = y") (simp_all add: Let_def)
    moreover
    from ufe_union.hyps(2) 1 in_Field_ufa_\<alpha> have "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y =
      ufa_lca (uf_ds ufe_ds) x y"
      using ufe_invars.ufe_lca_ufe_union_eq_if_ufe_rep_of_eq by blast
    moreover
    from this ufe_union.hyps(2) 1 in_Field_ufa_\<alpha> have
      "find_newest_on_walk (ufe_union ufe_ds a b) (ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y) x =
      find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) x" (is "_ = ?newest_x") and
      "find_newest_on_walk (ufe_union ufe_ds a b) (ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y) y =
      find_newest_on_walk ufe_ds (ufa_lca (uf_ds ufe_ds) x y) y" (is "_ = ?newest_y")
      using ufe_invars.find_newest_on_walk_ufe_union_ufe_lca by metis+
    moreover from calculation ufe_union.hyps(2) 1 in_Field_ufa_\<alpha> have
      "unions (ufe_union ufe_ds a b) ! the ?newest_x = unions ufe_ds ! the ?newest_x"
      if "?newest_y < ?newest_x"
      using that
      by (metis ufe_invars.unions_nth_find_newest_on_walk_ufe_union_ufe_lca(1))
    moreover from calculation ufe_union.hyps(2) 1 in_Field_ufa_\<alpha> have
      "unions (ufe_union ufe_ds a b) ! the ?newest_y = unions ufe_ds ! the ?newest_y"
      if "?newest_y > ?newest_x"
      using that
      by (metis ufe_invars.unions_nth_find_newest_on_walk_ufe_union_ufe_lca(2))
    moreover from "1" in_Field_ufa_\<alpha> have "?newest_x \<noteq> ?newest_y" if "x \<noteq> y"
      using that ufe_invars.neq_find_newest_on_path_ufa_lca_if_neq by blast
    moreover note * = calculation

    from 1 ufe_tree.x_in_verts in_Field_ufa_\<alpha> have "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
      using ufe_tree.in_verts_if_rep_of_eq by simp
    with ufe_tree.x_in_verts obtain px py where
      px: "ufe_tree.awalk (ufa_lca (uf_ds ufe_ds) x y) px x" and
      py: "ufe_tree.awalk (ufa_lca (uf_ds ufe_ds) x y) py y"
      using ufe_tree.lca_ufa_lca ufe_tree.lca_reachableD ufe_tree.reachable_awalk
      by metis

    from * consider
      (eq) "x = y" | (newest_x) "?newest_y < ?newest_x" | (newest_y) "?newest_y > ?newest_x"
      using linorder_cases by blast
    then show ?thesis
    proof cases
      case newest_x
      then have "?newest_y \<le> ?newest_x"
        by simp
      obtain ax bx where [simp]:
        "unions ufe_ds ! the ?newest_x = (ax, bx)"
        using find_newest_on_walk.cases by blast
      moreover from px newest_x have
        "ufe_tree.newest_on_walk (the ?newest_x) (ufa_lca (uf_ds ufe_ds) x y) px x"
        using ufe_tree.newest_on_walk_find_newest_on_walk
        by (metis find_newest_on_walk_if_eq less_option_None)
      ultimately have
        "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds ax"
        "ufe_rep_of ufe_ds bx = ufe_rep_of ufe_ds y"
        using 1 newest_x ufe_tree.ufe_rep_of_eq_if_newest_on_walk
        by (metis find_newest_on_walk_if_eq less_option_None)+
      then have
        "explain ufe_init (unions (ufe_union ufe_ds a b)) x ax =
          explain ufe_init (unions ufe_ds) x ax"
        "explain ufe_init (unions (ufe_union ufe_ds a b)) bx y =
          explain ufe_init (unions ufe_ds) bx y"
        using ufe_invars.ufe_ds_eq_ufe_unions by fastforce+
      with * in_Field_ufa_\<alpha> show ?thesis
        using ufe_union.IH[OF in_Field_ufa_\<alpha> 1] \<open>?newest_y \<le> ?newest_x\<close>
        by (auto simp: Let_def simp del: unions_ufe_union)
    next
      case newest_y
      then have "\<not> ?newest_y \<le> ?newest_x"
        by simp
      obtain ay "by" where [simp]:
        "unions ufe_ds ! the ?newest_y= (ay, by)"
        using find_newest_on_walk.cases by blast
      moreover from py newest_y have
        "ufe_tree.newest_on_walk (the ?newest_y) (ufa_lca (uf_ds ufe_ds) x y) py y"
        using ufe_tree.newest_on_walk_find_newest_on_walk
        by (metis find_newest_on_walk_if_eq less_option_None)
      ultimately have
        "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds by"
        "ufe_rep_of ufe_ds ay = ufe_rep_of ufe_ds y"
        using 1 newest_y ufe_tree.ufe_rep_of_eq_if_newest_on_walk 
        by (metis find_newest_on_walk_if_eq less_option_None)+
      then have
        "explain ufe_init (unions (ufe_union ufe_ds a b)) x by =
          explain ufe_init (unions ufe_ds) x by"
        "explain ufe_init (unions (ufe_union ufe_ds a b)) ay y =
          explain ufe_init (unions ufe_ds) ay y"
        using ufe_invars.ufe_ds_eq_ufe_unions by fastforce+
      with * in_Field_ufa_\<alpha> show ?thesis
        using ufe_union.IH[OF in_Field_ufa_\<alpha> 1] \<open>\<not> ?newest_y \<le> ?newest_x\<close>
        by (auto simp: Let_def simp del: unions_ufe_union)
    qed simp
  next
    case 2
    with ufe_union in_Field_ufa_\<alpha> have
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b" (is "?lca = _")
      using ufa_lca_ufa_union by (metis uf_ds_ufe_union)
    moreover from this 2 in_Field_ufa_\<alpha> have
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca x = Some (length (unions ufe_ds))"
      using ufe_invars.find_newest_on_walk_ufe_union_if_rep_of_neq[OF ufe_union.hyps(2) _ _ px]
      by (metis uf_ds_ufe_union ufa_rep_of_ufa_rep_of)
    moreover from this 2 have
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca y < Some (length (unions ufe_ds))"
      using find_newest_on_walk_le find_newest_on_walk_neq by fastforce
    moreover from calculation have
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca y \<le>
        find_newest_on_walk (ufe_union ufe_ds a b) ?lca x"
      by order
    ultimately show ?thesis
      using "2"(1) "2"(2,3)[symmetric]
      by (auto simp: ufe_invars.ufe_ds_eq_ufe_unions[symmetric])
  next
    case 3
    with ufe_union in_Field_ufa_\<alpha> have
      "ufa_lca (uf_ds (ufe_union ufe_ds a b)) x y = ufe_rep_of ufe_ds b" (is "?lca = _")
      using ufa_lca_ufa_union by (metis uf_ds_ufe_union)
    moreover from this 3 in_Field_ufa_\<alpha> have
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca y = Some (length (unions ufe_ds))"
      using ufe_invars.find_newest_on_walk_ufe_union_if_rep_of_neq[OF ufe_union.hyps(2) _ _ py]
      by (metis uf_ds_ufe_union ufa_rep_of_ufa_rep_of)
    moreover from this 3 have
      "find_newest_on_walk (ufe_union ufe_ds a b) ?lca x < Some (length (unions ufe_ds))"
      using find_newest_on_walk_le find_newest_on_walk_neq by fastforce
    moreover from calculation have
      "\<not> find_newest_on_walk (ufe_union ufe_ds a b) ?lca y \<le>
        find_newest_on_walk (ufe_union ufe_ds a b) ?lca x"
      by order
    ultimately show ?thesis
      using "3"(1) "3"(2,3)[symmetric]
      by (auto simp: ufe_invars.ufe_ds_eq_ufe_unions[symmetric])
  qed
qed

lemma proves_eq_explain:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "unions ufe_ds \<turnstile>\<^sub>= explain ufe_init (unions ufe_ds) x y : (x, y)"
  using assms
proof(induction arbitrary: x y rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    by (simp add: proves_eq.refl ufe_rep_of_ufe_init)
next
  case (ufe_union ufe_ds x y a b)
  then interpret ufe_invars: ufe_invars where ufe_ds = ufe_ds
    by blast

  note proves_eq.trans[OF proves_eq.trans]
  note proves_intros = this[OF _ proves_eq.assm] this[OF _ proves_eq.sym[OF proves_eq.assm]]
  note IH = ufe_union.IH[THEN weaken_proves_eq[where ?bs="[(x, y)]"]]
  from ufe_union.prems ufe_union.hyps(2) show ?case
    by (auto simp: Let_def ufe_invars.ufe_ds_eq_ufe_unions[symmetric] ufa_rep_of_ufa_union
        intro!: IH proves_intros split: if_splits)
qed

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
