theory UFA_Forest
  imports
    "Union_Find.Union_Find"
    "Tree_Theory.LCA_Directed_Forest"
begin

context
  fixes uf :: ufa
begin

definition "ufa_forest_of \<equiv>
  let
    vs = Field (ufa_\<alpha> uf)
  in
    \<lparr> pverts = vs
    , parcs = {(ufa_parent_of uf x, x) |x. x \<in> vs \<and> ufa_parent_of uf x \<noteq> x}
    \<rparr>"

function (domintros) awalk_from_rep where
  "awalk_from_rep x =
    (let
      px = ufa_parent_of uf x
    in
      if px = x then [] else awalk_from_rep px @ [(px, x)])"
  by auto

function (domintros) awalk_verts_from_rep where
  "awalk_verts_from_rep x =
    (let
      px = ufa_parent_of uf x
    in
      if px = x then [] else awalk_verts_from_rep px) @ [x]"
  by auto

end

lemma verts_ufa_forest_of:
  "verts (ufa_forest_of uf) = Field (ufa_\<alpha> uf)"
  unfolding ufa_forest_of_def Let_def by simp

lemma verts_ufa_forest_of_ufa_union:
  "verts (ufa_forest_of (ufa_union uf a b)) = verts (ufa_forest_of uf)"
  unfolding verts_ufa_forest_of by simp

lemma arcs_ufa_forest_of:
  "arcs (ufa_forest_of uf) =
    {(ufa_parent_of uf x, x) |x. x \<in> Field (ufa_\<alpha> uf) \<and> ufa_rep_of uf x \<noteq> x}"
  unfolding ufa_forest_of_def using ufa_rep_of_nrefl_iff_ufa_parent_of_nrefl
  by (auto simp: Let_def)

lemma in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of:
  "x \<in> verts (ufa_forest_of uf) \<Longrightarrow> x \<in> Field (ufa_\<alpha> uf)"
  unfolding verts_ufa_forest_of
  by (simp add: FieldI2)

lemmas in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_ofE[elim] =
  in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of[elim_format]

lemma ufa_parent_of_in_verts_if_in_verts_ufa_forest_of[simp, intro]:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "ufa_parent_of uf x \<in> verts (ufa_forest_of uf)"
  using assms verts_ufa_forest_of by auto

lemma ufa_rep_of_in_verts_if_in_verts_ufa_forest_of[simp, intro]:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "ufa_rep_of uf x \<in> verts (ufa_forest_of uf)"
  using assms verts_ufa_forest_of by auto

lemma eq_ufa_parent_of_if_mem_arcs_ufa_forest_of:
  assumes "(x, y) \<in> arcs (ufa_forest_of uf)"
  shows "x = ufa_parent_of uf y"
  using assms unfolding ufa_forest_of_def Let_def by simp

lemma awalk_from_rep_domI[simp, intro]:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_from_rep_dom uf x"
  using assms
  by (induction rule: ufa_rep_of_induct) (use awalk_from_rep.domintros in \<open>blast+\<close>)

lemma awalk_verts_from_rep_domI[simp, intro]:
  assumes "awalk_from_rep_dom uf x"
  shows "awalk_verts_from_rep_dom uf x"
  using assms
proof(induction rule: awalk_from_rep.pinduct)
  case (1 x)
  then show ?case
    by (intro awalk_verts_from_rep.domintros[of uf x]) auto
qed

lemma awalk_verts_from_rep_eq_map_fst_awalk_from_rep:
  assumes "awalk_from_rep_dom uf x"
  shows "awalk_verts_from_rep uf x = map fst (awalk_from_rep uf x) @ [x]"
  using assms 
proof(induction rule: awalk_from_rep.pinduct)
  case (1 x)
  then show ?case
    by (auto simp: awalk_verts_from_rep.psimps awalk_from_rep.psimps Let_def)
qed

lemma awalk_from_rep_rep_of:
  assumes "x \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_from_rep uf (ufa_rep_of uf x) = []"
  using assms awalk_from_rep.psimps by auto

locale ufa_forest =
  fixes uf :: ufa
begin

sublocale fin_digraph "ufa_forest_of uf"
proof unfold_locales
  show "finite (verts (ufa_forest_of uf))"
    unfolding verts_ufa_forest_of using finite_Field_ufa_\<alpha> by blast
  then show "finite (arcs (ufa_forest_of uf))"
    unfolding ufa_forest_of_def by (auto simp: Let_def)
qed (auto simp: ufa_forest_of_def Let_def)

lemma awalk_ufa_parent_of:
  assumes "x \<in> verts (ufa_forest_of uf)"
  assumes "ufa_parent_of uf x \<noteq> x"
  shows "awalk (ufa_parent_of uf x) [(ufa_parent_of uf x, x)] x"
proof -
  from assms have "(ufa_parent_of uf x, x) \<in> arcs (ufa_forest_of uf)"
    unfolding ufa_forest_of_def Let_def by simp
  note arc_implies_awalk[OF this]
  then show ?thesis
    by simp
qed

lemma awalk_from_rep_ufa_rep_of_if_in_verts:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "awalk_from_rep uf (ufa_rep_of uf x) = []"
  using assms awalk_from_rep_rep_of by blast 

lemma awlast_awalk_from_rep:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "awlast (ufa_rep_of uf x) (awalk_from_rep uf x) = x"
proof -
  from assms have "awalk_from_rep_dom uf x"
    by (intro awalk_from_rep_domI in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of)
  then show ?thesis
    using assms
  proof (induction rule: awalk_from_rep.pinduct)
    case (1 x)
    then show ?case
      using ufa_rep_of_if_refl_ufa_parent_of
      by (auto simp: awalk_from_rep.psimps Let_def pre_digraph.awalk_verts_conv)
  qed
qed

lemma awalk_awalk_from_rep:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
proof -
  from assms have "awalk_from_rep_dom uf x"
    by (intro awalk_from_rep_domI in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of)
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 x)
    then show ?case
    proof(cases "ufa_parent_of uf x = x")
      case True
      with 1 show ?thesis
        using awalk_from_rep_ufa_rep_of_if_in_verts
        using ufa_rep_of_if_refl_ufa_parent_of
        by (metis awalk_Nil_iff)
    next
      case False
      with 1 have
        "awalk (ufa_rep_of uf x) (awalk_from_rep uf (ufa_parent_of uf x)) (ufa_parent_of uf x)"
        using verts_ufa_forest_of by force
      moreover have "awalk (ufa_parent_of uf x) [(ufa_parent_of uf x, x)] x"
        using "1" False awalk_ufa_parent_of by blast
      ultimately show ?thesis
        using 1 False by (simp add: awalk_from_rep.psimps Let_def)
    qed
  qed
qed

lemma Ex1_awalk_ufa_rep_of:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "\<exists>!p. awalk (ufa_rep_of uf x) p x"
proof
  note awalk_awalk_from_rep[OF assms] 
  then show "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
    by assumption

  show "p = awalk_from_rep uf x" if "awalk (ufa_rep_of uf x) p x" for p
    using that assms
  proof(induction p arbitrary: x rule: rev_induct)
    case Nil
    then show ?case
      using awalk_from_rep_rep_of
      by (metis awalk_Nil_iff verts_ufa_forest_of)
  next
    case (snoc a p)
    then have "awalk (ufa_rep_of uf x) p (fst a)" "a \<in> arcs (ufa_forest_of uf)"
      by auto
    moreover from this have
      "a = (ufa_parent_of uf x, x)" "ufa_parent_of uf x \<noteq> x"
      unfolding ufa_forest_of_def using snoc.prems(1) by (auto simp: Let_def)
    moreover from snoc.prems have
      "ufa_rep_of uf (ufa_parent_of uf x) = ufa_rep_of uf x"
      using ufa_rep_of_ufa_parent_of by blast
    ultimately have
      "awalk (ufa_rep_of uf (ufa_parent_of uf x)) p (ufa_parent_of uf x)"
      by simp
    with snoc.IH have "p = awalk_from_rep uf (ufa_parent_of uf x)"
      by blast
    with \<open>a = (ufa_parent_of uf x, x)\<close> \<open>ufa_parent_of uf x \<noteq> x\<close> snoc.prems show ?case
      using awalk_from_rep_domI[OF in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of]
      by (auto simp: awalk_from_rep.psimps[where ?x=x] Let_def)
  qed
qed

lemma eq_awalk_from_rep_if_awalk_ufa_rep_of:
  assumes "x \<in> verts (ufa_forest_of uf)"
  assumes "awalk (ufa_rep_of uf x) p x"
  shows "p = awalk_from_rep uf x"
  using assms awalk_awalk_from_rep Ex1_awalk_ufa_rep_of
  by auto

lemma awalk_verts_from_rep_eq_awalk_verts:
  assumes "x \<in> verts (ufa_forest_of uf)"
  shows "awalk_verts_from_rep uf x = awalk_verts (ufa_rep_of uf x) (awalk_from_rep uf x)"
proof -
  from assms have "awalk_from_rep_dom uf x"
    by blast
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 x)
    let ?px = "ufa_parent_of uf x"
    show ?case
    proof(cases "?px = x")
      case True
      with 1 show ?thesis
        using awalk_from_rep_ufa_rep_of_if_in_verts
        using ufa_rep_of_if_refl_ufa_parent_of
        by (fastforce simp: awalk_verts_from_rep.psimps)
    next
      case False
      from 1 have "ufa_rep_of uf ?px = ufa_rep_of uf x"
        by (simp add: in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of)
      with 1 have "awalk (ufa_rep_of uf x) (awalk_from_rep uf ?px) ?px"
        using awalk_awalk_from_rep
        by (metis ufa_parent_of_in_verts_if_in_verts_ufa_forest_of)
      note awalk_appendI[OF this awalk_ufa_parent_of]
      with 1 False have "awalk (ufa_rep_of uf x) (awalk_from_rep uf ?px @ [(?px, x)]) x"
        by blast
      note awalk_verts_append[OF this]
      moreover from 1 False have "awalk_verts_from_rep uf ?px
        = awalk_verts (ufa_rep_of uf x) (awalk_from_rep uf ?px)"
        using ufa_parent_of_in_verts_if_in_verts_ufa_forest_of
        using \<open>ufa_rep_of uf ?px = ufa_rep_of uf x\<close> by simp
      ultimately show ?thesis
        using 1 False
        by (auto simp: Let_def awalk_verts_from_rep.psimps[where ?x=x] awalk_from_rep.psimps[where ?x=x])
    qed
  qed
qed

lemma awalk_verts_from_rep_eq_Cons:
  assumes "x \<in> verts (ufa_forest_of uf)"
  obtains px where "awalk_verts_from_rep uf x = ufa_rep_of uf x # px"
  using assms awalk_awalk_from_rep awalk_verts_from_rep_eq_awalk_verts 
  by (metis awalk_verts_non_Nil awhd_of_awalk list.collapse)

lemma ufa_rep_of_eq_if_awalk:
  assumes "awalk u p v"
  shows "ufa_rep_of uf u = ufa_rep_of uf v"
  using assms
proof(induction p arbitrary: v rule: rev_induct)
  case Nil
  then show ?case
    using awalk_Nil_iff by simp
next
  case (snoc a p)
  then have
    "awalk u p (tail (ufa_forest_of uf) a)"
    "awalk (tail (ufa_forest_of uf) a) [a] v"
    using awalk_Cons_iff by auto
  moreover from this have
    "tail (ufa_forest_of uf) a = ufa_parent_of uf v"
    using eq_ufa_parent_of_if_mem_arcs_ufa_forest_of by auto
  ultimately have "ufa_rep_of uf u = ufa_rep_of uf (ufa_parent_of uf v)"
    using snoc.IH by simp
  then show ?case
    using snoc.prems ufa_rep_of_ufa_parent_of
    by (metis awalk_last_in_verts verts_ufa_forest_of)
qed

lemma awalk_if_in_awalk_verts_from_rep:
  assumes "x \<in> verts (ufa_forest_of uf)"
  assumes "y \<in> set (awalk_verts_from_rep uf x)"
  obtains p where "awalk y p x"
proof -
  from assms have "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
    using assms awalk_awalk_from_rep by auto
  with assms that show ?thesis
    by (metis awalk_decomp awalk_verts_from_rep_eq_awalk_verts)
qed

lemma ufa_rep_of_eq_if_reachable:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>ufa_forest_of uf\<^esub> v"
  shows "ufa_rep_of uf u = ufa_rep_of uf v"
  using assms ufa_rep_of_eq_if_awalk
  using reachable_awalk by blast

lemma root_iff_ufa_rep_of_refl:
  assumes "v \<in> verts (ufa_forest_of uf)"
  shows "root v \<longleftrightarrow> ufa_rep_of uf v = v"
  using assms unfolding root_def in_arcs_def verts_ufa_forest_of arcs_ufa_forest_of
  by auto

lemma root_ufa_rep_of[simp, intro]:
  assumes "v \<in> verts (ufa_forest_of uf)"
  shows "root (ufa_rep_of uf v)"
proof -
  have "ufa_rep_of uf (ufa_rep_of uf v) = ufa_rep_of uf v"
    by (intro ufa_rep_of_ufa_rep_of in_Field_ufa_\<alpha>_if_in_verts_ufa_forest_of assms)
  then show ?thesis
    using assms
    by (subst root_iff_ufa_rep_of_refl) (simp_all del: with_proj_simps)
qed

lemma eq_ufa_rep_of_if_root_reachable:
  assumes "root r" "r \<rightarrow>\<^sup>*\<^bsub>ufa_forest_of uf\<^esub> v"
  shows "r = ufa_rep_of uf v"
  using assms
  by (metis root_iff_ufa_rep_of_refl root_in_vertsD ufa_rep_of_eq_if_reachable)

sublocale fin_directed_forest "ufa_forest_of uf"
proof unfold_locales
  show "\<exists>!r. root r \<and> r \<rightarrow>\<^sup>*\<^bsub>ufa_forest_of uf\<^esub> v"
    if v_in_verts: "v \<in> verts (ufa_forest_of uf)" for v
  proof
    from that show "root (ufa_rep_of uf v) \<and> ufa_rep_of uf v \<rightarrow>\<^sup>*\<^bsub>ufa_forest_of uf\<^esub> v"
      using reachable_awalkI[OF awalk_awalk_from_rep] by auto

    show "r = ufa_rep_of uf v"
      if "root r \<and> r \<rightarrow>\<^sup>*\<^bsub>ufa_forest_of uf\<^esub> v" for r
    proof -
      from that have "r \<in> verts (ufa_forest_of uf)"
        by blast
      with v_in_verts that show ?thesis
        using eq_ufa_rep_of_if_root_reachable
        by (auto simp del: with_proj_simps)
    qed
  qed

  show "\<exists>\<^sub>\<le>\<^sub>1p. awalk u p v" for u v
  proof (cases "u \<rightarrow>\<^sup>*\<^bsub>ufa_forest_of uf\<^esub> v")
    case False
    then have "\<nexists>p. awalk u p v"
      using reachable_awalk by simp
    then show ?thesis
      by (intro Uniq_I) blast
  next
    case True
    then obtain p where "awalk u p v"
      using reachable_awalk by blast
    have "\<exists>!p. awalk u p v"
    proof
      from \<open>awalk u p v\<close> show "awalk u p v"
        by assumption
      show "p' = p" if "awalk u p' v" for p'
      proof -
        from that \<open>awalk u p v\<close> have
          "awalk (ufa_rep_of uf u) (awalk_from_rep uf u @ p) v"
          "awalk (ufa_rep_of uf u) (awalk_from_rep uf u @ p') v"
          using awalk_awalk_from_rep awalk_hd_in_verts by force+
        with True show "p' = p"
          using Ex1_awalk_ufa_rep_of ufa_rep_of_eq_if_reachable
          by (metis awalk_last_in_verts same_append_eq)
      qed
    qed
    then show ?thesis
      by (intro Uniq_I) blast
  qed
qed
    
lemma awalk_and_ufa_rep_of_reflD:
  assumes "awalk y p x"
  assumes "ufa_rep_of uf x = x"
  shows "y = x" "p = []"
proof -
  show "p = []"
  proof(rule ccontr)
    assume "p \<noteq> []"
    with assms obtain y' where "y' \<rightarrow>\<^bsub>ufa_forest_of uf\<^esub> x" "y' \<noteq> x"
      using loopfree.adj_not_same by (metis reachable1_awalkI tranclD2)
    moreover from this have "y' = ufa_parent_of uf x"
      using eq_ufa_parent_of_if_mem_arcs_ufa_forest_of by auto
    ultimately show False
      using assms ufa_parent_of_ufa_rep_of
      by (metis awalk_last_in_verts verts_ufa_forest_of)
  qed
  with assms show "y = x"
    using awalk_empty_ends by blast
qed

lemma awlast_butlast_eq_ufa_parent_of_if_awalk:
  assumes "awalk y p x"
  assumes "p \<noteq> []"
  shows "awlast y (butlast p) = ufa_parent_of uf x"
proof(cases "ufa_rep_of uf x = x")
  case True
  with assms awalk_and_ufa_rep_of_reflD show ?thesis
    by simp
next
  case False
  from assms have "p = butlast p @ [last p]"
    by simp
  with assms have "awalk (awlast y (butlast p)) [last p] x"
    using awalk_not_Nil_butlastD by blast
  from assms have "x \<in> verts (ufa_forest_of uf)"
    by blast
  with \<open>awalk (awlast y (butlast p)) [last p] x\<close>
  show "awlast y (butlast p) = ufa_parent_of uf x"
    using awalk_Cons_iff eq_ufa_parent_of_if_mem_arcs_ufa_forest_of by auto
qed

lemma awalk_singletonD:
  assumes "awalk x [a] y"
  shows "x = ufa_parent_of uf y" "a = (ufa_parent_of uf y, y)"
  using assms eq_ufa_parent_of_if_mem_arcs_ufa_forest_of
  by (cases a; auto)+

lemma not_rep_if_in_tl_awalk_verts:
  assumes "awalk x p y"
  assumes "v \<in> set (tl (awalk_verts x p))"
  shows "ufa_rep_of uf v \<noteq> v"
  using assms
proof(induction p arbitrary: y v rule: rev_induct)
  case (snoc a as)   
  then show ?case
  proof(cases "v \<in> set (tl (awalk_verts x as))")
    case True
    from \<open>awalk x (as @ [a]) y\<close> have
      "awalk x as (ufa_parent_of uf (awlast x (as @ [a])))"
      using awlast_butlast_eq_ufa_parent_of_if_awalk
      by (metis awalkE awalk_append_iff snoc_eq_iff_butlast)
    from snoc.IH[OF this True] show ?thesis .
  next
    case False
    with snoc.prems have "awalk (awlast x as) [a] y"
      by simp
    moreover from snoc.prems False have "v = head (ufa_forest_of uf) a"
      using awalk_verts_append[OF \<open>awalk x (as @ [a]) y\<close>]
      by (cases a) auto
    with snoc.prems False have "y = v"
      by auto
    ultimately show ?thesis
      using awalk_and_ufa_rep_of_reflD(2) by blast
  qed
qed simp

context
  fixes a b
  assumes a_b_in_Field_ufa_\<alpha>: "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
  assumes ufa_rep_of_neq: "ufa_rep_of uf a \<noteq> ufa_rep_of uf b"
begin

interpretation ufa_union_forest: ufa_forest where uf = "ufa_union uf a b"
  by unfold_locales

lemma verts_ufa_forest_of_ufa_union_eq:
  "verts (ufa_forest_of (ufa_union uf a b)) = verts (ufa_forest_of uf)"
  using a_b_in_Field_ufa_\<alpha> unfolding verts_ufa_forest_of
  by simp

lemma arcs_ufa_forest_of_ufa_union_eq:
  "arcs (ufa_forest_of (ufa_union uf a b)) =
    insert (ufa_rep_of uf b, ufa_rep_of uf a) (arcs (ufa_forest_of uf))"
  using a_b_in_Field_ufa_\<alpha> ufa_rep_of_neq unfolding ufa_forest_of_def
  by (auto simp: Let_def ufa_parent_of_ufa_union)

lemma ufa_forest_of_ufa_union_eq_add_arc:
  "with_proj (ufa_forest_of (ufa_union uf a b)) =
    add_arc (ufa_rep_of uf b, ufa_rep_of uf a)"
  unfolding with_proj_def pre_digraph.add_arc_def
  using verts_ufa_forest_of_ufa_union_eq arcs_ufa_forest_of_ufa_union_eq
  using ufa_union_forest.adj_in_verts by force

lemma ufa_union_awalk_if_awalk:
  assumes "awalk x p y"
  shows "ufa_union_forest.awalk x p y"
  using assms awalk_add_arc_if_awalk ufa_forest_of_ufa_union_eq_add_arc
  by simp

lemma awalk_if_ufa_union_awalk:
  assumes "ufa_union_forest.awalk x p y"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "awalk x p y"
proof -
  from assms have "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
    using awalk_awalk_from_rep verts_ufa_forest_of_ufa_union_eq by blast
  moreover from this assms have
    "ufa_union_forest.awalk (ufa_rep_of uf x) (awalk_from_rep uf x @ p) y"
    by (meson ufa_union_awalk_if_awalk ufa_union_forest.awalk_appendI)
  moreover from assms have
    "awalk (ufa_rep_of uf x) (awalk_from_rep uf y) y"
    using awalk_awalk_from_rep verts_ufa_forest_of_ufa_union_eq
    using ufa_union_forest.awalk_last_in_verts by simp
  moreover from calculation have "awalk_from_rep uf y = awalk_from_rep uf x @ p"
    using ufa_union_forest.ufa_rep_of_eq_if_awalk ufa_union_forest.unique_awalk
    using ufa_union_awalk_if_awalk by metis
  ultimately show "awalk x p y"
    using \<open>awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x\<close> by force
qed

lemma awalk_from_rep_ufa_union:
  assumes "y \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_from_rep (ufa_union uf a b) y = 
    (if ufa_rep_of uf a = ufa_rep_of uf y then [(ufa_rep_of uf b, ufa_rep_of uf y)] else [])
    @ awalk_from_rep uf y"
proof -
  from a_b_in_Field_ufa_\<alpha> assms have "awalk_from_rep_dom (ufa_union uf a b) y"
    by simp
  then show ?thesis
    using \<open>y \<in> Field (ufa_\<alpha> uf)\<close>
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 y)
    then show ?case
    proof(cases "ufa_parent_of uf y = y")
      case True
      with 1 a_b_in_Field_ufa_\<alpha> ufa_rep_of_neq assms(1) show ?thesis
        using ufa_rep_of_if_refl_ufa_parent_of
        by (simp add: awalk_from_rep.psimps ufa_parent_of_ufa_union)
    next
      case False
      let ?px = "ufa_parent_of (ufa_union uf a b) y"
      from 1 False a_b_in_Field_ufa_\<alpha> have parent_of_union_y[simp]:
        "ufa_parent_of (ufa_union uf a b) y = ufa_parent_of uf y"
        by (metis ufa_parent_of_ufa_rep_of ufa_parent_of_ufa_union)
      from False "1.IH"[OF HOL.refl] have awalk_from_rep_py:
        "awalk_from_rep (ufa_union uf a b) ?px =
          (if ufa_rep_of uf a = ufa_rep_of uf y then [(ufa_rep_of uf b, ufa_rep_of uf y)] else []) @
          awalk_from_rep uf (ufa_parent_of uf y)"
        using "1.prems" by simp
      from "1.prems" have "awalk_from_rep_dom uf y"
        by blast
      with False have "awalk_from_rep uf (ufa_parent_of uf y) @ [(ufa_parent_of uf y, y)] =
        awalk_from_rep uf y"
        by (simp add: awalk_from_rep.psimps Let_def)
      with False show ?thesis
        unfolding awalk_from_rep.psimps[OF "1.hyps", unfolded Let_def]
        unfolding awalk_from_rep_py
        by auto
    qed
  qed
qed

lemma awalk_verts_from_rep_ufa_union:
  assumes "y \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_verts_from_rep (ufa_union uf a b) y = 
    (if ufa_rep_of uf a = ufa_rep_of uf y then [ufa_rep_of uf b] else [])
    @ awalk_verts_from_rep uf y"
  using awalk_from_rep_ufa_union[OF assms] assms a_b_in_Field_ufa_\<alpha>
  using awalk_verts_from_rep_eq_map_fst_awalk_from_rep
  by simp

end

end

end
