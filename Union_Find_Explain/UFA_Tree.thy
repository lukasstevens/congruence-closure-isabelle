theory UFA_Tree
  imports
    UF_ADT
    Map_ADT
    "Separation_Logic_Imperative_HOL.Union_Find"
    "Tree_Theory.LCA_Directed_Tree"
begin

context union_find_parent_adt
begin

context
  fixes uf :: 'uf
begin

definition "ufa_tree_of x \<equiv>
  let
    vs = uf_\<alpha> uf `` {x}
  in
    \<lparr> pverts = vs
    , parcs = {(uf_parent_of uf x, x) |x. x \<in> vs \<and> uf_parent_of uf x \<noteq> x}
    \<rparr>"

function (domintros) awalk_from_rep where
  "awalk_from_rep x =
    (let
      px = uf_parent_of uf x
    in
      if px = x then [] else awalk_from_rep px @ [(px, x)])"
  by auto

function (domintros) awalk_verts_from_rep where
  "awalk_verts_from_rep x =
    (let
      px = uf_parent_of uf x
    in
      (if px = x then [] else awalk_verts_from_rep px) @ [x])"
  by auto

end

end

context union_find_parent_invar
begin

lemma verts_ufa_tree_of:
  "verts (ufa_tree_of uf x) = uf_\<alpha> uf `` {x}"
  unfolding ufa_tree_of_def by simp

lemma in_Field_\<alpha>_if_in_verts:
  "y \<in> verts (ufa_tree_of uf x) \<Longrightarrow> y \<in> Field (uf_\<alpha> uf)"
  unfolding verts_ufa_tree_of
  by (simp add: FieldI2)

lemmas in_Field_\<alpha>_if_in_vertsE[elim] = in_Field_\<alpha>_if_in_verts[elim_format]

lemma in_vertsI:
  assumes "(x, y) \<in> uf_\<alpha> uf"
  shows "y \<in> verts (ufa_tree_of uf x)"
  using assms unfolding verts_ufa_tree_of by blast

lemma ufa_tree_of_eq_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "ufa_tree_of uf y = ufa_tree_of uf x"
proof -
  note part_equiv_\<alpha>
  then have "uf_\<alpha> uf `` {y} = uf_\<alpha> uf `` {x}"
    using assms unfolding verts_ufa_tree_of
    using part_equiv_sym part_equiv_trans by fast
  then show ?thesis
    unfolding ufa_tree_of_def Let_def
    by simp
qed
  
lemma in_verts_ufa_tree_ofD:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "(x, y) \<in> uf_\<alpha> uf"
  using assms verts_ufa_tree_of by simp_all

lemma parent_of_in_verts_ufa_tree_ofI[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "uf_parent_of uf y \<in> verts (ufa_tree_of uf x)"
  using assms \<alpha>_rep_of parent_of_in_\<alpha> rep_of_parent_of
  by (safe intro!: in_vertsI dest!: in_verts_ufa_tree_ofD) (metis FieldI1 FieldI2)

lemma rep_of_eq_if_in_verts_ufa_tree_of[simp]:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "NO_MATCH x y"
  shows "uf_rep_of uf y = uf_rep_of uf x"
  using assms
  by (metis FieldI1 FieldI2 \<alpha>_rep_of in_verts_ufa_tree_ofD)

lemma awalk_from_rep_domI[simp, intro]:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "awalk_from_rep_dom uf x"
  using wf_parent_of assms
proof(induction rule: wf_induct_rule)
  case (less x)
  then show ?case
    by (intro awalk_from_rep.domintros[of uf x]) auto
qed

lemma awalk_verts_from_rep_domI[simp, intro]:
  assumes "awalk_from_rep_dom uf x"
  shows "awalk_verts_from_rep_dom uf x"
  using assms
proof(induction rule: awalk_from_rep.pinduct)
  case (1 x)
  then show ?case
    by (intro awalk_verts_from_rep.domintros[of uf x]) auto
qed
 
end

locale ufa_tree = union_find_parent_invar where uf = uf for uf + 
  fixes x
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (uf_\<alpha> uf)"
      and finite_eq_class: "\<And>y. finite (uf_\<alpha> uf `` {y})"
begin

sublocale fin_digraph "ufa_tree_of uf x"
proof(unfold_locales)
  from finite_eq_class show "finite (verts (ufa_tree_of uf x))"
    unfolding verts_ufa_tree_of by blast
  then show "finite (arcs (ufa_tree_of uf x))"
    unfolding ufa_tree_of_def
    by (auto simp: Image_singleton)

  show "tail (ufa_tree_of uf x) e \<in> verts (ufa_tree_of uf x)"
    if "e \<in> arcs (ufa_tree_of uf x)" for e
    using that part_equiv_trans[OF part_equiv_\<alpha> _ parent_of_in_\<alpha>_sym]
    by (auto simp: FieldI2 ufa_tree_of_def)
qed (auto simp: ufa_tree_of_def)


lemma x_in_verts[simp, intro]: "x \<in> verts (ufa_tree_of uf x)"
  using \<alpha>_rep_of unfolding verts_ufa_tree_of
  by fastforce

lemma ufa_tree_of_parent_of[simp]:
  "ufa_tree_of uf (uf_parent_of uf x) = ufa_tree_of uf x"
  using ufa_tree_of_eq_if_in_verts parent_of_in_verts_ufa_tree_ofI
  by blast

lemma ufa_tree_of_rep_of[simp]:
  "ufa_tree_of uf (uf_rep_of uf x) = ufa_tree_of uf x"
  by (intro ufa_tree_of_eq_if_in_verts in_vertsI Pair_rep_of_in_\<alpha>_if_in_Field_\<alpha>) blast

lemma awalk_parent_of:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "uf_parent_of uf y \<noteq> y"
  shows "awalk (uf_parent_of uf y) [(uf_parent_of uf y, y)] y"
  using assms arc_implies_awalk
  unfolding ufa_tree_of_def by auto

lemma awalk_from_rep_rep_of:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awalk_from_rep uf (uf_rep_of uf y) = []"
proof -
  from x_in_verts have rep_of_in_Field: "uf_rep_of uf x \<in> Field (uf_\<alpha> uf)"
    by (metis Field_iff in_verts_ufa_tree_ofD ufa_tree_of_rep_of)
  from in_verts_ufa_tree_ofD[OF assms] have "uf_rep_of uf y = uf_rep_of uf x"
    using part_equiv_sym[OF part_equiv_\<alpha>]
    by (subst \<alpha>_rep_of) (auto simp: Field_iff)
  with assms have "awalk_from_rep_dom uf (uf_rep_of uf y)"
    by (intro awalk_from_rep_domI) auto
  then show ?thesis
    using parent_of_refl_iff_rep_of_refl[OF rep_of_in_Field]
    using \<open>uf_rep_of uf y = uf_rep_of uf x\<close>
    by (simp add: awalk_from_rep.psimps Let_def)
qed

lemma rep_of_if_parent_of_refl:
  assumes "y \<in> verts (ufa_tree_of uf x)" "z \<in> verts (ufa_tree_of uf x)"
  assumes "uf_parent_of uf y = y"
  shows "uf_rep_of uf z = y"
  using assms
  by (simp add: in_Field_\<alpha>_if_in_verts parent_of_refl_iff_rep_of_refl)
                        
lemma awlast_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awlast (uf_rep_of uf x) (awalk_from_rep uf y) = y"
proof -
  from assms have "awalk_from_rep_dom uf y"
    by (intro awalk_from_rep_domI in_Field_\<alpha>_if_in_verts)
  then show ?thesis
    using assms rep_of_if_parent_of_refl[OF _ x_in_verts]
    by (induction rule: awalk_from_rep.pinduct)
      (auto simp: awalk_from_rep.psimps pre_digraph.awalk_verts_conv Let_def)
qed

lemma awalk_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awalk (uf_rep_of uf y) (awalk_from_rep uf y) y"
proof -
  from assms have "awalk_from_rep_dom uf y"
    by (intro awalk_from_rep_domI in_Field_\<alpha>_if_in_verts)
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 y)
    then show ?case
    proof(cases "uf_parent_of uf y = y")
      case True
      with 1 show ?thesis
        using parent_of_refl_iff_rep_of_refl[OF in_Field_\<alpha>_if_in_verts]
        by (simp add: awalk_from_rep.psimps awalk_Nil_iff)
    next
      case False
      with 1 have "awalk (uf_rep_of uf y) (awalk_from_rep uf (uf_parent_of uf y)) (uf_parent_of uf y)"
        using parent_of_in_verts_ufa_tree_ofI
        by simp
      moreover have "awalk (uf_parent_of uf y) [(uf_parent_of uf y, y)] y"
        using "1" False awalk_parent_of by blast
      ultimately show ?thesis
        using 1 False by (simp add: awalk_from_rep.psimps Let_def)
    qed
  qed
qed

lemma unique_awalk_ufa_tree_of_rep:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "\<exists>!p. awalk (uf_rep_of uf x) p y"
proof
  note in_Field_\<alpha>_if_in_verts[OF assms]
  with assms interpret y: ufa_tree where uf = uf and x = y
    using finite_eq_class
    by unfold_locales simp_all
  from assms have "uf_rep_of uf y = uf_rep_of uf x"
    by auto
  then show "awalk (uf_rep_of uf x) (awalk_from_rep uf y) y"
    using assms y.awalk_awalk_from_rep
    using ufa_tree_of_eq_if_in_verts by force

  show "p = awalk_from_rep uf y" if "awalk (uf_rep_of uf x) p y" for p
    using that \<open>uf_rep_of uf y = uf_rep_of uf x\<close> assms
  proof(induction p arbitrary: y rule: rev_induct)
    case Nil
    then show ?case
      using awalk_from_rep_rep_of
      by (fastforce simp: awalk_Nil_iff)
  next
    case (snoc a p)
    then have "awalk (uf_rep_of uf x) p (fst a)" "a \<in> arcs (ufa_tree_of uf x)"
      by auto
    then have "a = (uf_parent_of uf y, y)" "uf_parent_of uf y \<noteq> y"
      unfolding ufa_tree_of_def using snoc.prems(1) by auto
    note snoc.IH[OF \<open>awalk (uf_rep_of uf x) p (fst a)\<close>]
    with snoc.prems have "p = awalk_from_rep uf (uf_parent_of uf y)"
      unfolding \<open>a = (uf_parent_of uf y, y)\<close>
      by auto
    with \<open>a = (uf_parent_of uf y, y)\<close> \<open>uf_parent_of uf y \<noteq> y\<close> snoc.prems show ?case
      using awalk_from_rep_domI[OF in_Field_\<alpha>_if_in_verts]
      by (auto simp: awalk_from_rep.psimps[where ?x=y] Let_def)
  qed
qed


lemma eq_awalk_from_rep_if_awalk_rep_of:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "awalk (uf_rep_of uf y) p y"
  shows "p = awalk_from_rep uf y"
  using assms awalk_awalk_from_rep unique_awalk_ufa_tree_of_rep
  by auto

sublocale fin_directed_tree "ufa_tree_of uf x" "uf_rep_of uf x"
  using unique_awalk_ufa_tree_of_rep
  by unfold_locales (use verts_ufa_tree_of x_in_verts in \<open>force+\<close>)

lemma awalk_verts_from_rep_eq_awalk_verts:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awalk_verts_from_rep uf y = awalk_verts (uf_rep_of uf y) (awalk_from_rep uf y)"
proof -
  from assms have "awalk_from_rep_dom uf y"
    using in_Field_\<alpha>_if_in_verts by blast
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 y)
    let ?py = "uf_parent_of uf y"
    show ?case
    proof(cases "?py = y")
      case True
      with 1 show ?thesis
        using awalk_from_rep_rep_of rep_of_if_parent_of_refl
        by (auto simp: awalk_verts_from_rep.psimps)
    next
      case False
      from 1 have "uf_rep_of uf ?py = uf_rep_of uf y"
        by (simp add: in_Field_\<alpha>_if_in_verts)
      with 1 have "awalk (uf_rep_of uf y) (awalk_from_rep uf ?py) ?py"
        using awalk_awalk_from_rep
        by (metis parent_of_in_verts_ufa_tree_ofI)
      note awalk_appendI[OF this awalk_parent_of]
      with 1 False have "awalk (uf_rep_of uf y) (awalk_from_rep uf ?py @ [(?py, y)]) y"
        by blast
      note awalk_verts_append[OF this]
      moreover from 1 False have "awalk_verts_from_rep uf ?py
        = awalk_verts (uf_rep_of uf y) (awalk_from_rep uf ?py)"
        using parent_of_in_verts_ufa_tree_ofI
        using \<open>uf_rep_of uf ?py = uf_rep_of uf y\<close> by simp
      ultimately show ?thesis
        using 1 False
        by (auto simp: Let_def awalk_verts_from_rep.psimps[where ?x=y] awalk_from_rep.psimps[where ?x=y])
    qed
  qed
qed

lemma awalk_and_parent_of_reflD:
  assumes "awalk z p y"
  assumes "uf_parent_of uf y = y"
  shows "y = z" "p = []"
proof -
  from assms(1) have
    "z \<in> verts (ufa_tree_of uf x)" and
    y_in_verts: "y \<in> verts (ufa_tree_of uf x)"
    by blast+
  with \<open>uf_parent_of uf y = y\<close> have "\<not> z \<rightarrow>\<^sup>+\<^bsub>ufa_tree_of uf x\<^esub> y" for z
    using x_in_verts not_root_if_dominated rep_of_if_parent_of_refl
    by (metis tranclD2)
  with assms have "z = uf_rep_of uf y"
    using rep_of_if_parent_of_refl
    by (metis awalk_Nil_iff reachable1_awalk)
  moreover from \<open>awalk z p y\<close> have "z \<in> verts (ufa_tree_of uf x)"
    by blast
  moreover note awalk_awalk_from_rep[OF y_in_verts]
  moreover from \<open>uf_parent_of uf y = y\<close> y_in_verts have "awalk_from_rep uf y = []"
    using awalk_from_rep_rep_of rep_of_if_parent_of_refl
    by blast
  moreover note eq_awalk_from_rep_if_awalk_rep_of[OF y_in_verts]
  moreover note in_verts_ufa_tree_ofD[OF y_in_verts]
  ultimately show "y = z" "p = []"
    using assms by (metis awalk_ends)+
qed

lemma awlast_butlast_eq_parent_of_if_awalk:
  assumes "awalk z p y"
  assumes "p \<noteq> []"
  shows "awlast z (butlast p) = uf_parent_of uf y"
proof(cases "uf_parent_of uf y = y")
  case True
  with assms awalk_and_parent_of_reflD show ?thesis
    by simp
next
  case False
  from assms have "p = butlast p @ [last p]"
    by simp
  with assms have "awalk (awlast z (butlast p)) [last p] y"
    using awalk_not_Nil_butlastD by blast
  from assms have "y \<in> verts (ufa_tree_of uf x)"
    by blast
  with awalk_parent_of[OF this False] \<open>awalk (awlast z (butlast p)) [last p] y\<close>
  show "awlast z (butlast p) = uf_parent_of uf y"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)
qed

lemma awalk_singletonD:
  assumes "awalk y [a] z"
  shows "y = uf_parent_of uf z" "a = (uf_parent_of uf z, z)"
proof -
  from assms have "uf_parent_of uf z \<noteq> z"
    using awalk_and_parent_of_reflD(2) by blast
  with assms awalk_parent_of have
    "awalk (uf_parent_of uf z) [(uf_parent_of uf z, z)] z"
    by auto
  with assms unique_awalk_All show
    "y = uf_parent_of uf z" "a = (uf_parent_of uf z, z)"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)+
qed

lemma not_rep_if_in_tl_awalk_verts:
  assumes "awalk y p z"
  assumes "v \<in> set (tl (awalk_verts y p))"
  shows "uf_parent_of uf v \<noteq> v"
  using assms
proof(induction p arbitrary: z v rule: rev_induct)
  case (snoc a as)   
  then show ?case
  proof(cases "v \<in> set (tl (awalk_verts y as))")
    case True
    from \<open>awalk y (as @ [a]) z\<close> have
      "awalk y as (uf_parent_of uf (awlast y (as @ [a])))"
      using awlast_butlast_eq_parent_of_if_awalk
      by (metis awalkE awalk_append_iff snoc_eq_iff_butlast)
    from snoc.IH[OF this True] show ?thesis .
  next
    case False
    with snoc.prems have "awalk (awlast y as) [a] z"
      by simp
    moreover from snoc.prems False have "v = head (ufa_tree_of uf x) a"
      using awalk_verts_append[OF \<open>awalk y (as @ [a]) z\<close>]
      by (cases a) auto
    with snoc.prems False have "z = v"
      by auto
    ultimately show ?thesis
      using awalk_and_parent_of_reflD(2) by blast
  qed
qed simp

context
  fixes a b
  assumes a_b_in_Field_\<alpha>: "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
begin

interpretation ufa_tree_union: ufa_tree where uf = "uf_union uf a b" and x = x
proof(unfold_locales)
  note finite_eq_class_per_union_if_finite_eq_class[OF part_equiv_\<alpha> finite_eq_class] 
  with a_b_in_Field_\<alpha> show "finite (uf_\<alpha> (uf_union uf a b) `` {y})" for y
    by simp
qed(use a_b_in_Field_\<alpha> in simp_all)

lemma in_verts_ufa_tree_of_union_if_in_verts[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "y \<in> verts (ufa_tree_of (uf_union uf a b) x)"
  using assms a_b_in_Field_\<alpha> 
  unfolding ufa_tree_of_def by auto

lemma in_arcs_ufa_tree_of_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufa_tree_of uf x)"
  shows "e \<in> arcs (ufa_tree_of (uf_union uf a b) x)"
  using assms x_in_Field_\<alpha> a_b_in_Field_\<alpha>
  unfolding ufa_tree_of_def
  apply(auto)
  sorry

lemma awalk_ufa_union_if_awalk:
  assumes "awalk y p z"
  shows "ufa_tree_union.awalk y p z"
  using assms
proof(induction p arbitrary: y)
  case Nil
  then show ?case
    using in_verts_ufa_tree_of_union_if_in_verts
    by (auto simp: awalk_Nil_iff ufa_tree_union.awalk_Nil_iff)
next
  case (Cons a p)
  then show ?case
    unfolding awalk_Cons_iff ufa_tree_union.awalk_Cons_iff
    using in_arcs_ufa_tree_of_union_if_in_arcs
    by auto
qed

end

end

end