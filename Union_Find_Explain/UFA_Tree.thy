theory UFA_Tree
  imports
    Union_Find
    "Tree_Theory.LCA_Directed_Tree"
begin

context
  fixes uf :: ufa
begin

definition "ufa_tree_of x \<equiv>
  let
    vs = ufa_\<alpha> uf `` {x}
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

lemma verts_eq_eq_class_ufa_\<alpha>:
  "verts (ufa_tree_of uf x) = ufa_\<alpha> uf `` {x}"
  unfolding ufa_tree_of_def by simp

lemma in_Field_ufa_\<alpha>_if_in_verts:
  "y \<in> verts (ufa_tree_of uf x) \<Longrightarrow> y \<in> Field (ufa_\<alpha> uf)"
  unfolding verts_eq_eq_class_ufa_\<alpha>
  by (simp add: FieldI2)

lemmas in_Field_ufa_\<alpha>_if_in_vertsE[elim] = in_Field_ufa_\<alpha>_if_in_verts[elim_format]

lemma in_vertsI:
  assumes "(x, y) \<in> ufa_\<alpha> uf"
  shows "y \<in> verts (ufa_tree_of uf x)"
  using assms unfolding verts_eq_eq_class_ufa_\<alpha> by blast

lemma ufa_tree_of_eq_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "ufa_tree_of uf y = ufa_tree_of uf x"
proof -
  note part_equiv_ufa_\<alpha>
  then have "ufa_\<alpha> uf `` {y} = ufa_\<alpha> uf `` {x}"
    using assms unfolding verts_eq_eq_class_ufa_\<alpha>
    using part_equiv_sym part_equiv_trans by fast
  then show ?thesis
    unfolding ufa_tree_of_def Let_def
    by simp
qed
  
lemma in_ufa_\<alpha>_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "(x, y) \<in> ufa_\<alpha> uf"
  using assms verts_eq_eq_class_ufa_\<alpha> by simp_all

lemma ufa_parent_of_in_verts_if_in_verts[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "ufa_parent_of uf y \<in> verts (ufa_tree_of uf x)"
  using assms
  using ufa_parent_of_in_Field_ufa_\<alpha>I ufa_rep_of_eq_iff_in_ufa_\<alpha> ufa_rep_of_ufa_parent_of
  by (safe intro!: in_vertsI dest!: in_ufa_\<alpha>_if_in_verts) (metis FieldI1 FieldI2 )

lemma ufa_rep_of_eq_if_in_verts[simp]:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "NO_MATCH x y"
  shows "ufa_rep_of uf y = ufa_rep_of uf x"
  using assms
  by (metis in_ufa_\<alpha>_if_in_verts ufa_rep_of_eq_if_in_ufa_\<alpha>)

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

locale ufa_tree =
  fixes uf x
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (ufa_\<alpha> uf)"
begin

sublocale fin_digraph "ufa_tree_of uf x"
proof(unfold_locales)
  from finite_ufa_eq_class show "finite (verts (ufa_tree_of uf x))"
    unfolding verts_eq_eq_class_ufa_\<alpha> ufa_eq_class_def by force
  then show "finite (arcs (ufa_tree_of uf x))"
    unfolding ufa_tree_of_def
    by (auto simp: Image_singleton)

  show "tail (ufa_tree_of uf x) e \<in> verts (ufa_tree_of uf x)"
    if "e \<in> arcs (ufa_tree_of uf x)" for e
    using that part_equiv_trans[OF part_equiv_ufa_\<alpha> _ _]
    using ufa_parent_of_in_verts_if_in_verts
    unfolding ufa_tree_of_def by auto
qed (auto simp: ufa_tree_of_def)

lemma x_in_verts[simp, intro]: "x \<in> verts (ufa_tree_of uf x)"
  using in_vertsI ufa_\<alpha>I by blast

lemma in_verts_if_rep_of_eq:
  assumes "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of uf y = ufa_rep_of uf x"
  shows "y \<in> verts (ufa_tree_of uf x)"
  using assms
  by (intro in_vertsI ufa_\<alpha>I) simp_all

lemma ufa_tree_of_parent_of[simp]:
  "ufa_tree_of uf (ufa_parent_of uf x) = ufa_tree_of uf x"
  using ufa_tree_of_eq_if_in_verts ufa_parent_of_in_verts_if_in_verts
  by blast

lemma ufa_tree_of_rep_of[simp]:
  "ufa_tree_of uf (ufa_rep_of uf x) = ufa_tree_of uf x"
  using ufa_rep_of_ufa_rep_of  
  by (intro ufa_tree_of_eq_if_in_verts in_vertsI ufa_\<alpha>I) auto

lemma awalk_parent_of:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "ufa_parent_of uf y \<noteq> y"
  shows "awalk (ufa_parent_of uf y) [(ufa_parent_of uf y, y)] y"
  using assms arc_implies_awalk
  unfolding ufa_tree_of_def by auto

lemma awalk_from_rep_rep_of_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awalk_from_rep uf (ufa_rep_of uf y) = []"
  using assms awalk_from_rep_rep_of by blast

lemma rep_of_if_parent_of_refl:
  assumes "y \<in> verts (ufa_tree_of uf x)" "z \<in> verts (ufa_tree_of uf x)"
  assumes "ufa_parent_of uf y = y"
  shows "ufa_rep_of uf z = y"
  using assms ufa_rep_of_if_refl_ufa_parent_of by fastforce
                        
lemma awlast_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awlast (ufa_rep_of uf x) (awalk_from_rep uf y) = y"
proof -
  from assms have "awalk_from_rep_dom uf y"
    by (intro awalk_from_rep_domI in_Field_ufa_\<alpha>_if_in_verts)
  then show ?thesis
    using assms rep_of_if_parent_of_refl[OF _ x_in_verts]
    by (induction rule: awalk_from_rep.pinduct)
      (auto simp: awalk_from_rep.psimps pre_digraph.awalk_verts_conv Let_def)
qed

lemma awalk_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awalk (ufa_rep_of uf y) (awalk_from_rep uf y) y"
proof -
  from assms have "awalk_from_rep_dom uf y"
    by (intro awalk_from_rep_domI in_Field_ufa_\<alpha>_if_in_verts)
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 y)
    then show ?case
    proof(cases "ufa_parent_of uf y = y")
      case True
      with 1 show ?thesis
        using awalk_from_rep_rep_of_if_in_verts rep_of_if_parent_of_refl
        by (simp add: awalk_Nil_iff)
    next
      case False
      with 1 have "awalk (ufa_rep_of uf y) (awalk_from_rep uf (ufa_parent_of uf y)) (ufa_parent_of uf y)"
        using ufa_parent_of_in_verts_if_in_verts
        by simp
      moreover have "awalk (ufa_parent_of uf y) [(ufa_parent_of uf y, y)] y"
        using "1" False awalk_parent_of by blast
      ultimately show ?thesis
        using 1 False by (simp add: awalk_from_rep.psimps Let_def)
    qed
  qed
qed

lemma unique_awalk_ufa_tree_of_rep:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "\<exists>!p. awalk (ufa_rep_of uf x) p y"
proof
  note in_Field_ufa_\<alpha>_if_in_verts[OF assms]
  with assms interpret y: ufa_tree where uf = uf and x = y
    by unfold_locales simp_all
  from assms have "ufa_rep_of uf y = ufa_rep_of uf x"
    by auto
  then show "awalk (ufa_rep_of uf x) (awalk_from_rep uf y) y"
    using assms y.awalk_awalk_from_rep
    using ufa_tree_of_eq_if_in_verts by force

  show "p = awalk_from_rep uf y" if "awalk (ufa_rep_of uf x) p y" for p
    using that \<open>ufa_rep_of uf y = ufa_rep_of uf x\<close> assms
  proof(induction p arbitrary: y rule: rev_induct)
    case Nil
    then show ?case
      using awalk_from_rep_rep_of
      by (fastforce simp: awalk_Nil_iff)
  next
    case (snoc a p)
    then have "awalk (ufa_rep_of uf x) p (fst a)" "a \<in> arcs (ufa_tree_of uf x)"
      by auto
    then have "a = (ufa_parent_of uf y, y)" "ufa_parent_of uf y \<noteq> y"
      unfolding ufa_tree_of_def using snoc.prems(1) by auto
    note snoc.IH[OF \<open>awalk (ufa_rep_of uf x) p (fst a)\<close>]
    with snoc.prems have "p = awalk_from_rep uf (ufa_parent_of uf y)"
      unfolding \<open>a = (ufa_parent_of uf y, y)\<close>
      by auto
    with \<open>a = (ufa_parent_of uf y, y)\<close> \<open>ufa_parent_of uf y \<noteq> y\<close> snoc.prems show ?case
      using awalk_from_rep_domI[OF in_Field_ufa_\<alpha>_if_in_verts]
      by (auto simp: awalk_from_rep.psimps[where ?x=y] Let_def)
  qed
qed


lemma eq_awalk_from_rep_if_awalk_rep_of:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  assumes "awalk (ufa_rep_of uf y) p y"
  shows "p = awalk_from_rep uf y"
  using assms awalk_awalk_from_rep unique_awalk_ufa_tree_of_rep
  by auto

sublocale fin_directed_tree "ufa_tree_of uf x" "ufa_rep_of uf x"
  using unique_awalk_ufa_tree_of_rep
  by unfold_locales (use verts_eq_eq_class_ufa_\<alpha> x_in_verts in \<open>force+\<close>)

lemma awalk_verts_from_rep_eq_awalk_verts:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "awalk_verts_from_rep uf y = awalk_verts (ufa_rep_of uf y) (awalk_from_rep uf y)"
proof -
  from assms have "awalk_from_rep_dom uf y"
    using in_Field_ufa_\<alpha>_if_in_verts by blast
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 y)
    let ?py = "ufa_parent_of uf y"
    show ?case
    proof(cases "?py = y")
      case True
      with 1 show ?thesis
        using awalk_from_rep_rep_of_if_in_verts rep_of_if_parent_of_refl
        by (auto simp: awalk_verts_from_rep.psimps)
    next
      case False
      from 1 have "ufa_rep_of uf ?py = ufa_rep_of uf y"
        by (simp add: in_Field_ufa_\<alpha>_if_in_verts)
      with 1 have "awalk (ufa_rep_of uf y) (awalk_from_rep uf ?py) ?py"
        using awalk_awalk_from_rep
        by (metis ufa_parent_of_in_verts_if_in_verts)
      note awalk_appendI[OF this awalk_parent_of]
      with 1 False have "awalk (ufa_rep_of uf y) (awalk_from_rep uf ?py @ [(?py, y)]) y"
        by blast
      note awalk_verts_append[OF this]
      moreover from 1 False have "awalk_verts_from_rep uf ?py
        = awalk_verts (ufa_rep_of uf y) (awalk_from_rep uf ?py)"
        using ufa_parent_of_in_verts_if_in_verts
        using \<open>ufa_rep_of uf ?py = ufa_rep_of uf y\<close> by simp
      ultimately show ?thesis
        using 1 False
        by (auto simp: Let_def awalk_verts_from_rep.psimps[where ?x=y] awalk_from_rep.psimps[where ?x=y])
    qed
  qed
qed

lemma awalk_verts_from_rep_eq_Cons:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  obtains py where "awalk_verts_from_rep uf y = ufa_rep_of uf y # py"
  using assms awalk_awalk_from_rep awalk_verts_from_rep_eq_awalk_verts 
  by (metis awalk_verts_non_Nil awhd_of_awalk list.collapse)

lemma awalk_and_parent_of_reflD:
  assumes "awalk z p y"
  assumes "ufa_parent_of uf y = y"
  shows "y = z" "p = []"
proof -
  from assms(1) have
    "z \<in> verts (ufa_tree_of uf x)" and
    y_in_verts: "y \<in> verts (ufa_tree_of uf x)"
    by blast+
  with \<open>ufa_parent_of uf y = y\<close> have "\<not> z \<rightarrow>\<^sup>+\<^bsub>ufa_tree_of uf x\<^esub> y" for z
    using x_in_verts not_root_if_dominated rep_of_if_parent_of_refl
    by (metis tranclD2)
  with assms have "z = ufa_rep_of uf y"
    using rep_of_if_parent_of_refl
    by (metis awalk_Nil_iff reachable1_awalk)
  moreover from \<open>awalk z p y\<close> have "z \<in> verts (ufa_tree_of uf x)"
    by blast
  moreover note awalk_awalk_from_rep[OF y_in_verts]
  moreover from \<open>ufa_parent_of uf y = y\<close> y_in_verts have "awalk_from_rep uf y = []"
    using awalk_from_rep_rep_of rep_of_if_parent_of_refl
    by blast
  moreover note eq_awalk_from_rep_if_awalk_rep_of[OF y_in_verts]
  moreover note in_ufa_\<alpha>_if_in_verts[OF y_in_verts]
  ultimately show "y = z" "p = []"
    using assms by (metis awalk_ends)+
qed

lemma awlast_butlast_eq_parent_of_if_awalk:
  assumes "awalk z p y"
  assumes "p \<noteq> []"
  shows "awlast z (butlast p) = ufa_parent_of uf y"
proof(cases "ufa_parent_of uf y = y")
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
  show "awlast z (butlast p) = ufa_parent_of uf y"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)
qed

lemma awalk_singletonD:
  assumes "awalk y [a] z"
  shows "y = ufa_parent_of uf z" "a = (ufa_parent_of uf z, z)"
proof -
  from assms have "ufa_parent_of uf z \<noteq> z"
    using awalk_and_parent_of_reflD(2) by blast
  with assms awalk_parent_of have
    "awalk (ufa_parent_of uf z) [(ufa_parent_of uf z, z)] z"
    by auto
  with assms unique_awalk_All show
    "y = ufa_parent_of uf z" "a = (ufa_parent_of uf z, z)"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)+
qed

lemma not_rep_if_in_tl_awalk_verts:
  assumes "awalk y p z"
  assumes "v \<in> set (tl (awalk_verts y p))"
  shows "ufa_parent_of uf v \<noteq> v"
  using assms
proof(induction p arbitrary: z v rule: rev_induct)
  case (snoc a as)   
  then show ?case
  proof(cases "v \<in> set (tl (awalk_verts y as))")
    case True
    from \<open>awalk y (as @ [a]) z\<close> have
      "awalk y as (ufa_parent_of uf (awlast y (as @ [a])))"
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
  assumes a_b_in_Field_\<alpha>: "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
begin

interpretation ufa_tree_union: ufa_tree where uf = "ufa_union uf a b" and x = x
  by unfold_locales simp

lemma in_verts_ufa_tree_of_union_if_in_verts[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of uf x)"
  shows "y \<in> verts (ufa_tree_of (ufa_union uf a b) x)"
  using assms a_b_in_Field_\<alpha> 
  unfolding ufa_tree_of_def by auto

lemma in_arcs_ufa_tree_of_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufa_tree_of uf x)"
  shows "e \<in> arcs (ufa_tree_of (ufa_union uf a b) x)"
  using assms a_b_in_Field_\<alpha>
  unfolding ufa_tree_of_def
  using FieldI2 ufa_parent_of_ufa_rep_of ufa_parent_of_ufa_union by force

lemma union_awalk_if_awalk:
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

lemma awalk_if_union_awalk:
  assumes "ufa_tree_union.awalk x p y"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "awalk x p y"
proof -
  from assms have
    "x \<in> Field (ufa_\<alpha> (ufa_union uf a b))"
    "y \<in> Field (ufa_\<alpha> (ufa_union uf a b))"
    by blast+
  with a_b_in_Field_\<alpha> have "y \<in> Field (ufa_\<alpha> uf)"
    by auto
  with assms have "y \<in> verts (ufa_tree_of uf x)"
    using in_verts_if_rep_of_eq by simp
    
  then have
    "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
    "awalk (ufa_rep_of uf y) (awalk_from_rep uf y) y"
    using awalk_awalk_from_rep assms by blast+
  with assms union_awalk_if_awalk ufa_tree_union.unique_awalk_All
  have "awalk (ufa_rep_of uf x) (awalk_from_rep uf x @ p) y"
    using ufa_tree_union.awalk_appendI by metis
  with \<open>awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x\<close> show "awalk x p y"
    by auto
qed

lemma awalk_from_rep_union:
  assumes "ufa_rep_of uf a \<noteq> ufa_rep_of uf b" "y \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_from_rep (ufa_union uf a b) y = 
    (if ufa_rep_of uf a = ufa_rep_of uf y then [(ufa_rep_of uf b, ufa_rep_of uf y)] else [])
    @ awalk_from_rep uf y"
proof -
  from a_b_in_Field_\<alpha> assms(2) have "awalk_from_rep_dom (ufa_union uf a b) y"
    by simp
  then show ?thesis
    using \<open>y \<in> Field (ufa_\<alpha> uf)\<close>
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 y)
    then show ?case
    proof(cases "ufa_parent_of uf y = y")
      case True
      with 1 a_b_in_Field_\<alpha> assms(1) show ?thesis
        using ufa_rep_of_if_refl_ufa_parent_of
        by (simp add: awalk_from_rep.psimps ufa_parent_of_ufa_union)
    next
      case False
      let ?py = "ufa_parent_of (ufa_union uf a b) y"
      from 1 False a_b_in_Field_\<alpha> have parent_of_union_y[simp]:
        "ufa_parent_of (ufa_union uf a b) y = ufa_parent_of uf y"
        by (metis ufa_parent_of_ufa_rep_of ufa_parent_of_ufa_union)
      from False "1.IH"[OF HOL.refl] have awalk_from_rep_py:
        "awalk_from_rep (ufa_union uf a b) ?py =
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

lemma awalk_verts_from_rep_union:
  assumes "ufa_rep_of uf a \<noteq> ufa_rep_of uf b" "y \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_verts_from_rep (ufa_union uf a b) y = 
    (if ufa_rep_of uf a = ufa_rep_of uf y then [ufa_rep_of uf b] else [])
    @ awalk_verts_from_rep uf y"
  using awalk_from_rep_union[OF assms] assms(2) a_b_in_Field_\<alpha>
  using awalk_verts_from_rep_eq_map_fst_awalk_from_rep
  by (simp add: in_Field_ufa_\<alpha>_if_in_verts)

end

end

end