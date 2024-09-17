theory UFA_Tree
  imports
    "Union_Find.Union_Find"
    "Tree_Theory.LCA_Directed_Tree"
begin

context
  fixes uf :: ufa
begin

definition "ufa_tree_of pivot \<equiv>
  let
    vs = ufa_\<alpha> uf `` {pivot}
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
  "verts (ufa_tree_of uf pivot) = ufa_\<alpha> uf `` {pivot}"
  unfolding ufa_tree_of_def by simp

lemma in_Field_ufa_\<alpha>_if_in_verts:
  "x \<in> verts (ufa_tree_of uf pivot) \<Longrightarrow> x \<in> Field (ufa_\<alpha> uf)"
  unfolding verts_eq_eq_class_ufa_\<alpha>
  by (simp add: FieldI2)

lemmas in_Field_ufa_\<alpha>_if_in_vertsE[elim] = in_Field_ufa_\<alpha>_if_in_verts[elim_format]

lemma in_vertsI:
  assumes "(pivot, x) \<in> ufa_\<alpha> uf"
  shows "x \<in> verts (ufa_tree_of uf pivot)"
  using assms unfolding verts_eq_eq_class_ufa_\<alpha> by blast

lemma ufa_tree_of_eq_if_in_verts:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "ufa_tree_of uf x = ufa_tree_of uf pivot"
proof -
  note part_equiv_ufa_\<alpha>
  then have "ufa_\<alpha> uf `` {x} = ufa_\<alpha> uf `` {pivot}"
    using assms unfolding verts_eq_eq_class_ufa_\<alpha>
    using part_equiv_sym part_equiv_trans by fast
  then show ?thesis
    unfolding ufa_tree_of_def Let_def
    by simp
qed
  
lemma in_ufa_\<alpha>_if_in_verts:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "(pivot, x) \<in> ufa_\<alpha> uf"
  using assms verts_eq_eq_class_ufa_\<alpha> by simp_all

lemma ufa_parent_of_in_verts_if_in_verts[simp, intro]:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "ufa_parent_of uf x \<in> verts (ufa_tree_of uf pivot)"
  using assms
  using ufa_parent_of_in_Field_ufa_\<alpha>I ufa_rep_of_eq_iff_in_ufa_\<alpha> ufa_rep_of_ufa_parent_of
  by (safe intro!: in_vertsI dest!: in_ufa_\<alpha>_if_in_verts) (metis FieldI1 FieldI2 )

lemma ufa_rep_of_eq_if_in_verts[simp]:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  assumes "NO_MATCH pivot x"
  shows "ufa_rep_of uf x = ufa_rep_of uf pivot"
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
  fixes uf pivot
  assumes pivot_in_Field_ufa_\<alpha>[simp, intro]: "pivot \<in> Field (ufa_\<alpha> uf)"
begin

sublocale fin_digraph "ufa_tree_of uf pivot"
proof(unfold_locales)
  from finite_ufa_eq_class show "finite (verts (ufa_tree_of uf pivot))"
    unfolding verts_eq_eq_class_ufa_\<alpha> ufa_eq_class_def by force
  then show "finite (arcs (ufa_tree_of uf pivot))"
    unfolding ufa_tree_of_def
    by (auto simp: Image_singleton)

  show "tail (ufa_tree_of uf pivot) e \<in> verts (ufa_tree_of uf pivot)"
    if "e \<in> arcs (ufa_tree_of uf pivot)" for e
    using that part_equiv_trans[OF part_equiv_ufa_\<alpha> _ _]
    using ufa_parent_of_in_verts_if_in_verts
    unfolding ufa_tree_of_def by auto
qed (auto simp: ufa_tree_of_def)

lemma pivot_in_verts[simp, intro]: "pivot \<in> verts (ufa_tree_of uf pivot)"
  using in_vertsI ufa_\<alpha>I by blast

lemma in_verts_if_ufa_rep_of_eq:
  assumes "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of uf y = ufa_rep_of uf pivot"
  shows "y \<in> verts (ufa_tree_of uf pivot)"
  using assms
  by (intro in_vertsI ufa_\<alpha>I) simp_all

lemma ufa_tree_of_ufa_parent_of[simp]:
  "ufa_tree_of uf (ufa_parent_of uf pivot) = ufa_tree_of uf pivot"
  using ufa_tree_of_eq_if_in_verts ufa_parent_of_in_verts_if_in_verts
  by blast

lemma ufa_tree_of_ufa_rep_of[simp]:
  "ufa_tree_of uf (ufa_rep_of uf pivot) = ufa_tree_of uf pivot"
  using ufa_rep_of_ufa_rep_of  
  by (intro ufa_tree_of_eq_if_in_verts in_vertsI ufa_\<alpha>I) auto

lemma awalk_ufa_parent_of:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  assumes "ufa_parent_of uf x \<noteq> x"
  shows "awalk (ufa_parent_of uf x) [(ufa_parent_of uf x, x)] x"
  using assms arc_implies_awalk
  unfolding ufa_tree_of_def by auto

lemma awalk_from_rep_ufa_rep_of_if_in_verts:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "awalk_from_rep uf (ufa_rep_of uf x) = []"
  using assms awalk_from_rep_rep_of by blast

lemma ufa_rep_of_if_ufa_parent_of_refl:
  assumes "x \<in> verts (ufa_tree_of uf pivot)" "y \<in> verts (ufa_tree_of uf pivot)"
  assumes "ufa_parent_of uf x = x"
  shows "ufa_rep_of uf y = x"
  using assms ufa_rep_of_if_refl_ufa_parent_of by fastforce
                        
lemma awlast_awalk_from_rep:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "awlast (ufa_rep_of uf x) (awalk_from_rep uf x) = x"
proof -
  from assms have "awalk_from_rep_dom uf x"
    by (intro awalk_from_rep_domI in_Field_ufa_\<alpha>_if_in_verts)
  then show ?thesis
    using assms ufa_rep_of_if_ufa_parent_of_refl[OF _ pivot_in_verts]
    by (induction rule: awalk_from_rep.pinduct)
      (auto simp: awalk_from_rep.psimps pre_digraph.awalk_verts_conv Let_def)
qed

lemma awalk_awalk_from_rep:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
proof -
  from assms have "awalk_from_rep_dom uf x"
    by (intro awalk_from_rep_domI in_Field_ufa_\<alpha>_if_in_verts)
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 x)
    then show ?case
    proof(cases "ufa_parent_of uf x = x")
      case True
      with 1 show ?thesis
        using awalk_from_rep_ufa_rep_of_if_in_verts ufa_rep_of_if_ufa_parent_of_refl
        by (simp add: awalk_Nil_iff)
    next
      case False
      with 1 have
        "awalk (ufa_rep_of uf x) (awalk_from_rep uf (ufa_parent_of uf x)) (ufa_parent_of uf x)"
        using ufa_parent_of_in_verts_if_in_verts
        by simp
      moreover have "awalk (ufa_parent_of uf x) [(ufa_parent_of uf x, x)] x"
        using "1" False awalk_ufa_parent_of by blast
      ultimately show ?thesis
        using 1 False by (simp add: awalk_from_rep.psimps Let_def)
    qed
  qed
qed

lemma unique_awalk_ufa_tree_of_ufa_rep_of:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "\<exists>!p. awalk (ufa_rep_of uf x) p x"
proof
  note in_Field_ufa_\<alpha>_if_in_verts[OF assms]
  with assms interpret ufa_tree_x: ufa_tree where uf = uf and pivot = x
    by unfold_locales simp_all
  from assms have "ufa_rep_of uf x = ufa_rep_of uf pivot"
    by auto
  then show "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
    using assms ufa_tree_x.awalk_awalk_from_rep
    using ufa_tree_of_eq_if_in_verts by force

  show "p = awalk_from_rep uf x" if "awalk (ufa_rep_of uf x) p x" for p
    using that \<open>ufa_rep_of uf x = ufa_rep_of uf pivot\<close> assms
  proof(induction p arbitrary: x rule: rev_induct)
    case Nil
    then show ?case
      using awalk_from_rep_rep_of
      by (fastforce simp: awalk_Nil_iff)
  next
    case (snoc a p)
    then have "awalk (ufa_rep_of uf (fst a)) p (fst a)" "a \<in> arcs (ufa_tree_of uf pivot)"
      by auto
    then have "a = (ufa_parent_of uf x, x)" "ufa_parent_of uf x \<noteq> x"
      unfolding ufa_tree_of_def using snoc.prems(1) by auto
    note snoc.IH[OF \<open>awalk (ufa_rep_of uf (fst a)) p (fst a)\<close>]
    with snoc.prems have "p = awalk_from_rep uf (ufa_parent_of uf x)"
      unfolding \<open>a = (ufa_parent_of uf x, x)\<close>
      by auto
    with \<open>a = (ufa_parent_of uf x, x)\<close> \<open>ufa_parent_of uf x \<noteq> x\<close> snoc.prems show ?case
      using awalk_from_rep_domI[OF in_Field_ufa_\<alpha>_if_in_verts]
      by (auto simp: awalk_from_rep.psimps[where ?x=x] Let_def)
  qed
qed

lemma eq_awalk_from_rep_if_awalk_ufa_rep_of:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  assumes "awalk (ufa_rep_of uf x) p x"
  shows "p = awalk_from_rep uf x"
  using assms awalk_awalk_from_rep unique_awalk_ufa_tree_of_ufa_rep_of
  by auto

sublocale fin_directed_tree "ufa_tree_of uf pivot" "ufa_rep_of uf pivot"
  using unique_awalk_ufa_tree_of_ufa_rep_of
  by unfold_locales (use verts_eq_eq_class_ufa_\<alpha> pivot_in_verts in \<open>force+\<close>)

lemma awalk_verts_from_rep_eq_awalk_verts:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "awalk_verts_from_rep uf x = awalk_verts (ufa_rep_of uf x) (awalk_from_rep uf x)"
proof -
  from assms have "awalk_from_rep_dom uf x"
    using in_Field_ufa_\<alpha>_if_in_verts by blast
  then show ?thesis
    using assms
  proof(induction rule: awalk_from_rep.pinduct)
    case (1 x)
    let ?px = "ufa_parent_of uf x"
    show ?case
    proof(cases "?px = x")
      case True
      with 1 show ?thesis
        using awalk_from_rep_ufa_rep_of_if_in_verts ufa_rep_of_if_ufa_parent_of_refl
        by (auto simp: awalk_verts_from_rep.psimps)
    next
      case False
      from 1 have "ufa_rep_of uf ?px = ufa_rep_of uf x"
        by (simp add: in_Field_ufa_\<alpha>_if_in_verts)
      with 1 have "awalk (ufa_rep_of uf x) (awalk_from_rep uf ?px) ?px"
        using awalk_awalk_from_rep
        by (metis ufa_parent_of_in_verts_if_in_verts)
      note awalk_appendI[OF this awalk_ufa_parent_of]
      with 1 False have "awalk (ufa_rep_of uf x) (awalk_from_rep uf ?px @ [(?px, x)]) x"
        by blast
      note awalk_verts_append[OF this]
      moreover from 1 False have "awalk_verts_from_rep uf ?px
        = awalk_verts (ufa_rep_of uf x) (awalk_from_rep uf ?px)"
        using ufa_parent_of_in_verts_if_in_verts
        using \<open>ufa_rep_of uf ?px = ufa_rep_of uf x\<close> by simp
      ultimately show ?thesis
        using 1 False
        by (auto simp: Let_def awalk_verts_from_rep.psimps[where ?x=x] awalk_from_rep.psimps[where ?x=x])
    qed
  qed
qed

lemma awalk_verts_from_rep_eq_Cons:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  obtains px where "awalk_verts_from_rep uf x = ufa_rep_of uf x # px"
  using assms awalk_awalk_from_rep awalk_verts_from_rep_eq_awalk_verts 
  by (metis awalk_verts_non_Nil awhd_of_awalk list.collapse)

lemma awalk_and_ufa_parent_of_reflD:
  assumes "awalk y p x"
  assumes "ufa_parent_of uf x = x"
  shows "x = y" "p = []"
proof -
  from assms(1) have
    "y \<in> verts (ufa_tree_of uf pivot)" and
    x_in_verts: "x \<in> verts (ufa_tree_of uf pivot)"
    by blast+
  with \<open>ufa_parent_of uf x = x\<close> have "\<not> z \<rightarrow>\<^sup>+\<^bsub>ufa_tree_of uf pivot\<^esub> x" for z
    using pivot_in_verts not_root_if_dominated ufa_rep_of_if_ufa_parent_of_refl
    by (metis tranclD2)
  with assms have "y = ufa_rep_of uf x"
    using ufa_rep_of_if_ufa_parent_of_refl
    by (metis awalk_Nil_iff reachable1_awalk)
  moreover from \<open>awalk y p x\<close> have "y \<in> verts (ufa_tree_of uf pivot)"
    by blast
  moreover note awalk_awalk_from_rep[OF pivot_in_verts]
  moreover from \<open>ufa_parent_of uf x = x\<close> x_in_verts have "awalk_from_rep uf x = []"
    using awalk_from_rep_rep_of ufa_rep_of_if_ufa_parent_of_refl
    by blast
  moreover note eq_awalk_from_rep_if_awalk_ufa_rep_of[OF x_in_verts]
  moreover note in_ufa_\<alpha>_if_in_verts[OF x_in_verts]
  ultimately show "x = y" "p = []"
    using assms by (metis awalk_ends)+
qed

lemma awlast_butlast_eq_ufa_parent_of_if_awalk:
  assumes "awalk y p x"
  assumes "p \<noteq> []"
  shows "awlast y (butlast p) = ufa_parent_of uf x"
proof(cases "ufa_parent_of uf x = x")
  case True
  with assms awalk_and_ufa_parent_of_reflD show ?thesis
    by simp
next
  case False
  from assms have "p = butlast p @ [last p]"
    by simp
  with assms have "awalk (awlast y (butlast p)) [last p] x"
    using awalk_not_Nil_butlastD by blast
  from assms have "x \<in> verts (ufa_tree_of uf pivot)"
    by blast
  with awalk_ufa_parent_of[OF this False] \<open>awalk (awlast y (butlast p)) [last p] x\<close>
  show "awlast y (butlast p) = ufa_parent_of uf x"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)
qed

lemma awalk_singletonD:
  assumes "awalk x [a] y"
  shows "x = ufa_parent_of uf y" "a = (ufa_parent_of uf y, y)"
proof -
  from assms have "ufa_parent_of uf y \<noteq> y"
    using awalk_and_ufa_parent_of_reflD(2) by blast
  with assms awalk_ufa_parent_of have
    "awalk (ufa_parent_of uf y) [(ufa_parent_of uf y, y)] y"
    by auto
  with assms unique_awalk_All show
    "x = ufa_parent_of uf y" "a = (ufa_parent_of uf y, y)"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)+
qed

lemma not_rep_if_in_tl_awalk_verts:
  assumes "awalk x p y"
  assumes "v \<in> set (tl (awalk_verts x p))"
  shows "ufa_parent_of uf v \<noteq> v"
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
    moreover from snoc.prems False have "v = head (ufa_tree_of uf pivot) a"
      using awalk_verts_append[OF \<open>awalk x (as @ [a]) y\<close>]
      by (cases a) auto
    with snoc.prems False have "y = v"
      by auto
    ultimately show ?thesis
      using awalk_and_ufa_parent_of_reflD(2) by blast
  qed
qed simp

context
  fixes a b
  assumes a_b_in_Field_\<alpha>: "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
begin

interpretation ufa_tree_union: ufa_tree where uf = "ufa_union uf a b" and pivot = pivot
  by unfold_locales simp

lemma in_verts_ufa_tree_of_ufa_union_if_in_verts[simp, intro]:
  assumes "x \<in> verts (ufa_tree_of uf pivot)"
  shows "x \<in> verts (ufa_tree_of (ufa_union uf a b) pivot)"
  using assms a_b_in_Field_\<alpha> 
  unfolding ufa_tree_of_def by auto

lemma in_arcs_ufa_tree_of_ufa_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufa_tree_of uf pivot)"
  shows "e \<in> arcs (ufa_tree_of (ufa_union uf a b) pivot)"
  using assms a_b_in_Field_\<alpha>
  unfolding ufa_tree_of_def
  using FieldI2 ufa_parent_of_ufa_rep_of ufa_parent_of_ufa_union by force

lemma ufa_union_awalk_if_awalk:
  assumes "awalk x p y"
  shows "ufa_tree_union.awalk x p y"
  using assms
proof(induction p arbitrary: x)
  case Nil
  then show ?case
    unfolding awalk_Nil_iff ufa_tree_union.awalk_Nil_iff
    using in_verts_ufa_tree_of_ufa_union_if_in_verts
    by blast
next
  case (Cons a p)
  then show ?case
    unfolding awalk_Cons_iff ufa_tree_union.awalk_Cons_iff
    using in_arcs_ufa_tree_of_ufa_union_if_in_arcs
    by simp
qed

lemma awalk_if_ufa_union_awalk:
  assumes "ufa_tree_union.awalk pivot p x"
  assumes "ufa_rep_of uf pivot = ufa_rep_of uf x"
  shows "awalk pivot p x"
proof -
  from assms have
    "pivot \<in> Field (ufa_\<alpha> (ufa_union uf a b))"
    "x \<in> Field (ufa_\<alpha> (ufa_union uf a b))"
    by blast+
  with a_b_in_Field_\<alpha> have "x \<in> Field (ufa_\<alpha> uf)"
    by auto
  with assms have "x \<in> verts (ufa_tree_of uf pivot)"
    using in_verts_if_ufa_rep_of_eq by simp
    
  then have
    "awalk (ufa_rep_of uf pivot) (awalk_from_rep uf pivot) pivot"
    "awalk (ufa_rep_of uf x) (awalk_from_rep uf x) x"
    using awalk_awalk_from_rep assms by blast+
  with assms ufa_union_awalk_if_awalk ufa_tree_union.unique_awalk_All
  have "awalk (ufa_rep_of uf pivot) (awalk_from_rep uf pivot @ p) x"
    using ufa_tree_union.awalk_appendI by metis
  with \<open>awalk (ufa_rep_of uf pivot) (awalk_from_rep uf pivot) pivot\<close> show "awalk pivot p x"
    by auto
qed

lemma awalk_from_rep_ufa_union:
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
      let ?px = "ufa_parent_of (ufa_union uf a b) y"
      from 1 False a_b_in_Field_\<alpha> have parent_of_union_y[simp]:
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
  assumes "ufa_rep_of uf a \<noteq> ufa_rep_of uf b" "y \<in> Field (ufa_\<alpha> uf)"
  shows "awalk_verts_from_rep (ufa_union uf a b) y = 
    (if ufa_rep_of uf a = ufa_rep_of uf y then [ufa_rep_of uf b] else [])
    @ awalk_verts_from_rep uf y"
  using awalk_from_rep_ufa_union[OF assms] assms(2) a_b_in_Field_\<alpha>
  using awalk_verts_from_rep_eq_map_fst_awalk_from_rep
  by (simp add: in_Field_ufa_\<alpha>_if_in_verts)

end

end

end
