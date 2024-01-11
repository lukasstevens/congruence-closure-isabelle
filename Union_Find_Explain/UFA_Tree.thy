theory UFA_Tree
  imports
    UF_ADT
    Map_ADT
    "Separation_Logic_Imperative_HOL.Union_Find"
    "Tree_Theory.LCA_Directed_Tree"
begin

context union_find_parent
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
  apply(rule ufa_tree_of_eq_if_in_verts)
  sorry


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
  from in_verts_ufa_tree_ofD[OF assms] have "uf_rep_of uf y = uf_rep_of uf x"
    using x_in_Field_\<alpha> apply(auto simp: FieldI2)
    by (metis FieldI2 \<alpha>_rep_of x_in_Field_\<alpha>)
  then show ?thesis
    by (smt (verit, best) FieldI1 awalk_from_rep_domI in_verts_ufa_tree_ofD invar_uf
        parent_of_refl_iff_rep_of_refl
        ufa_tree_of_rep_of union_find.\<alpha>_rep_of
        union_find_axioms
        union_find_parent.awalk_from_rep.psimps
        union_find_parent_axioms
        x_in_verts)
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

context union_find
begin

abbreviation "uf_unions \<equiv> foldl (\<lambda>uf (x, y). uf_union uf x y)"

definition "valid_unions uf us \<equiv> \<forall>(x, y) \<in> set us. x \<in> Field (uf_\<alpha> uf) \<and> y \<in> Field (uf_\<alpha> uf)"

lemma valid_unions_Nil[simp]:
  "valid_unions uf []"
  unfolding valid_unions_def by simp

lemma valid_unions_Cons[simp]:
  "valid_unions uf (x # xs) \<longleftrightarrow>
  fst x \<in> Field (uf_\<alpha> uf) \<and> snd x \<in> Field (uf_\<alpha> uf) \<and> valid_unions uf xs"
  unfolding valid_unions_def by (simp split: prod.splits)

lemma valid_unions_append[simp]:
  "valid_unions uf (xs @ ys) \<longleftrightarrow> valid_unions uf xs \<and> valid_unions uf ys"
  unfolding valid_unions_def by auto

lemma valid_unions_takeI[simp, intro]:
  "valid_unions uf us \<Longrightarrow> valid_unions uf (take i us)"
  unfolding valid_unions_def using in_set_takeD by fast

end

context union_find_invar
begin

lemma Field_\<alpha>_unions[simp]:
  assumes "valid_unions uf us"
  shows "Field (uf_\<alpha> (uf_unions uf us)) = Field (uf_\<alpha> uf)"
  using assms invar_uf
proof(induction us arbitrary: uf)
  case (Cons u us)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from Cons show ?case
    by (cases u) (auto simp: valid_unions_def)
qed simp

lemma valid_unions_uf_unions[simp]:
  assumes "valid_unions uf us"
  shows "valid_unions (uf_unions uf us) ous = valid_unions uf ous"
  using Field_\<alpha>_unions[OF assms] unfolding valid_unions_def by simp

lemma valid_union_union[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "valid_unions (uf_union uf x y) us \<longleftrightarrow> valid_unions uf us"
  using assms valid_unions_uf_unions[where ?us="[(x, y)]"]
  by simp

lemma valid_unions_nthD[simp, dest]:
  assumes "valid_unions uf us" "i < length us"
  shows "fst (us ! i) \<in> Field (uf_\<alpha> uf)" "snd (us ! i) \<in> Field (uf_\<alpha> uf)"
  using assms unfolding valid_unions_def
  using nth_mem by fastforce+

lemma valid_unions_nth_eq_pairD:
  assumes "valid_unions uf us" "i < length us"
  assumes "us ! i = (a, b)"
  shows "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  using assms valid_unions_nthD by force+

lemma uf_invar_uf_unions[simp, intro]:
  assumes "valid_unions uf us"
  shows "uf_invar (uf_unions uf us)"
  using assms invar_uf
proof(induction us arbitrary: uf)
  case (Cons u us)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from Cons show ?case
    by (cases u) (auto intro!: Cons.IH)
qed simp

lemma rep_of_neq_if_rep_of_ufa_union_neq:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  assumes "j \<in> Field (uf_\<alpha> uf)" "k \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_union uf x y) j \<noteq> uf_rep_of (uf_union uf x y) k"
  shows "uf_rep_of uf j \<noteq> uf_rep_of uf k"
  using assms
proof -
  from assms interpret uf_union: union_find_invar where uf = "uf_union uf x y"
    by unfold_locales auto
  from assms show ?thesis
    by (auto simp: \<alpha>_rep_of uf_union.\<alpha>_rep_of)
qed  

lemma rep_of_uf_unions_take_neq_if_rep_of_uf_unions_neq:
  assumes "valid_unions uf us"
  assumes "j \<in> Field (uf_\<alpha> uf)" "k \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_unions uf us) j \<noteq> uf_rep_of (uf_unions uf us) k"
  shows "uf_rep_of (uf_unions uf (take i us)) j \<noteq> uf_rep_of (uf_unions uf (take i us)) k"
  using assms
proof(induction us arbitrary: i rule: rev_induct)
  case (snoc u us)
  from snoc interpret uf_unions: union_find_invar where uf = "uf_unions uf us"
    by unfold_locales auto
  from snoc have rep_of_ufa_union:
    "uf_rep_of (uf_union (uf_unions uf us) (fst u) (snd u)) j
    \<noteq> uf_rep_of (uf_union (uf_unions uf us) (fst u) (snd u)) k"
    by (cases u) simp
  note uf_unions.rep_of_neq_if_rep_of_ufa_union_neq[OF _ _ _  _ this]
  with snoc.prems have "uf_rep_of (uf_unions uf us) j \<noteq> uf_rep_of (uf_unions uf us) k"
    by auto
  note snoc.IH[OF _ snoc.prems(2,3) this]
  with snoc.prems(1) rep_of_ufa_union show ?case
    by (cases "i \<le> length us") (auto split: prod.splits)
qed simp

end

locale union_find_explain =
  union_find_parent where uf_ty = uf_ty and dom_ty = dom_ty +
  map_mono where
    mm_adt = au_adt and invar = invar_au and \<alpha> = \<alpha>_au and
    m_ty = au_ty and dom_ty = dom_ty and ran_ty = ran_ty 
  for au_adt invar_au \<alpha>_au and
    uf_ty :: "'uf itself" and
    au_ty :: "'au itself" and dom_ty :: "'dom itself" and ran_ty :: "nat itself"

locale union_find_explain_invars = union_find_explain +
  fixes uf
  fixes unions
  fixes au

  assumes valid_unions: "valid_unions uf_init unions"
  assumes eq_uf_unions:
    "uf = uf_unions uf_init unions"
  assumes valid_au:
    "mm_lookup\<^bsub>au_adt\<^esub> au x = Some i \<Longrightarrow> i < length unions"
  assumes inj_on_dom_au:
    "inj_on (mm_lookup\<^bsub>au_adt\<^esub> au) (dom (mm_lookup\<^bsub>au_adt\<^esub> au))"
  assumes lookup_au_if_not_rep:
    "y \<in> Field (uf_\<alpha> uf) \<Longrightarrow> uf_rep_of uf y \<noteq> y \<Longrightarrow> mm_lookup\<^bsub>au_adt\<^esub> au y \<noteq> None"
  assumes rep_of_before_au:
    "\<lbrakk> mm_lookup\<^bsub>au_adt\<^esub> au x = Some i; unions ! i = (j, k)
     ; before = uf_unions uf_init (take i unions) \<rbrakk>
     \<Longrightarrow> uf_rep_of before j \<noteq> uf_rep_of before k"
begin

sublocale uf_invar_init: union_find_invar where uf = uf_init
  using invar_init by unfold_locales assumption+

lemma valid_unions_uf:
  "valid_unions uf unions"
  using valid_unions by (simp add: eq_uf_unions)

sublocale union_find_invar where uf = uf
  using eq_uf_unions valid_unions by unfold_locales blast


lemma rep_of_after_au:
  assumes "mm_lookup\<^bsub>au_adt\<^esub> au x = Some i" "unions ! i = (j, k)"
  assumes "i' > i"
  assumes "after = uf_unions uf_init (take i' unions)"
  shows "uf_rep_of after j = uf_rep_of after k"
  using assms
proof(induction "i' - Suc i" arbitrary: i' after)
  case 0
  then have "i' = Suc i"
    by simp
  with 0 valid_au have take_i'_unions_eq:
    "take i' unions = take (i' - 1) unions @ [(j, k)]"
    by (metis diff_Suc_1 take_Suc_conv_app_nth)

  from assms valid_unions valid_au have j_k_in_Field_uf_\<alpha>:
    "j \<in> Field (uf_\<alpha> (uf_unions uf_init (take (i' - 1) unions)))"
    "k \<in> Field (uf_\<alpha> (uf_unions uf_init (take (i' - 1) unions)))"
    by fastforce+
  from ufa_init_invar have "uf_invar (uf_unions uf_init (take (i' - 1) unions))"
    using valid_unions by fastforce
  then interpret before: union_find_invar where
    uf = "uf_unions uf_init (take (i' - 1) unions)"
    by unfold_locales simp

  from valid_unions have valid_unions_after:
    "valid_unions uf_init (take i' unions)"
    by blast
  with 0 interpret after: union_find_invar where uf = after
    by unfold_locales blast

  note before.\<alpha>_union in_per_unionI[OF before.part_equiv_\<alpha>]
  note this[OF j_k_in_Field_uf_\<alpha>]
  with 0 valid_au valid_unions show ?case
    unfolding take_i'_unions_eq
    by (subst after.\<alpha>_rep_of) force+
next
  case (Suc i'')
  then have "i'' = (i' - 1) - Suc i" "i < i' - 1"
    by simp_all
  note IH = "Suc.hyps"(1)[OF this(1) Suc.prems(1,2) this(2) HOL.refl]
  then show ?case
  proof(cases "i' < Suc (length unions)")
    case False
    then have "take i' unions = unions"
      by simp
    moreover from False have "take (i' - 1) unions = unions"
      by simp
    ultimately show ?thesis
      using IH Suc.prems(4) by simp
  next
    case True
    with Suc have "i' - 1 < length unions" "Suc (i' - 1) = i'"
      by linarith+
    note take_Suc_conv_app_nth[OF this(1), unfolded this(2)]
    then have uf_unions_eq: "uf_unions uf_init (take i' unions) =
      uf_union (uf_unions uf_init (take (i' - 1) unions))
        (fst (unions ! (i' - 1))) (snd (unions ! (i' - 1)))" (is "_ = uf_union ?uf' ?a ?b")
      by (simp split: prod.split)

    have "uf_invar ?uf'"
      using ufa_init_invar uf_invar_init.uf_invar_uf_unions valid_unions
      by force
    with valid_unions interpret before: union_find_invar where
      uf = ?uf'
      by unfold_locales simp
    have a_b_in_Field_\<alpha>: "?a \<in> Field (uf_\<alpha> ?uf')" "?b \<in> Field (uf_\<alpha> ?uf')"
      using \<open>i' - 1 < length unions\<close>
      using uf_invar_init.Field_\<alpha>_unions valid_unions by blast+
    have "j \<in> Field (uf_\<alpha> ?uf')" "k \<in> Field (uf_\<alpha> ?uf')"
      using assms valid_au valid_unions by force+

    with IH a_b_in_Field_\<alpha> show ?thesis
      unfolding Suc.prems(4) uf_unions_eq
      using before.rep_of_neq_if_rep_of_ufa_union_neq by blast
  qed
qed

lemma rep_of_au:
  assumes "mm_lookup\<^bsub>au_adt\<^esub> au x = Some i" "unions ! i = (j, k)"
  shows "uf_rep_of uf j = uf_rep_of uf k"
proof -
  note eq_uf_unions
  then have "uf = uf_unions uf_init (take (length unions) unions)"
    by simp
  note rep_of_after_au[OF assms _  this]
  with assms valid_au show ?thesis
    by blast
qed

lemma rep_of_before_au':
  assumes "mm_lookup\<^bsub>au_adt\<^esub> au x = Some i" "unions ! i = (j, k)"
  assumes "i' \<le> i"
  assumes "before = uf_unions uf_init (take i' unions)"
  shows "uf_rep_of before j \<noteq> uf_rep_of before k"
  using assms
proof -
  from \<open>i' \<le> i\<close> obtain i'' where take_i''_i:
    "take i'' (take i unions) = take i' unions"
    by (metis min.orderE take_take)
        
  note rep_of_before_au[OF assms(1,2) HOL.refl]
  note uf_invar_init.rep_of_uf_unions_take_neq_if_rep_of_uf_unions_neq[OF _ _ _ this]
  note this[where ?i=i'', unfolded take_i''_i]
  with assms(1,2,4) show ?thesis
    using ufa_init_invar valid_au valid_unions
    by fastforce
qed
  
(*
lemma ufe_invars_union:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of uf x \<noteq> uf_rep_of uf y"
  defines "uf' \<equiv> uf_union uf x y"
  shows "ufe_invars uf' (unions @ [(x, y)]) (au[uf_rep_of uf x := length unions])"
proof -
  from distinct_au valid_au have distinct_au_upd:
    "distinct (au[i := length unions])" for i
  proof(induction au arbitrary: i)
    case (Cons a au)
    then have "distinct (au[i := length unions])" for i
      by simp
    with "Cons.prems" show ?case
      by (cases "a \<ge> 0")
        (auto simp: comp_def elim!: in_set_upd_cases split: nat.splits)
  qed simp
  from nth_au_nonneg_if_not_rep length_au have nth_au_nonneg:
    "au[uf_rep_of uf x := length unions] ! y \<ge> 0"
    if "y < length l'" "l' ! y \<noteq> y" for y
    using that unfolding l'_def
    by (auto simp: nth_list_update')
  note axioms = ufe_invars_axioms[unfolded ufe_invars_def ufe_invars_axioms_def]
  with assms distinct_au_upd nth_au_nonneg show ?thesis
    by (unfold_locales)
      (fastforce simp: less_Suc_eq elim!: in_set_upd_cases)+
qed *)
    
end

locale ufe_tree = union_find_explain_invars +
  fixes x
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (uf_\<alpha> uf)"
      and finite_eq_class: "\<And>y. finite (uf_\<alpha> uf `` {y})"
begin

sublocale ufa_tree where uf = uf and x = x
  using invar_uf finite_eq_class
  by unfold_locales blast+

definition "newest_on_walk newest y p z \<equiv>
  awalk y p z \<and> newest = Max (Option.these (mm_lookup\<^bsub>au_adt\<^esub> au ` set (tl (awalk_verts y p))))"

lemma newest_on_walk_awalkD[simp]:
  assumes "newest_on_walk newest y p z"
  shows "awalk y p z"
  using assms unfolding newest_on_walk_def by simp

lemma Not_is_none_lookup_if_in_tl_awalk_verts:
  assumes "awalk y p z"
  assumes "y \<noteq> z"
  assumes "i \<in> set (tl (awalk_verts y p))"
  shows "\<not> Option.is_none (mm_lookup\<^bsub>au_adt\<^esub> au i)"
  using assms
proof -
  from assms have "i \<in> verts (ufa_tree_of uf x)"
    using awalk_verts_in_verts
    by (meson awalkE' list.set_sel(2) pre_digraph.awalk_verts_non_Nil)
  then have "i \<in> Field (uf_\<alpha> uf)"
    using verts_ufa_tree_of by blast
  moreover from assms \<open>i \<in> Field (uf_\<alpha> uf)\<close> have "uf_rep_of uf i \<noteq> i"
    using not_rep_if_in_tl_awalk_verts parent_of_refl_iff_rep_of_refl by blast
  ultimately show ?thesis
    using lookup_au_if_not_rep
    by (simp add: Option.is_none_def)
qed

lemma newest_on_walkE:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z"
  obtains i where
    "awalk y p z" "i \<in> set (tl (awalk_verts y p))"
    "newest = the (mm_lookup\<^bsub>au_adt\<^esub> au i)"
    "\<forall>i' \<in> set (tl (awalk_verts y p)).
      the (mm_lookup\<^bsub>au_adt\<^esub> au i') \<le> the (mm_lookup\<^bsub>au_adt\<^esub> au i)"
proof -
  from assms have "set (tl (awalk_verts y p)) \<noteq> {}"
    unfolding newest_on_walk_def
    by (cases p) auto
  then obtain i where i:
    "i \<in> set (tl (awalk_verts y p))"
    "newest = the (mm_lookup\<^bsub>au_adt\<^esub> au i)"
    "\<forall>i' \<in> set (tl (awalk_verts y p)).
      the (mm_lookup\<^bsub>au_adt\<^esub> au i') \<le> the (mm_lookup\<^bsub>au_adt\<^esub> au i)"
    using assms unfolding newest_on_walk_def
    by (metis (mono_tags, opaque_lifting) awalkE'
        awalk_and_parent_of_reflD(1)
        in_Field_\<alpha>_if_in_verts
        in_hd_or_tl_conv
        lookup_au_if_not_rep option.sel
        parent_of_refl_iff_rep_of_refl
        order.refl list.set(1)
        )
  with i that show ?thesis
    using assms unfolding newest_on_walk_def by blast
qed

lemma newest_on_walk_in_bounds:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z"
  shows "newest < length unions"
proof -
  from newest_on_walkE[OF assms] obtain i where i:
    "awalk y p z"
    "i \<in> set (tl (awalk_verts y p))"
    "newest = the (mm_lookup\<^bsub>au_adt\<^esub> au i)"
    by blast
  then have "i \<in> verts (ufa_tree_of uf x)"
    by (meson awalk_decomp awalk_hd_in_verts in_set_tlD)

  with i valid_au show "newest < length unions"
    using lookup_au_if_not_rep in_Field_\<alpha>_if_in_verts
    by (meson not_rep_if_in_tl_awalk_verts parent_of_refl_iff_rep_of_refl)
qed

lemma newest_on_walk_valid_union:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z"
  assumes "unions ! newest = (a, b)"
  shows "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  using newest_on_walk_in_bounds[OF assms(1,2)] assms(3)
  using valid_unions_nth_eq_pairD[OF valid_unions_uf]
  by blast+

end

end