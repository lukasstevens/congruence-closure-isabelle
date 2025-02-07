theory UFE_Forest
  imports Explain_Simple Explain_Efficient
begin
             
lemma lookup_au_ds_lt_length_unions:
  "au_ds ufe_ds x = Some i \<Longrightarrow> i < length (unions ufe_ds)"
proof(induction ufe_ds arbitrary: x i rule: ufe_induct)
  case (ufe_union ufe a b x)
  then show ?case
    by (simp add: less_Suc_eq split: if_splits)
qed simp

lemma dom_au_ds_subs_Field_ufa_\<alpha>:
  "dom (au_ds ufe_ds) \<subseteq> Field (ufe_\<alpha> ufe_ds)"
proof(induction ufe_ds rule: ufe_induct)
  case (ufe_union ufe a b)
  then show ?case
    by (simp add: domIff subset_iff)
qed simp

lemma ufe_rep_of_eq_if_au:
  assumes "au_ds ufe_ds x = Some i"
  assumes "unions ufe_ds ! i = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
proof -
  have
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x \<and>
    ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    using assms
  proof(induction ufe_ds arbitrary: i a b rule: ufe_induct)
    case (ufe_union ufe_ds y z)

    from ufe_union.prems have "(a, b) \<in> set (unions (ufe_union ufe_ds y z))"
      by (metis lookup_au_ds_lt_length_unions nth_mem)
    with ufe_union.hyps have
      a_in_Field_\<alpha>: "a \<in> Field (ufe_\<alpha> ufe_ds)" and
      b_in_Field_\<alpha>: "b \<in> Field (ufe_\<alpha> ufe_ds)"
      using Field_unions_subs_Field_ufe_\<alpha>
      by (auto intro: FieldI1 FieldI2)
    from ufe_union have x_in_Field_\<alpha>: "x \<in> Field (ufe_\<alpha> ufe_ds)"
      using dom_au_ds_subs_Field_ufa_\<alpha> Field_ufe_\<alpha>_ufe_union_eq
      by blast

    show ?case
    proof(cases "i < length (unions ufe_ds)")
      case False

      note lookup_au_ds_lt_length_unions[OF ufe_union.prems(1)]
      with ufe_union.hyps False have "i = length (unions ufe_ds)"
        by simp
      moreover from calculation have "au_ds ufe_ds x \<noteq> Some i"
        using lookup_au_ds_lt_length_unions by blast
      ultimately show ?thesis
        using ufe_union.prems a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        unfolding uf_ds_ufe_union_eq_if_eff_union[OF ufe_union.hyps]
        by (simp add: ufe_union.hyps ufa_rep_of_ufa_union)
          (metis ufa_rep_of_ufa_rep_of)
      next
      case True
      with ufe_union.prems ufe_union.hyps have "au_ds ufe_ds x = Some i"
        by (simp split: if_splits)
      moreover from ufe_union.hyps True have "unions (ufe_union ufe_ds y z) ! i = unions ufe_ds ! i"
        by (simp add: nth_append)
      ultimately show ?thesis
        using ufe_union a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        by (simp add: uf_ds_ufe_union_eq ufa_rep_of_ufa_union)
    qed
  qed simp
  then show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    by blast+
qed

lemma lookup_au_ds_eq_None_iff:
  assumes "z \<in> Field (ufe_\<alpha> ufe_ds)"
  shows "au_ds ufe_ds z \<noteq> None \<longleftrightarrow> ufe_rep_of ufe_ds z \<noteq> z"
  using assms
proof(induction rule: ufe_induct)
  case init
  then show ?case
    by (auto dest!: subsetD simp: ufa_\<alpha>I)
next
  case (ufe_union ufe_ds x y)
  then show ?case
    unfolding uf_ds_ufe_union_eq_if_eff_union[OF ufe_union.hyps]
    by (simp add:  ufa_rep_of_ufa_union)
      (metis eff_unionE ufa_rep_of_ufa_rep_of)
qed

lemma inj_au_ds:
  shows "inj_on (au_ds ufe_ds) (dom (au_ds ufe_ds))"
proof(induction ufe_ds rule: ufe_induct)
  case init
  then show ?case
    by (simp add: au_ds.simps)
next
  case (ufe_union ufe_ds x y)
  then show ?case
    using lookup_au_ds_lt_length_unions
    by (force simp: domIff inj_on_def)
qed

locale ufe_forest =
  fixes ufe_ds :: ufe
begin

definition "au_of a \<equiv> the (au_ds ufe_ds (head (ufe_forest_of ufe_ds) a))"

sublocale ufa_forest where uf = "uf_ds ufe_ds"
  by unfold_locales

context
  fixes a b
  assumes eff_union: "eff_union (uf_ds ufe_ds) a b"
begin

interpretation ufe_union_forest: ufe_forest where
  ufe_ds = "ufe_union ufe_ds a b"
  by unfold_locales

lemma in_verts_ufe_forest_of_ufe_union_if_in_verts[simp, intro]:
  assumes "x \<in> verts (ufe_forest_of ufe_ds)"
  shows "x \<in> verts (ufe_forest_of (ufe_union ufe_ds a b))"
  using assms eff_union
  unfolding verts_ufa_forest_of by auto

lemma in_arcs_ufe_forest_of_ufe_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufe_forest_of ufe_ds)"
  shows "e \<in> arcs (ufe_forest_of (ufe_union ufe_ds a b))"
  using assms eff_union
  by (simp add: uf_ds_ufe_union_eq ufa_forest_of_ufa_union_eq_add_arc)

lemma ufe_union_awalk_if_awalk:
  assumes "awalk x p y"
  shows "ufe_union_forest.awalk x p y"
  using assms eff_union ufa_union_awalk_if_awalk
  by (simp add: uf_ds_ufe_union_eq)

lemma awalk_if_ufe_union_awalk:
  assumes "ufe_union_forest.awalk x p y"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "awalk x p y"
  using assms eff_union
  by (intro awalk_if_ufa_union_awalk[of a b]) (auto simp: uf_ds_ufe_union_eq)

lemma ufe_union_au_of_eq_if_in_arcs:
  assumes "e \<in> arcs (ufe_forest_of ufe_ds)"
  shows "ufe_union_forest.au_of e = au_of e"
proof -
  note assms[THEN arc_implies_awalk, THEN ufa_forest.awalk_singletonD(1)]
  with assms eff_unionD[OF eff_union] have
    "head (ufe_forest_of ufe_ds) e \<noteq> ufe_rep_of ufe_ds a"
    by (metis loopfree.no_loops ufa_parent_of_ufa_rep_of)
  then show ?thesis
    unfolding ufe_union_forest.au_of_def au_of_def
    by (auto simp: eff_union)
qed

lemma ufe_union_au_of_eq_if_head_eq:
  assumes "head (ufe_forest_of (ufe_union ufe_ds a b)) e = ufe_rep_of ufe_ds a"
  shows "ufe_union_forest.au_of e = length (unions ufe_ds)"
  using assms unfolding ufe_union_forest.au_of_def
  by (cases e) (auto simp: eff_union au_of_def)

end

lemma head_in_dom_lookup_if_in_arcs:
  assumes "e \<in> arcs (ufe_forest_of ufe_ds)"
  shows "head (ufe_forest_of ufe_ds) e \<in> dom (au_ds ufe_ds)"
  using assms
proof -
  from assms have
    "head (ufe_forest_of ufe_ds) e \<in> Field (ufe_\<alpha> ufe_ds)" (is "?a \<in> _")
    using head_in_verts by blast
  moreover from assms have "ufe_rep_of ufe_ds ?a \<noteq> ?a"
    using arc_implies_awalk awalk_and_ufa_rep_of_reflD(1) loopfree.no_loops by blast
  ultimately obtain i where "au_ds ufe_ds ?a = Some i"
    using lookup_au_ds_eq_None_iff by blast
  then show ?thesis
    unfolding domIff by simp
qed

lemma au_of_lt_length_unions:
  assumes "e \<in> arcs (ufe_forest_of ufe_ds)"
  shows "au_of e < length (unions ufe_ds)"
  using head_in_dom_lookup_if_in_arcs[OF assms]
  using lookup_au_ds_lt_length_unions
  unfolding au_of_def by force

lemma ufe_rep_of_eq_au_of:
  assumes "e \<in> arcs (ufe_forest_of ufe_ds)"
  assumes "unions ufe_ds ! au_of e = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds b"
proof -
  from head_in_dom_lookup_if_in_arcs[OF assms(1)] have
    "au_ds ufe_ds (head (ufe_forest_of ufe_ds) e) = Some (au_of e)"
    unfolding au_of_def by auto
  from ufe_rep_of_eq_if_au[OF this assms(2)] assms(1) show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds b"
    using head_in_verts by auto
qed

lemma inj_on_au_of_arcs:
  "inj_on au_of (arcs (ufe_forest_of ufe_ds))"
proof(intro inj_onI)
  let ?F = "ufe_forest_of ufe_ds"
  fix y z
  assume
    "y \<in> arcs ?F"
    "z \<in> arcs ?F"
    "au_of y = au_of z"
  with this(1,2)[THEN head_in_dom_lookup_if_in_arcs]
  have "head ?F y = head ?F z"
    by (intro inj_au_ds[THEN inj_onD]) (auto simp: au_of_def)
  with \<open>y \<in> arcs ?F\<close> \<open>z \<in> arcs ?F\<close> show "y = z"
    by (metis arc_implies_awalk awalk_singletonD(2))
qed

lemma inj_on_au_of_awalk:
  assumes "awalk x p y"
  shows "inj_on au_of (set p)"
  using assms inj_on_au_of_arcs
  by (meson awalkE' inj_on_subset)

definition "newest_on_path newest x p y \<equiv> awalk x p y \<and> newest = Max (au_of ` set p)"

lemma newest_on_path_awalkD[simp]:
  assumes "newest_on_path newest x p y"
  shows "awalk x p y"
  using assms unfolding newest_on_path_def by simp

lemma newest_on_pathE:
  assumes "newest_on_path newest x p y"
  assumes "x \<noteq> y" 
  obtains i where
    "i \<in> set p"
    "awalk x p y" "newest = au_of i"
proof -
  from assms have "au_of ` set p \<noteq> {}"
    unfolding newest_on_path_def by auto
  from Max_in[OF _ this] obtain i where "i \<in> set p" "Max (au_of ` set p) = au_of i"
    by blast
  with assms that show ?thesis
    unfolding newest_on_path_def by simp
qed

lemma newest_on_path_lt_length_unions:
  assumes "newest_on_path newest x p y"
  assumes "x \<noteq> y"
  shows "newest < length (unions ufe_ds)"
proof -
  from newest_on_pathE[OF assms] obtain i where i:
    "awalk x p y" "i \<in> set p" "newest = au_of i"
    by blast
  then show ?thesis
    using au_of_lt_length_unions by blast
qed

lemma newest_on_path_valid_union:
  assumes "newest_on_path newest x p y"
  assumes "x \<noteq> y"
  assumes "unions ufe_ds ! newest = (a, b)"
  shows "a \<in> Field (ufe_\<alpha> ufe_ds)" "b \<in> Field (ufe_\<alpha> ufe_ds)"
proof -
  from assms have "(a, b) \<in> set (unions ufe_ds)"
    using newest_on_path_lt_length_unions by (metis nth_mem)
  then show "a \<in> Field (ufe_\<alpha> ufe_ds)" "b \<in> Field (ufe_\<alpha> ufe_ds)"
    using Field_unions_subs_Field_ufe_\<alpha>
    by (auto intro: FieldI1 FieldI2)
qed

lemma ufe_rep_of_eq_if_newest_on_path:
  assumes "newest_on_path newest x p y"
  assumes "x \<noteq> y"
  assumes "unions ufe_ds ! newest = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
proof -
  from newest_on_pathE[OF assms(1,2)] obtain i where
    "i \<in> set p" "awalk x p y" "newest = au_of i"
    by blast
  moreover from this have "i \<in> arcs (ufe_forest_of ufe_ds)"
    by blast
  note head_in_dom_lookup_if_in_arcs[OF this]
  ultimately have "au_ds ufe_ds (head (ufe_forest_of ufe_ds) i) = Some newest"
    unfolding au_of_def by force
  note ufe_rep_of_eq_if_au[OF this assms(3)]
  moreover from \<open>i \<in> set p\<close> \<open>awalk x p y\<close> have
    "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds (head (ufe_forest_of ufe_ds) i)"
    using ufa_rep_of_eq_if_awalk by (metis awalk_decomp awalk_verts_arc2)
  ultimately show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    by simp_all
qed

end

end
