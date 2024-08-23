theory UFE_Tree
  imports Explain_Simple Explain_Efficient
begin

lemma ufa_\<alpha>_uf_ds_ufe_unions_eq_ufa_\<alpha>_ufa_unions_uf_ds:
  assumes "eff_unions (uf_ds ufe_ds) us"
  shows "ufe_\<alpha> (ufe_unions ufe_ds us) = ufa_\<alpha> (ufa_unions (uf_ds ufe_ds) us)"
  using assms
  by (induction "uf_ds ufe_ds" us arbitrary: ufe_ds rule: eff_unions.induct) simp_all

locale ufe_init_invars =
  fixes ufe_init :: "ufe_ds"

  assumes ufa_\<alpha>_uf_ds_ufe_init:
    "ufe_\<alpha> ufe_init \<subseteq> Id"
  assumes au_ds_ufe_init[simp]:
    "au_ds ufe_init = Map.empty"
  assumes unions_ufe_init[simp]:
    "unions ufe_init = []"
begin

lemma in_ufa_\<alpha>_uf_ds_ufe_init[simp]:
  assumes "x \<in> Field (ufe_\<alpha> ufe_init)"
  shows "(x, x) \<in> ufe_\<alpha> ufe_init"
  using assms ufa_\<alpha>_uf_ds_ufe_init ufa_\<alpha>I by blast

lemma ufe_rep_of_ufe_init:
  assumes "x \<in> Field (ufe_\<alpha> ufe_init)"
  shows "ufe_rep_of ufe_init x = x"
  using assms ufa_\<alpha>_uf_ds_ufe_init ufa_rep_of_eq_iff_in_ufa_\<alpha> by fastforce

end

locale ufe_invars = ufe_init_invars +
  fixes ufe_ds

  assumes eff_unions:
    "eff_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes ufe_ds_eq_ufe_unions:
    "ufe_ds = ufe_unions ufe_init (unions ufe_ds)"
begin

lemma ufe_ds_induct[case_names ufe_init ufe_union]:
  assumes "P ufe_init"
  assumes "\<And>ufe_ds x y.
    \<lbrakk> ufe_invars ufe_init ufe_ds; eff_union (uf_ds ufe_ds) x y; P ufe_ds 
    \<rbrakk> \<Longrightarrow> P (ufe_union ufe_ds x y)"
  shows "P ufe_ds"
  using eff_unions ufe_ds_eq_ufe_unions
proof(induction "unions ufe_ds" arbitrary: ufe_ds rule: rev_induct)
  case (snoc u us)
  let ?ufe_ds0 = "ufe_unions ufe_init us"

  from snoc have "ufe_\<alpha> ?ufe_ds0 = ufa_\<alpha> (ufa_unions (uf_ds ufe_init) us)"
    by (metis ufa_\<alpha>_uf_ds_ufe_unions_eq_ufa_\<alpha>_ufa_unions_uf_ds eff_unions_append)
  moreover from this have u_in_Field_ufa_\<alpha>:
    "fst u \<in> Field (ufe_\<alpha> (ufe_unions ufe_init us))"
    "snd u \<in> Field (ufe_\<alpha> (ufe_unions ufe_init us))"
    using snoc.prems \<open>us @ [u] = unions ufe_ds\<close>[symmetric]
    by (force simp: eff_unions_append)+

  moreover from snoc have "ufa_rep_of (ufa_unions (uf_ds ufe_init) us) (fst u) \<noteq>
    ufa_rep_of (ufa_unions (uf_ds ufe_init) us) (snd u)"
    using \<open>us @ [u] = unions ufe_ds\<close>[symmetric]
    by (simp add: eff_unions_append)
  ultimately have eff_union_u:
    "eff_union (uf_ds (ufe_unions ufe_init us)) (fst u) (snd u)"
    unfolding eff_union_def valid_union_def
    by (simp add: ufa_rep_of_eq_iff_in_ufa_\<alpha>)

  moreover from snoc have "ufe_ds = ufe_union ?ufe_ds0 (fst u) (snd u)"
    by (metis ufe_unions_Cons ufe_unions_Nil ufe_unions_append)
  moreover from this snoc have "unions (ufe_union ?ufe_ds0 (fst u) (snd u)) = us @ [u]"
    by simp
  ultimately have "us = unions ?ufe_ds0"
    by fastforce
  moreover from this have
    "?ufe_ds0 = ufe_unions ufe_init (unions ?ufe_ds0)"
    by simp
  moreover from \<open>us = unions ?ufe_ds0\<close> snoc.prems snoc.hyps(2)[symmetric] have
    "eff_unions (uf_ds ufe_init) (unions ?ufe_ds)"
    by (simp_all add: eff_unions_append)
  ultimately have "P ?ufe_ds0"
    using snoc.hyps(1) by blast

  moreover have "ufe_invars ufe_init ?ufe_ds0"
    using \<open>us = unions ?ufe_ds0\<close>
    using \<open>eff_unions (uf_ds ufe_init) (unions ?ufe_ds0)\<close>
    by unfold_locales simp_all

  ultimately have "P (ufe_union ?ufe_ds0 (fst u) (snd u))"
    using \<open>unions (ufe_union ?ufe_ds0 (fst u) (snd u)) = us @ [u]\<close>
    using u_in_Field_ufa_\<alpha> eff_union_u assms(2)
    by (simp add: case_prod_unfold)
  then show ?case
    using \<open>ufe_ds = ufe_union ?ufe_ds0 (fst u) (snd u)\<close> by blast
qed (use assms(1) in simp)

lemma uf_ds_ufe_ds_eq_ufa_unions:
  "uf_ds ufe_ds = ufa_unions (uf_ds ufe_init) (unions ufe_ds)"
  by (induction rule: ufe_ds_induct) (simp_all add: ufa_unions_def)

lemma in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init:
  shows "x \<in> Field (ufe_\<alpha> ufe_ds) \<longleftrightarrow> x \<in> Field (ufe_\<alpha> ufe_init)"
  using uf_ds_ufe_ds_eq_ufa_unions eff_unions by simp

lemma ufe_invars_ufe_union:
  assumes "eff_union (uf_ds ufe_ds) x y"
  defines "ufe_ds' \<equiv> ufe_union ufe_ds x y"
  shows "ufe_invars ufe_init ufe_ds'"
proof unfold_locales
  from assms have x_y_in_Field:
    "x \<in> Field (ufe_\<alpha> ufe_init)" "y \<in> Field (ufe_\<alpha> ufe_init)"
    using in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init
    by auto

  show "ufe_ds' = ufe_unions ufe_init (unions ufe_ds')"
    unfolding ufe_ds'_def using ufe_ds_eq_ufe_unions
    by simp

  from assms x_y_in_Field eff_unions show "eff_unions (uf_ds ufe_init) (unions ufe_ds')"
    unfolding ufe_ds'_def uf_ds_ufe_ds_eq_ufa_unions
    by (auto simp: eff_unions_append)
qed
                   
lemma lookup_au_ds_lt_length_unions:
  "au_ds ufe_ds x = Some i \<Longrightarrow> i < length (unions ufe_ds)"
proof(induction rule: ufe_ds_induct)
  case (ufe_union ufe_ds y z)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by simp
  from ufe_union show ?case
    by (auto simp: less_SucI split: if_splits)
qed simp

lemma dom_au_ds_subs_Field_ufa_\<alpha>:
  "dom (au_ds ufe_ds) \<subseteq> Field (ufe_\<alpha> ufe_ds)"
proof(induction rule: ufe_ds_induct)
  case (ufe_union ufe_ds y z)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by simp
  from ufe_union show ?case
    using ufa_rep_of_in_Field_ufa_\<alpha>I
    by (fastforce split: if_splits)+
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
  proof(induction arbitrary: i a b rule: ufe_ds_induct)
    case ufe_init
    then show ?case by simp
  next
    case (ufe_union ufe_ds y z)
    then interpret ufe_invars where ufe_ds = ufe_ds
      by simp
    from ufe_union interpret ufe_invars_union: ufe_invars where
      ufe_ds = "ufe_union ufe_ds y z"
      by (intro ufe_invars_ufe_union eff_unionI) simp_all

    from ufe_union.prems have "(a, b) \<in> set (unions (ufe_union ufe_ds y z))"
      by (metis nth_mem ufe_invars_union.lookup_au_ds_lt_length_unions)
    with ufe_invars_union.eff_unions have
      a_in_Field_\<alpha>: "a \<in> Field (ufe_\<alpha> ufe_ds)" and
      b_in_Field_\<alpha>: "b \<in> Field (ufe_\<alpha> ufe_ds)"
      unfolding in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init
      using in_Field_ufa_\<alpha>_if_in_eff_unions by force+
    from ufe_union have x_in_Field_\<alpha>: "x \<in> Field (ufe_\<alpha> ufe_ds)"
      using ufe_invars_union.dom_au_ds_subs_Field_ufa_\<alpha>
      using Field_ufa_\<alpha>_uf_ds_ufe_union by blast

    show ?case
    proof(cases "i < length (unions ufe_ds)")
      case False

      note ufe_invars_union.lookup_au_ds_lt_length_unions[OF ufe_union.prems(1)]
      with False have "i = length (unions ufe_ds)"
        by simp
      moreover from calculation have "au_ds ufe_ds x \<noteq> Some i"
        using lookup_au_ds_lt_length_unions by blast
      ultimately show ?thesis
        using ufe_union.prems a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        by (simp add: ufa_rep_of_ufa_union) (metis ufa_rep_of_ufa_rep_of)
    next
      case True
      with ufe_union.prems ufe_union.hyps have "au_ds ufe_ds x = Some i"
        by (simp split: if_splits)
      moreover from True have "unions (ufe_union ufe_ds y z) ! i = unions ufe_ds ! i"
        by (simp add: nth_append)
      ultimately show ?thesis
        using a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        using ufe_union
        by (force simp: ufa_rep_of_ufa_union)+
    qed
  qed
  then show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    by blast+
qed

lemma lookup_au_ds_eq_None_iff:
  assumes "z \<in> Field (ufe_\<alpha> ufe_ds)"
  shows "au_ds ufe_ds z \<noteq> None \<longleftrightarrow> ufe_rep_of ufe_ds z \<noteq> z"
  using assms
proof(induction rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    using ufa_\<alpha>_uf_ds_ufe_init ufa_eq_class_def ufa_eq_class_ufa_rep_of
    by fastforce
next
  case (ufe_union ufe_ds x y)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by blast

  from ufe_union show ?case
    by (simp add: ufa_rep_of_ufa_union) (metis eff_unionE ufa_rep_of_ufa_rep_of)
qed

lemma inj_au_ds:
  shows "inj_on (au_ds ufe_ds) (dom (au_ds ufe_ds))"
proof(induction rule: ufe_ds_induct)
  case (ufe_union ufe_ds x y)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by blast

  from ufe_union show ?case
    using lookup_au_ds_lt_length_unions
    unfolding dom_def inj_on_def
    by simp_all (metis order_less_irrefl)
qed simp

end

locale ufe_tree = ufe_invars +
  fixes x
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (ufe_\<alpha> ufe_ds)"
begin

sublocale ufa_tree where uf = "uf_ds ufe_ds" and x = x
  using x_in_Field_\<alpha> eff_unions
  by unfold_locales

context
  fixes a b
  assumes eff_union: "eff_union (uf_ds ufe_ds) a b"
begin

interpretation ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
  using eff_union ufe_invars_ufe_union by blast

interpretation ufe_tree_union: ufe_tree where
  ufe_ds = "ufe_union ufe_ds a b" and x = x
  by unfold_locales simp

lemma in_verts_ufa_tree_of_ufe_union_if_in_verts[simp, intro]:
  assumes "y \<in> verts (ufe_tree_of ufe_ds x)"
  shows "y \<in> verts (ufe_tree_of (ufe_union ufe_ds a b) x)"
  using assms eff_union 
  using in_verts_ufa_tree_of_union_if_in_verts
  by auto

lemma in_arcs_ufa_tree_of_ufe_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufe_tree_of ufe_ds x)"
  shows "e \<in> arcs (ufe_tree_of (ufe_union ufe_ds a b) x)"
  using assms eff_unionD[OF eff_union]
  using in_arcs_ufa_tree_of_union_if_in_arcs
  by auto

lemma ufe_union_awalk_if_awalk:
  assumes "awalk y p z"
  shows "ufe_tree_union.awalk y p z"
  using assms eff_union union_awalk_if_awalk
  by auto

lemma awalk_if_ufe_union_awalk:
  assumes "ufe_tree_union.awalk x p y"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "awalk x p y"
  using awalk_if_union_awalk[OF _ _ _ assms(2)] assms(1) eff_union
  by auto

end

definition "au_of a \<equiv> the (au_ds ufe_ds (head (ufe_tree_of ufe_ds x) a))"

lemma head_in_dom_lookup_if_in_arcs:
  assumes "e \<in> arcs (ufe_tree_of ufe_ds x)"
  shows "head (ufe_tree_of ufe_ds x) e \<in> dom (au_ds ufe_ds)"
  using assms
proof -
  from assms have
    "head (ufe_tree_of ufe_ds x) e \<in> Field (ufe_\<alpha> ufe_ds)" (is "?a \<in> _")
    using head_in_verts by blast
  moreover from assms have "ufe_rep_of ufe_ds ?a \<noteq> ?a"
    using adj_in_verts(2) not_root_if_dominated by (cases e) fastforce
  ultimately obtain i where "au_ds ufe_ds ?a = Some i"
    using lookup_au_ds_eq_None_iff by blast
  then show ?thesis
    unfolding domIff by simp
qed

lemma au_of_lt_length_unions:
  assumes "e \<in> arcs (ufe_tree_of ufe_ds x)"
  shows "au_of e < length (unions ufe_ds)"
  using head_in_dom_lookup_if_in_arcs[OF assms]
  using lookup_au_ds_lt_length_unions
  unfolding au_of_def by force

lemma rep_of_eq_au_of:
  assumes "e \<in> arcs (ufe_tree_of ufe_ds x)"
  assumes "unions ufe_ds ! au_of e = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
proof -
  from head_in_dom_lookup_if_in_arcs[OF assms(1)] have
    "au_ds ufe_ds (head (ufe_tree_of ufe_ds x) e) = Some (au_of e)"
    unfolding au_of_def by auto
  from ufe_rep_of_eq_if_au[OF this assms(2)] assms(1) show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    using head_in_verts by auto
qed

lemma inj_on_au_of_arcs:
  "inj_on au_of (arcs (ufe_tree_of ufe_ds x))"
proof(intro inj_onI)
  let ?T = "ufe_tree_of ufe_ds x"
  fix y z
  assume
    "y \<in> arcs ?T"
    "z \<in> arcs ?T"
    "au_of y = au_of z"
  with this(1,2)[THEN head_in_dom_lookup_if_in_arcs]
  have "head ?T y = head ?T z"
    by (intro inj_au_ds[THEN inj_onD]) (auto simp: au_of_def)
  with \<open>y \<in> arcs ?T\<close> \<open>z \<in> arcs ?T\<close> show "y = z"
    using two_in_arcs_contr by blast
qed

lemma inj_on_au_of_awalk:
  assumes "awalk y p z"
  shows "inj_on au_of (set p)"
  using assms inj_on_au_of_arcs
  by (meson awalkE' inj_on_subset)

definition "newest_on_path newest y p z \<equiv> awalk y p z \<and> newest = Max (au_of ` set p)"

lemma newest_on_path_awalkD[simp]:
  assumes "newest_on_path newest y p z"
  shows "awalk y p z"
  using assms unfolding newest_on_path_def by simp

lemma newest_on_pathE:
  assumes "newest_on_path newest y p z"
  assumes "y \<noteq> z" 
  obtains i where
    "i \<in> set p"
    "awalk y p z" "newest = au_of i"
proof -
  from assms have "au_of ` set p \<noteq> {}"
    unfolding newest_on_path_def by auto
  from Max_in[OF _ this] obtain i where "i \<in> set p" "Max (au_of ` set p) = au_of i"
    by blast
  with assms that show ?thesis
    unfolding newest_on_path_def by simp
qed

lemma newest_on_path_lt_length_unions:
  assumes "newest_on_path newest y p z"
  assumes "y \<noteq> z"
  shows "newest < length (unions ufe_ds)"
proof -
  from newest_on_pathE[OF assms] obtain i where i:
    "awalk y p z" "i \<in> set p" "newest = au_of i"
    by blast
  then show ?thesis
    using au_of_lt_length_unions by blast
qed

lemma newest_on_path_valid_union:
  assumes "newest_on_path newest y p z"
  assumes "y \<noteq> z"
  assumes "unions ufe_ds ! newest = (a, b)"
  shows "a \<in> Field (ufe_\<alpha> ufe_ds)" "b \<in> Field (ufe_\<alpha> ufe_ds)"
proof -
  from assms have "(a, b) \<in> set (unions ufe_ds)"
    using newest_on_path_lt_length_unions by (metis nth_mem)
  then show "a \<in> Field (ufe_\<alpha> ufe_ds)" "b \<in> Field (ufe_\<alpha> ufe_ds)"
    using uf_ds_ufe_ds_eq_ufa_unions in_Field_ufa_\<alpha>_if_in_eff_unions eff_unions by auto
qed

lemma ufe_rep_of_eq_if_newest_on_path:
  assumes "newest_on_path newest y p z"
  assumes "y \<noteq> z"
  assumes "unions ufe_ds ! newest = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
proof -
  from newest_on_pathE[OF assms(1,2)] obtain i where
    "i \<in> set p" "awalk y p z" "newest = au_of i"
    by blast
  moreover note rep_of_eq_au_of[OF _ assms(3)[unfolded this]]
  moreover have "ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds x"
    using \<open>awalk y p z\<close> awalk_def by force
  ultimately show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    by (metis (no_types, lifting) awalkE' subsetD)+
qed

end

end