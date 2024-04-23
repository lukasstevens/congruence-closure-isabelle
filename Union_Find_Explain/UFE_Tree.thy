theory UFE_Tree
  imports Explain_Definition
begin

locale union_find_explain_invars =
  union_find_explain_adts where uf_adt = uf_adt and au_adt = au_adt +
  union_find_parent where uf_adt = uf_adt +
  map_mono where mm_adt = au_adt
for uf_adt :: "('uf, 'dom, _) union_find_parent_adt_scheme" (structure)
and au_adt :: "('au, 'dom, nat, _) map_mono_adt_scheme"
begin

lemma uf_ds_ufe_unions_eq_unions:
  assumes "eff_unions uf us"
  assumes "valid_unions uf us"
  assumes "uf_invar uf"
  assumes "uf_ds ufe_ds = uf"
  shows "uf_ds (ufe_unions ufe_ds us) = uf_unions uf us"
  using assms
proof(induction uf us arbitrary: ufe_ds rule: eff_unions.induct)
  case (2 uf x y us)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from 2 have "uf_ds (ufe_union ufe_ds x y) = uf_union uf x y"
    by simp
  note "2.IH"[OF _ _ _ this]
  with "2.prems" have
    "uf_ds (ufe_unions (ufe_union ufe_ds x y) us) = uf_unions (uf_union uf x y) us"
    by simp
  then show ?case
    by simp
qed simp

lemma unions_ufe_unions_eq_unions_append:
  assumes "eff_unions uf us"
  assumes "valid_unions uf us"
  assumes "uf_invar uf"
  assumes "uf_ds ufe_ds = uf"
  shows "unions (ufe_unions ufe_ds us) = unions ufe_ds @ us"
  using assms
proof(induction uf us arbitrary: ufe_ds rule: eff_unions.induct)
  case (2 uf x y us)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from 2 have "uf_ds (ufe_union ufe_ds x y) = uf_union uf x y"
    by simp
  note "2.IH"[OF _ _ _ this]
  with "2.prems" have
    "unions (ufe_unions (ufe_union ufe_ds x y) us)
    = unions (ufe_union ufe_ds x y) @ us"
    by simp
  with 2 show ?case
    by simp
qed simp

end

locale union_find_explain_ds =
  union_find_explain_invars where uf_adt = uf_adt and au_adt = au_adt
  for uf_adt (structure) and au_adt +

  fixes ufe_ds

  assumes valid_unions:
    "valid_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes eff_unions:
    "eff_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes ufe_ds_eq_ufe_unions:
    "ufe_ds = ufe_unions ufe_init (unions ufe_ds)"
begin

sublocale ufp_invar_init: union_find_parent_invar where uf = "uf_ds ufe_init"
  using invar_init by unfold_locales simp

sublocale union_find_parent_unions where uf = "uf_ds ufe_ds" and us = "unions ufe_ds"
proof(unfold_locales)
  from valid_unions show "valid_unions uf_init (unions ufe_ds)"
    by simp

  from uf_ds_ufe_unions_eq_unions[OF eff_unions valid_unions]
  show "uf_ds ufe_ds = uf_unions uf_init (unions ufe_ds)"
    using ufe_ds_eq_ufe_unions invar_init by fastforce
qed

lemma in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init[simp]:
  shows "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds)) \<longleftrightarrow> x \<in> Field (uf_\<alpha> (uf_ds ufe_init))"
  unfolding uf_eq_unions_init using valid_unions by simp

lemma ufe_explain_ds_union:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  defines "ufe_ds' \<equiv> ufe_union ufe_ds x y"
  shows "union_find_explain_ds uf_adt au_adt ufe_ds'"
proof unfold_locales
  from assms have x_y_in_Field:
    "x \<in> Field (uf_\<alpha> (uf_ds ufe_init))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_init))"
    by simp_all
  with valid_unions show "valid_unions (uf_ds ufe_init) (unions ufe_ds')"
    unfolding ufe_ds'_def by (auto simp: ufe_union_sel)

  show "ufe_ds' = ufe_unions ufe_init (unions ufe_ds')"
    unfolding ufe_ds'_def using ufe_ds_eq_ufe_unions
    by (simp add: ufe_union_sel)

  show "eff_unions (uf_ds ufe_init) (unions ufe_ds')"
  proof(cases "uf_rep_of (uf_ds ufe_ds) x = uf_rep_of (uf_ds ufe_ds) y")
    case True
    then have "unions ufe_ds' = unions ufe_ds"
      by (simp add: ufe_union_sel ufe_ds'_def)
    with eff_unions show ?thesis
      by simp
  next
    case False
    from ufp_invar_init.invar_uf have "uf_invar (uf_ds ufe_init)"
      by simp
    from x_y_in_Field have "valid_unions (uf_ds ufe_init) (unions ufe_ds @ [(x, y)])"
      using assms valid_unions by auto
    note eff_unions_append[OF \<open>uf_invar (uf_ds ufe_init)\<close> this]
    with False eff_unions show ?thesis
      unfolding ufe_ds'_def by (simp add: uf_eq_unions_init)
  qed
qed

lemma ufe_ds_induct[case_names ufe_init ufe_union]:
  assumes "P ufe_init"
  assumes "\<And>ufe_ds x y.
    \<lbrakk> union_find_explain_ds uf_adt au_adt ufe_ds
    ; x \<in> Field (uf_\<alpha> (uf_ds ufe_ds)); y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))
    ; uf_rep_of (uf_ds ufe_ds) x \<noteq> uf_rep_of (uf_ds ufe_ds) y
    ; P ufe_ds 
    \<rbrakk> \<Longrightarrow> P (ufe_union ufe_ds x y)"
  shows "P ufe_ds"
  using valid_unions eff_unions ufe_ds_eq_ufe_unions
proof(induction "unions ufe_ds" arbitrary: ufe_ds rule: rev_induct)
  case (snoc u us)
  let ?ufe_ds0 = "ufe_unions ufe_init us"

  from snoc have valid_unions:
    "valid_unions (uf_ds ufe_init) us"
    using valid_unions_append unfolding ufe_init_sel by metis
  moreover from snoc have eff_unions:
    "eff_unions (uf_ds ufe_init) us"
    using eff_unions_append invar_init unfolding ufe_init_sel by metis
  ultimately have
    unions_ufe_unions_eq: "unions (ufe_unions ufe_init us) = us" and
    uf_ds_ufe_unions_eq: "uf_ds (ufe_unions ufe_init us) = uf_unions uf_init us"
    using unions_ufe_unions_eq_unions_append
    using uf_ds_ufe_unions_eq_unions
    using invar_init by auto

  with snoc.hyps(1) valid_unions eff_unions have "P (ufe_unions ufe_init us)"
    by simp
  moreover have "union_find_explain_ds uf_adt au_adt ?ufe_ds0"
    using valid_unions eff_unions unions_ufe_unions_eq by unfold_locales auto
  moreover from snoc have
    "fst u \<in> Field (uf_\<alpha> (uf_ds ?ufe_ds0))"
    "snd u \<in> Field (uf_\<alpha> (uf_ds ?ufe_ds0))"
    unfolding uf_ds_ufe_unions_eq using ufp_invar_init.Field_\<alpha>_unions
    by (metis valid_unions_Cons valid_unions_append)+
  moreover from snoc.prems snoc.hyps(2)[symmetric] have
    "uf_rep_of (uf_ds ?ufe_ds0) (fst u) \<noteq> uf_rep_of (uf_ds ?ufe_ds0) (snd u)"
    using eff_unions_append[OF invar_init] uf_ds_ufe_unions_eq
    by (cases u) auto
  ultimately have "P (ufe_union ?ufe_ds0 (fst u) (snd u))"
    using assms(2) by blast
  then show ?case
    using \<open>ufe_ds = ufe_unions ufe_init (unions ufe_ds)\<close>[folded \<open>us @ [u] = unions ufe_ds\<close>]
    by simp
qed (use assms(1) in simp)

lemma mm_invar_au_ds: "mm_invar\<^bsub>au_adt\<^esub> (au_ds ufe_ds)"
  by (induction rule: ufe_ds_induct) simp_all
                   
lemma lookup_au_ds_lt_length_unions:
  "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) x = Some i \<Longrightarrow> i < length (unions ufe_ds)"
proof(induction rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    by (simp add: \<alpha>_empty \<alpha>_lookup)
next
  case (ufe_union ufe_ds y z)
  then interpret union_find_explain_ds where ufe_ds = ufe_ds
    by simp
  note mm_relI[OF mm_invar_au_ds, transfer_rule]
  from ufe_union show ?case
    unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
    by (transfer fixing: ufe_ds) (auto simp: less_SucI split: if_splits)
qed

lemma dom_lookup_au_ds_subs_Field_\<alpha>:
  "dom (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds)) \<subseteq> Field (uf_\<alpha> (uf_ds ufe_ds))"
proof(induction rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    by (simp add: \<alpha>_empty \<alpha>_lookup)
next
  case (ufe_union ufe_ds y z)
  then interpret union_find_explain_ds where ufe_ds = ufe_ds
    by simp
  note mm_relI[OF mm_invar_au_ds, transfer_rule]
  from ufe_union show ?case
    unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
    by (transfer fixing: uf_adt ufe_ds) (use rep_of_in_Field_\<alpha>_if_in_Field_\<alpha> in simp)
qed

lemma rep_of_eq_if_au:
  assumes "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) x = Some i"
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
    then show ?case
      by (simp add: \<alpha>_empty \<alpha>_lookup)
  next
    case (ufe_union ufe_ds y z)
    then interpret union_find_explain_ds where ufe_ds = ufe_ds
      by simp
    from ufe_union interpret ufe_ds_union: union_find_explain_ds where
      ufe_ds = "ufe_union ufe_ds y z"
      by (intro ufe_explain_ds_union)
    note mm_relI[OF mm_invar_au_ds, transfer_rule]

    from ufe_union.prems have "(a, b) \<in> set (unions (ufe_union ufe_ds y z))"
      by (metis nth_mem ufe_ds_union.lookup_au_ds_lt_length_unions)
    with ufe_ds_union.valid_unions have
      a_in_Field_\<alpha>: "a \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" and
      b_in_Field_\<alpha>: "b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
      unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
      by (auto simp: valid_unions_def)
    from ufe_union have x_in_Field_\<alpha>: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
      using ufe_ds_union.dom_lookup_au_ds_subs_Field_\<alpha> by auto

    show ?case
    proof(cases "i < length (unions ufe_ds)")
      case False

      note ufe_ds_union.lookup_au_ds_lt_length_unions[OF ufe_union.prems(1)]
      with False ufe_union.hyps(4) have "i = length (unions ufe_ds)"
        by simp
      moreover from calculation have "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) x \<noteq> Some i"
        using lookup_au_ds_lt_length_unions by blast
      ultimately show ?thesis
        using ufe_union.prems a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha> rep_of_union
        unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
        apply(transfer fixing: uf_adt ufe_ds y z a b x i)
        by (metis fun_upd_other id_apply nth_append_length prod.inject rep_of_rep_of)
    next
      case True
      with ufe_union.prems have "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) x = Some i"
        unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
        by (transfer fixing: uf_adt ufe_ds y z a b x i) (auto split: if_splits)
      moreover from True have "unions (ufe_union ufe_ds y z) ! i = unions ufe_ds ! i"
        by (simp add: True ufe_union.hyps(4))
      ultimately show ?thesis
        using a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        using ufe_union.IH ufe_union.hyps(2-4) ufe_union.prems(2)
        by (force simp: rep_of_union)
    qed
  qed
  then show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    by blast+
qed


lemma lookup_au_ds_eq_None_iff:
  assumes "z \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) z \<noteq> None \<longleftrightarrow> ufe_rep_of ufe_ds z \<noteq> z"
  using assms
proof(induction rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    using ufp_invar_init.refl_parent_of_iff_refl_rep_of
    by (simp add: \<alpha>_empty \<alpha>_lookup)
next
  case (ufe_union ufe_ds x y)
  then interpret union_find_explain_ds where ufe_ds = ufe_ds
    by blast
  note mm_relI[OF mm_invar_au_ds, transfer_rule]
  from ufe_union.hyps have
    "mm_invar\<^bsub>au_adt\<^esub> (au_ds (ufe_union ufe_ds x y))"
    using mm_invar_au_ds by fastforce
  note mm_relI[OF this, transfer_rule]

  from ufe_union show ?case
    unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union.hyps(4)]
    by (transfer fixing: ufe_ds) (subst rep_of_union, auto)
qed

lemma inj_on_\<alpha>_au_ds:
  shows "inj_on (mm_\<alpha>\<^bsub>au_adt\<^esub> (au_ds ufe_ds)) (dom (mm_\<alpha>\<^bsub>au_adt\<^esub> (au_ds ufe_ds)))"
proof(induction rule: ufe_ds_induct)
  case ufe_init
  then show ?case
    by (simp add: \<alpha>_empty)
next
  case (ufe_union ufe_ds x y)
  then interpret union_find_explain_ds where ufe_ds = ufe_ds
    by blast
  interpret map_mono_invar where mm_adt = au_adt and m = "au_ds ufe_ds"
    using mm_invar_au_ds by unfold_locales

  from ufe_union show ?case
    using lookup_au_ds_lt_length_unions
    by (force simp: \<alpha>_update \<alpha>_lookup dom_def inj_on_def)
qed

end

locale ufe_tree = union_find_explain_ds  +
  fixes x
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
begin

sublocale ufa_tree where uf = "uf_ds ufe_ds" and us = "unions ufe_ds" and x = x
  using x_in_Field_\<alpha> valid_unions
  by unfold_locales

definition "au_of a \<equiv>
  the (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) (head (ufa_tree_of (uf_ds ufe_ds) x) a))"

lemma head_in_dom_lookup_if_in_arcs:
  assumes "e \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "head (ufa_tree_of (uf_ds ufe_ds) x) e \<in> dom (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds))"
  using assms
proof -
  from assms have
    "head (ufa_tree_of (uf_ds ufe_ds) x) e \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" (is "?a \<in> _")
    using head_in_verts by blast
  moreover from assms have "ufe_rep_of ufe_ds ?a \<noteq> ?a"
    using adj_in_verts(2) not_root_if_dominated by (cases e) fastforce
  ultimately obtain i where "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) ?a = Some i"
    using lookup_au_ds_eq_None_iff by blast
  then show ?thesis
    unfolding domIff by simp
qed

lemma au_of_lt_length_unions:
  assumes "e \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "au_of e < length (unions ufe_ds)"
  using head_in_dom_lookup_if_in_arcs[OF assms]
  using lookup_au_ds_lt_length_unions
  unfolding au_of_def by force

lemma rep_of_eq_au_of:
  assumes "e \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  assumes "unions ufe_ds ! au_of e = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
proof -
  from head_in_dom_lookup_if_in_arcs[OF assms(1)] have
    "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) (head (ufa_tree_of (uf_ds ufe_ds) x) e) =
    Some (au_of e)"
    unfolding au_of_def by auto
  from rep_of_eq_if_au[OF this assms(2)] assms(1) show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    using head_in_verts by auto
qed

lemma inj_on_au_of_arcs:
  "inj_on au_of (arcs (ufa_tree_of (uf_ds ufe_ds) x))"
proof(intro inj_onI)
  let ?T = "ufa_tree_of (uf_ds ufe_ds) x"
  fix y z
  assume
    "y \<in> arcs ?T"
    "z \<in> arcs ?T"
    "au_of y = au_of z"
  with this(1,2)[THEN head_in_dom_lookup_if_in_arcs]
  have "head ?T y = head ?T z"
    by (intro inj_on_\<alpha>_au_ds[THEN inj_onD])
      (auto simp: au_of_def \<alpha>_lookup[OF mm_invar_au_ds])
  with \<open>y \<in> arcs ?T\<close> \<open>z \<in> arcs ?T\<close> show "y = z"
    using two_in_arcs_contr by blast
qed

lemma inj_on_au_of_awalk:
  assumes "awalk y p z"
  shows "inj_on au_of (set p)"
  using assms inj_on_au_of_arcs
  by (meson awalkE' inj_on_subset)

definition "newest_on_walk newest y p z \<equiv> awalk y p z \<and> newest = Max (au_of ` set p)"

lemma newest_on_walk_awalkD[simp]:
  assumes "newest_on_walk newest y p z"
  shows "awalk y p z"
  using assms unfolding newest_on_walk_def by simp

lemma newest_on_walkE:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z" 
  obtains i where
    "i \<in> set p"
    "awalk y p z" "newest = au_of i"
proof -
  from assms have "au_of ` set p \<noteq> {}"
    unfolding newest_on_walk_def by auto
  from Max_in[OF _ this] obtain i where "i \<in> set p" "Max (au_of ` set p) = au_of i"
    by blast
  with assms that show ?thesis
    unfolding newest_on_walk_def by simp
qed

lemma newest_on_walk_lt_length_unions:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z"
  shows "newest < length (unions ufe_ds)"
proof -
  from newest_on_walkE[OF assms] obtain i where i:
    "awalk y p z" "i \<in> set p" "newest = au_of i"
    by blast
  then show ?thesis
    using au_of_lt_length_unions by blast
qed

lemma newest_on_walk_valid_union:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z"
  assumes "unions ufe_ds ! newest = (a, b)"
  shows "a \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "b \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  using newest_on_walk_lt_length_unions[OF assms(1,2)] assms(3)
  using valid_unions_nth_eq_pairD valid_unions
  by auto

lemma rep_of_eq_if_newest_on_walk:
  assumes "newest_on_walk newest y p z"
  assumes "y \<noteq> z"
  assumes "unions ufe_ds ! newest = (a, b)"
  shows
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
proof -
  from newest_on_walkE[OF assms(1,2)] obtain i where
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