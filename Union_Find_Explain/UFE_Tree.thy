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

(*
lemma Field_\<alpha>_ufe_union:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "Field (uf_\<alpha> (uf_ds (ufe_union ufe_ds x y))) = Field (uf_\<alpha> (uf_ds ufe_ds))"
  using assms
  by (auto simp: uf_ds_ufe_union \<alpha>_union)

lemma invar_ufe_union:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "uf_invar (uf_ds (ufe_union ufe_ds x y))"
  using assms
  by (auto simp: uf_ds_ufe_union invar_union)

lemma Field_\<alpha>_ufe_unions:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "valid_unions (uf_ds ufe_ds) us"
  shows "Field (uf_\<alpha> (uf_ds (ufe_unions ufe_ds us))) = Field (uf_\<alpha> (uf_ds ufe_ds))"
  using assms
proof(induction us arbitrary: ufe_ds)
  case (Cons u us)
  then interpret union_find_invar where uf = "uf_ds ufe_ds"
    by unfold_locales
  from Cons show ?case
  proof(cases u)
    case (Pair u1 u2)
    with Cons have "uf_invar (uf_union (uf_ds ufe_ds) u1 u2)"
      by simp
    with Cons have invar: "uf_invar (uf_ds (ufe_union ufe_ds u1 u2))"
      by (simp add: uf_ds_ufe_union)

    from Cons Pair have valid: "valid_unions (uf_ds (ufe_union ufe_ds u1 u2)) us"
      using valid_union_union by (force simp: uf_ds_ufe_union)

    with Cons.IH[OF invar valid] Cons.prems show ?thesis
      using Pair by (simp add: Field_\<alpha>_ufe_union ufe_unions_def)
  qed
qed (simp add: ufe_unions_def)
    
lemma valid_unions_ufe_unions_eq:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "valid_unions (uf_ds ufe_ds) us"
  shows "valid_unions (uf_ds (ufe_unions ufe_ds us)) ous = valid_unions (uf_ds ufe_ds) ous"
  using Field_\<alpha>_ufe_unions[OF assms] unfolding valid_unions_def by simp

lemma invar_ufe_unions:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "valid_unions (uf_ds ufe_ds) us"
  shows "uf_invar (uf_ds (ufe_unions ufe_ds us))"
  using assms
proof(induction us arbitrary: ufe_ds)
  case (Cons u us)
  then interpret union_find_invar where uf = "uf_ds ufe_ds"
    by unfold_locales
  from Cons show ?case
    using invar_union valid_union_union  unfolding ufe_unions_def
    by (cases u) (force simp: uf_ds_ufe_union)
qed (simp add: ufe_unions_def)

lemma uf_invar_ufe_init: "uf_invar (uf_ds ufe_init)"
  using invar_init by simp

lemma mm_invar_ufe_init: "mm_invar\<^bsub>au_adt\<^esub> (au_ds ufe_init)"
  using invar_empty by simp

lemma
  assumes "eff_unions (uf_ds ufe_ds) us"
  assumes "valid_unions (uf_ds ufe_ds) us"
  assumes "uf_invar (uf_ds ufe_ds)"
  shows unions_ufe_unions_eq_if_eff_unions:
    "unions (ufe_unions ufe_ds us) = unions ufe_ds @ us" (is ?P1)
  and uf_ds_ufe_unions_eq:
    "uf_ds (ufe_unions ufe_ds us)
    = foldl (\<lambda>uf (x, y). uf_union uf x y) (uf_ds ufe_ds) us" (is ?P2)
proof -
  from assms have "?P1 \<and> ?P2"
  proof(induction "uf_ds ufe_ds" us arbitrary: ufe_ds rule: eff_unions.induct)
    case (2 x y us)
    let ?ufe_ds' = "ufe_union ufe_ds x y"
    from 2 have eq_uf_ds':
      "uf_union (uf_ds ufe_ds) x y = uf_ds ?ufe_ds'"
      by (auto simp: uf_ds_ufe_union)
    moreover from 2 eq_uf_ds' have "eff_unions (uf_ds ?ufe_ds') us"
      by auto
    moreover from 2 have "valid_unions (uf_ds ?ufe_ds') us"
      using valid_unions_ufe_unions_eq[where ?us="[(x, y)]"] by force
    moreover from 2 have "uf_invar (uf_ds ?ufe_ds')"
      using invar_ufe_union by force
    ultimately have
      "unions (ufe_unions ?ufe_ds' us) = unions ?ufe_ds' @ us"
      "uf_ds (ufe_unions ?ufe_ds' us)
        = foldl (\<lambda>uf (x, y). uf_union uf x y) (uf_ds ?ufe_ds') us"
      using 2 by blast+
    with "2.prems" show ?case
      by (auto simp: ufe_union_sel)
  qed simp
  then show ?P1 ?P2
    by blast+
qed

lemma eff_unions_uf_ds_append:
  assumes "valid_unions (uf_ds ufe_ds) (us1 @ us2)"
  assumes "uf_invar (uf_ds ufe_ds)"
  shows "eff_unions (uf_ds ufe_ds) (us1 @ us2)
    \<longleftrightarrow> eff_unions (uf_ds ufe_ds) us1 \<and> eff_unions (uf_ds (ufe_unions ufe_ds us1)) us2"
  using assms eff_unions_append uf_ds_ufe_unions_eq by auto
*)

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
  (*
  assumes invar_au: "mm_invar\<^bsub>au_adt\<^esub> au"
  assumes valid_au:
    "mm_lookup\<^bsub>au_adt\<^esub> au x = Some i \<Longrightarrow> i < length unions"
  assumes inj_on_dom_au:
    "inj_on (mm_lookup\<^bsub>au_adt\<^esub> au) (dom (mm_lookup\<^bsub>au_adt\<^esub> au))"
  assumes lookup_au_if_not_rep:
    "y \<in> Field (uf_\<alpha> uf) \<Longrightarrow> uf_rep_of uf y \<noteq> y \<Longrightarrow> mm_lookup\<^bsub>au_adt\<^esub> au y \<noteq> None" *)
  (* assumes rep_of_before_au:
    "\<lbrakk> mm_lookup\<^bsub>au_adt\<^esub> au x = Some i; unions ! i = (j, k)
     ; before = uf_unions uf_init (take i unions) \<rbrakk>
     \<Longrightarrow> uf_rep_of before j \<noteq> uf_rep_of before k" *)
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

(*
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
*)

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
  note mm_relI[OF mm_invar_au_ds, transfer_rule]
  from ufe_union.hyps have "mm_invar\<^bsub>au_adt\<^esub> (au_ds (ufe_union ufe_ds x y))"
    using mm_invar_au_ds by fastforce
  note mm_relI[OF this, transfer_rule]

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
  assumes "a \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "head (ufa_tree_of (uf_ds ufe_ds) x) a \<in> dom (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds))"
  using assms
proof -
  let ?y = "head (ufa_tree_of (uf_ds ufe_ds) x) a"
  from assms have "?y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
    using head_in_verts by blast
  from assms have "uf_rep_of (uf_ds ufe_ds) ?y \<noteq> ?y"
    by (metis awalk_from_rep_rep_of awlast_awalk_from_rep
        head_in_verts in_arcs_imp_in_arcs_ends
        not_root_if_dominated root_in_verts x_in_verts)
  with lookup_au_ds_eq_None_iff[OF \<open>?y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))\<close>]
  show ?thesis
    unfolding domIff by blast
qed

lemma au_of_lt_length_unions:
  assumes "a \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "au_of a < length (unions ufe_ds)"
  using head_in_dom_lookup_if_in_arcs[OF assms]
  using lookup_au_ds_lt_length_unions
  unfolding au_of_def by force

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

end

end