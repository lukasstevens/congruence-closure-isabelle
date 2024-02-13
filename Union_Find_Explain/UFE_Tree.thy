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

lemma Field_\<alpha>_ufe_union:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "Field (uf_\<alpha> (uf_ds (ufe_union ufe_ds x y))) = Field (uf_\<alpha> (uf_ds ufe_ds))"
  using assms
  by (cases ufe_ds) (auto simp: \<alpha>_union)

lemma invar_ufe_union:
  assumes "uf_invar (uf_ds ufe_ds)"
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  shows "uf_invar (uf_ds (ufe_union ufe_ds x y))"
  using assms
  by (cases ufe_ds) (auto simp: invar_union)

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
      by (cases ufe_ds) simp

    from Cons Pair have valid: "valid_unions (uf_ds (ufe_union ufe_ds u1 u2)) us"
      using valid_union_union by (cases ufe_ds) force

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
    by (cases ufe_ds; cases u) force
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
      by (cases ufe_ds) auto
    moreover from 2 eq_uf_ds' have "eff_unions (uf_ds ?ufe_ds') us"
      by simp
    moreover from 2 have "valid_unions (uf_ds ?ufe_ds') us"
      using valid_unions_ufe_unions_eq[where ?us="[(x, y)]"] by simp
    moreover from 2 have "uf_invar (uf_ds ?ufe_ds')"
      using invar_ufe_union by simp
    ultimately have
      "unions (ufe_unions ?ufe_ds' us) = unions ?ufe_ds' @ us"
      "uf_ds (ufe_unions ?ufe_ds' us)
        = foldl (\<lambda>uf (x, y). uf_union uf x y) (uf_ds ?ufe_ds') us"
      using 2 by blast+
    with "2.prems" show ?case
      by (cases ufe_ds) auto
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

end

locale union_find_explain_ds =
  union_find_explain_invars where uf_adt = uf_adt and au_adt = au_adt
  for uf_adt (structure) and au_adt +

  fixes ufe_ds

  assumes valid_unions:
    "valid_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes eff_unions:
    "eff_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes eq_ufe_unions:
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

lemma valid_unions_ufe_ds:
  "valid_unions (uf_ds ufe_ds) (unions ufe_ds)"
  by (metis eq_ufe_unions uf_invar_ufe_init valid_unions valid_unions_ufe_unions_eq)

sublocale union_find_parent_invar where uf = "uf_ds ufe_ds"
  apply (subst eq_ufe_unions)
  apply (unfold_locales)
  apply (intro invar_ufe_unions uf_invar_ufe_init valid_unions)
  done

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
  
lemma ufe_explain_ds_union:
  assumes "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
  defines "ufe_ds' \<equiv> ufe_union ufe_ds x y"
  shows "union_find_explain_ds uf_adt au_adt ufe_ds'"
proof unfold_locales
  from assms have x_y_in_Field:
    "x \<in> Field (uf_\<alpha> (uf_ds ufe_init))" "y \<in> Field (uf_\<alpha> (uf_ds ufe_init))"
    using valid_unions eq_ufe_unions
    by (metis Field_\<alpha>_ufe_unions uf_invar_ufe_init)+
  with valid_unions show "valid_unions (uf_ds ufe_init) (unions ufe_ds')"
    unfolding ufe_ds'_def by (cases ufe_ds) auto

  show "ufe_ds' = ufe_unions ufe_init (unions ufe_ds')"
    unfolding ufe_ds'_def using eq_ufe_unions
    by (cases ufe_ds; cases "ufe_unions ufe_init (unions ufe_ds)") simp_all

  show "eff_unions (uf_ds ufe_init) (unions ufe_ds')"
  proof(cases "uf_rep_of (uf_ds ufe_ds) x = uf_rep_of (uf_ds ufe_ds) y")
    case True
    then have "unions ufe_ds' = unions ufe_ds"
      by (cases ufe_ds) (simp add: ufe_ds'_def)
    with eff_unions show ?thesis
      by simp
  next
    case False
    from ufp_invar_init.invar_uf have "uf_invar (uf_ds ufe_init)"
      by simp
    from x_y_in_Field have "valid_unions (uf_ds ufe_init) (unions ufe_ds @ [(x, y)])"
      using assms valid_unions by auto
    note eff_unions_uf_ds_append[OF this \<open>uf_invar (uf_ds ufe_init)\<close>]
    with False eff_unions show ?thesis
      unfolding ufe_ds'_def
      by (auto simp: unions_ufe_union_if_rep_of_neq eq_ufe_unions[symmetric])
  qed
qed

lemma ufe_explain_ds_induct:
  assumes "P ufe_init"
  assumes "\<And>ufe_ds x y.
    \<lbrakk> union_find_explain_ds uf_adt au_adt ufe_ds
    ; x \<in> Field (uf_\<alpha> (uf_ds ufe_init)); y \<in> Field (uf_\<alpha> (uf_ds ufe_init))
    ; uf_rep_of (uf_ds ufe_ds) x \<noteq> uf_rep_of (uf_ds ufe_ds) y
    ; P ufe_ds 
    \<rbrakk> \<Longrightarrow> P (ufe_union ufe_ds x y)"
  shows "P ufe_ds"
  using valid_unions eff_unions eq_ufe_unions
proof(induction "unions ufe_ds" arbitrary: ufe_ds rule: rev_induct)
  case (snoc u us)
  let ?ufe_ds0 = "ufe_unions ufe_init us"
  from snoc have valid_unions_ufe_ds0:
    "valid_unions (uf_ds ufe_init) us"
    using valid_unions_append by metis
  from snoc have eff_unions_ufe_ds0:
    "eff_unions (uf_ds ufe_init) us"
    using eff_unions_uf_ds_append ufp_invar_init.invar_uf by metis
  note unions_ufe_unions_eq_if_eff_unions[
      OF eff_unions_ufe_ds0 valid_unions_ufe_ds0 ufp_invar_init.invar_uf]
  then have "unions (ufe_unions ufe_init us) = us"
    by simp

  with snoc.prems valid_unions_ufe_ds0 eff_unions_ufe_ds0
  have ufe_ds_ufe_ds0: "union_find_explain_ds uf_adt au_adt ?ufe_ds0"
    by unfold_locales simp_all

  from snoc have u_in_Field:
    "fst u \<in> Field (uf_\<alpha> (uf_ds ufe_init))"
    "snd u \<in> Field (uf_\<alpha> (uf_ds ufe_init))"
    by (metis valid_unions_Cons valid_unions_append)+

  note eff_unions_uf_ds_append[OF snoc.prems(1)[folded \<open>us @ [u] = unions ufe_ds\<close>]]
  note this[OF uf_invar_ufe_init]
  with snoc.prems(2) have rep_of_neq:
    "uf_rep_of (uf_ds ?ufe_ds0) (fst u) \<noteq> uf_rep_of (uf_ds ?ufe_ds0) (snd u)"
    by (cases u) (fold \<open>us @ [u] = unions ufe_ds\<close>, auto)
    
  from snoc have ufe_ds_eq: "ufe_ds = ufe_union ?ufe_ds0 (fst u) (snd u)"
    by (metis ufe_unions_Cons ufe_unions_Nil ufe_unions_append)
  from snoc valid_unions_ufe_ds0 eff_unions_ufe_ds0 show ?case
    unfolding ufe_ds_eq
    by (intro assms(2)[OF ufe_ds_ufe_ds0 u_in_Field rep_of_neq] snoc.hyps)
      (simp_all add: \<open>unions (ufe_unions ufe_init us) = us\<close>)
qed (use assms(1) in simp)

lemma mm_invar_au_ds: "mm_invar\<^bsub>au_adt\<^esub> (au_ds ufe_ds)"
proof(induction rule: ufe_explain_ds_induct)
  case (2 ufe_ds x y)
  then show ?case
    by (cases ufe_ds) auto
qed simp

lemma valid_au:
  "mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) x = Some i \<Longrightarrow> i < length (unions ufe_ds)"
proof(induction rule: ufe_explain_ds_induct)
  case 1
  then show ?case
    by (simp add: \<alpha>_empty \<alpha>_lookup)
next
  case (2 ufe_ds y z)
  then interpret union_find_explain_ds where ufe_ds = ufe_ds
    by simp

  note mm_relI[OF mm_invar_au_ds, transfer_rule]
  from 2 show ?case
    apply(transfer fixing: ufe_ds)
    sledgehammer
    sorry
qed

end

locale ufe_tree = union_find_explain_ds  +
  fixes x
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (uf_\<alpha> (uf_ds ufe_ds))"
      and finite_eq_class: "\<And>y. finite (uf_\<alpha> (uf_ds ufe_ds) `` {y})"
begin

sublocale ufa_tree where uf = "uf_ds ufe_ds" and x = x
  using invar_uf finite_eq_class
  by unfold_locales blast+

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
  from assms parent_of_refl_iff_rep_of_refl[OF this] have "uf_rep_of (uf_ds ufe_ds) ?y \<noteq> ?y"
    by (metis arc_implies_awalk awalk_and_parent_of_reflD(1) loopfree.no_loops)
  (* note lookup_au_if_not_rep[OF \<open>?y \<in> Field (uf_\<alpha> (uf_ds ufe_ds))\<close> this] *)
  then show ?thesis
    unfolding domIff  by blast
qed

lemma au_of_lt_length_unions:
  assumes "a \<in> arcs (ufa_tree_of uf x)"
  shows "au_of a < length unions"
  using head_in_dom_lookup_if_in_arcs[OF assms] valid_au
  unfolding au_of_def dom_def by simp

lemma inj_on_au_of_arcs:
  "inj_on au_of (arcs (ufa_tree_of uf x))"
  using head_in_dom_lookup_if_in_arcs inj_on_dom_au
  unfolding au_of_def inj_on_def
  by (metis two_in_arcs_contr domIff option.collapse)

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
  shows "newest < length unions"
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
  assumes "unions ! newest = (a, b)"
  shows "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  using newest_on_walk_lt_length_unions[OF assms(1,2)] assms(3)
  using valid_unions_nth_eq_pairD[OF valid_unions_uf]
  by blast+

end

end