theory UFE_Tree
  imports Explain_Definition
begin

definition "ufa_unions \<equiv> foldl (\<lambda>uf (x, y). ufa_union uf x y)"

lemma
  ufa_unions_Nil[simp]: "ufa_unions uf [] = uf" and
  ufa_unions_Cons[simp]: "ufa_unions uf (u # us) = ufa_unions (ufa_union uf (fst u) (snd u)) us"
  unfolding ufa_unions_def by (simp_all split: prod.splits)

lemma ufa_unions_append:
  "ufa_unions uf (us1 @ us2) = ufa_unions (ufa_unions uf us1) us2"
  by (induction us1 arbitrary: uf) simp_all

definition valid_unions :: "ufa \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
  "valid_unions uf us \<equiv> \<forall>(x, y) \<in> set us. x \<in> Field (ufa_\<alpha> uf) \<and> y \<in> Field (ufa_\<alpha> uf)"

lemma valid_unions_Nil[simp]:
  "valid_unions uf []"
  unfolding valid_unions_def by simp

lemma valid_unions_Cons[simp]:
  "valid_unions uf (x # xs) \<longleftrightarrow>
    fst x \<in> Field (ufa_\<alpha> uf) \<and> snd x \<in> Field (ufa_\<alpha> uf) \<and> valid_unions uf xs"
  unfolding valid_unions_def by (simp split: prod.splits)

lemma valid_unions_append[simp]:
  "valid_unions uf (xs @ ys) \<longleftrightarrow> valid_unions uf xs \<and> valid_unions uf ys"
  unfolding valid_unions_def by auto

lemma valid_unions_takeI[simp, intro]:
  "valid_unions uf us \<Longrightarrow> valid_unions uf (take i us)"
  unfolding valid_unions_def using in_set_takeD by fast

lemma valid_union_union[simp]:
  "valid_unions (ufa_union uf x y) us \<longleftrightarrow> valid_unions uf us"
  by (induction us) auto

lemma valid_unions_induct[consumes 1, case_names init union]:
  assumes "valid_unions uf us"
  assumes "P uf"
  assumes "\<And>uf x y.
    \<lbrakk>  x \<in> Field (ufa_\<alpha> uf); y \<in> Field (ufa_\<alpha> uf) ; P uf \<rbrakk>
    \<Longrightarrow> P (ufa_union uf x y)"
  shows "P (ufa_unions uf us)"
  using assms(1,2)
  by (induction us arbitrary: uf) (use assms(3) in simp_all)

lemma Field_ufa_\<alpha>_ufa_unions[simp]:
  assumes "valid_unions uf us"
  shows "Field (ufa_\<alpha> (ufa_unions uf us)) = Field (ufa_\<alpha> uf)"
  using assms
  by (induction rule: valid_unions_induct) simp_all

lemma valid_union_unions[simp]:
  assumes "valid_unions uf us"
  shows "valid_unions (ufa_unions uf us) ous \<longleftrightarrow> valid_unions uf ous"
  using assms Field_ufa_\<alpha>_ufa_unions unfolding valid_unions_def by simp

lemma ufa_\<alpha>_uf_ds_ufe_unions_eq_ufa_\<alpha>_ufa_unions_uf_ds:
  assumes "valid_unions (uf_ds ufe_ds) us"
  shows "ufa_\<alpha> (uf_ds (ufe_unions ufe_ds us)) = ufa_\<alpha> (ufa_unions (uf_ds ufe_ds) us)"
  using assms
proof(induction us rule: rev_induct)
  case (snoc u us)
  then show ?case
    by (cases u) (auto simp: ufa_\<alpha>_uf_ds_ufe_union_eq_per_union ufa_unions_append)
qed simp

fun eff_unions where
  "eff_unions uf [] \<longleftrightarrow> True"
| "eff_unions uf ((x, y) # us) \<longleftrightarrow>
    ufa_rep_of uf x \<noteq> ufa_rep_of uf y \<and> eff_unions (ufa_union uf x y) us"

lemma eff_unions_append:
  assumes "valid_unions uf (us1 @ us2)"
  shows "eff_unions uf (us1 @ us2) \<longleftrightarrow>
    eff_unions uf us1 \<and> eff_unions (ufa_unions uf us1) us2"
  using assms
proof(induction us1 arbitrary: uf)
  case Nil
  then show ?case
    by simp
next
  case (Cons u1 us1)
  let ?uf' = "ufa_union uf (fst u1) (snd u1)"
  from Cons have "valid_unions ?uf' (us1 @ us2)"
    by (simp add: valid_unions_def)
  from Cons.IH[OF this] show ?case
    by (cases u1) simp
qed

(*
lemma uf_ds_ufe_unions_eq_unions:
  assumes "eff_unions uf us"
  assumes "valid_unions uf us"
  assumes "uf_ds ufe_ds = uf"
  shows "uf_ds (ufe_unions ufe_ds us) = ufa_unions uf us"
  using assms
proof(induction uf us arbitrary: ufe_ds rule: eff_unions.induct)
  case (2 uf x y us)
  then have "uf_ds (ufe_union ufe_ds x y) = ufa_union uf x y"
    by simp
  note "2.IH"[OF _ _ this]
  with "2.prems" have
    "uf_ds (ufe_unions (ufe_union ufe_ds x y) us) = ufa_unions (ufa_union uf x y) us"
    by simp
  then show ?case
    by simp
qed simp

lemma unions_ufe_unions_eq_unions_append:
  assumes "eff_unions uf us"
  assumes "valid_unions uf us"
  assumes "uf_ds ufe_ds = uf"
  shows "unions (ufe_unions ufe_ds us) = unions ufe_ds @ us"
  using assms
proof(induction uf us arbitrary: ufe_ds rule: eff_unions.induct)
  case (2 uf x y us)
  from 2 have "uf_ds (ufe_union ufe_ds x y) = ufa_union uf x y"
    by simp
  note "2.IH"[OF _ _ this]
  with "2.prems" have
    "unions (ufe_unions (ufe_union ufe_ds x y) us) =
    unions (ufe_union ufe_ds x y) @ us"
    by simp
  with 2 show ?case
    by simp
qed simp
*)

locale ufe_init_invars =
  fixes ufe_init

  assumes ufa_\<alpha>_uf_ds_ufe_init:
    "ufa_\<alpha> (uf_ds ufe_init) \<subseteq> Id"
  assumes au_ds_ufe_init[simp]:
    "au_ds ufe_init = Map.empty"
  assumes unions_ufe_init[simp]:
    "unions ufe_init = []"
begin

lemma in_ufa_\<alpha>_uf_ds_ufe_init[simp]:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_init))"
  shows "(x, x) \<in> ufa_\<alpha> (uf_ds ufe_init)"
  using assms ufa_\<alpha>_uf_ds_ufe_init ufa_\<alpha>I by blast

lemma ufe_rep_of_ufe_init:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_init))"
  shows "ufe_rep_of ufe_init x = x"
  using assms ufa_\<alpha>_uf_ds_ufe_init ufa_rep_of_eq_iff_in_ufa_\<alpha> by fastforce

end

locale ufe_invars = ufe_init_invars +
  fixes ufe_ds

  assumes valid_unions:
    "valid_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes eff_unions:
    "eff_unions (uf_ds ufe_init) (unions ufe_ds)"
  assumes ufe_ds_eq_ufe_unions:
    "ufe_ds = ufe_unions ufe_init (unions ufe_ds)"
begin

lemma ufe_ds_induct[case_names ufe_init ufe_union]:
  assumes "P ufe_init"
  assumes "\<And>ufe_ds x y.
    \<lbrakk> ufe_invars ufe_init ufe_ds
    ; x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)); y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))
    ; ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y
    ; some_pair x y = (x, y)
    ; P ufe_ds 
    \<rbrakk> \<Longrightarrow> P (ufe_union ufe_ds x y)"
  shows "P ufe_ds"
  using valid_unions eff_unions ufe_ds_eq_ufe_unions
proof(induction "unions ufe_ds" arbitrary: ufe_ds rule: rev_induct)
  case (snoc u us)
  let ?ufe_ds0 = "ufe_unions ufe_init us"

  from snoc have "ufa_\<alpha> (uf_ds ?ufe_ds0) = ufa_\<alpha> (ufa_unions (uf_ds ufe_init) us)"
    by (metis ufa_\<alpha>_uf_ds_ufe_unions_eq_ufa_\<alpha>_ufa_unions_uf_ds valid_unions_append)
  moreover from this have valid_union_u:
    "fst u \<in> Field (ufa_\<alpha> (uf_ds (ufe_unions ufe_init us)))"
    "snd u \<in> Field (ufa_\<alpha> (uf_ds (ufe_unions ufe_init us)))"
    using snoc.prems \<open>us @ [u] = unions ufe_ds\<close>[symmetric] by simp_all
  moreover from snoc have "ufa_rep_of (ufa_unions (uf_ds ufe_init) us) (fst u) \<noteq>
    ufa_rep_of (ufa_unions (uf_ds ufe_init) us) (snd u)"
    by (metis eff_unions.simps(2) eff_unions_append prod.collapse)
  ultimately have eff_union_u:
    "ufe_rep_of (ufe_unions ufe_init us) (fst u) \<noteq>
    ufe_rep_of (ufe_unions ufe_init us) (snd u)"
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
    "valid_unions (uf_ds ufe_init) (unions ?ufe_ds0)"
    "eff_unions (uf_ds ufe_init) (unions ?ufe_ds)"
    by (simp_all add: eff_unions_append)
  ultimately have "P ?ufe_ds0"
    using snoc.hyps(1) by blast

  moreover have "ufe_invars ufe_init ?ufe_ds0"
    using \<open>us = unions ?ufe_ds0\<close>
    using \<open>valid_unions (uf_ds ufe_init) (unions ?ufe_ds0)\<close>
    using \<open>eff_unions (uf_ds ufe_init) (unions ?ufe_ds0)\<close>
    by unfold_locales simp_all

  ultimately have "P (ufe_union ?ufe_ds0 (fst u) (snd u))"
    using \<open>unions (ufe_union ?ufe_ds0 (fst u) (snd u)) = us @ [u]\<close>
    using valid_union_u eff_union_u assms(2)
    by (simp add: case_prod_unfold)

  then show ?case
    using \<open>ufe_ds = ufe_union ?ufe_ds0 (fst u) (snd u)\<close> by blast
qed (use assms(1) in simp)

lemma uf_ds_ufe_ds_eq_ufa_unions:
  "uf_ds ufe_ds = ufa_unions (uf_ds ufe_init) (unions ufe_ds)"
  by (induction rule: ufe_ds_induct) (simp_all add: ufa_unions_def)

lemma in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init:
  shows "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds)) \<longleftrightarrow> x \<in> Field (ufa_\<alpha> (uf_ds ufe_init))"
  using uf_ds_ufe_ds_eq_ufa_unions valid_unions by simp

lemma ufe_invars_ufe_union:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  defines "ufe_ds' \<equiv> ufe_union ufe_ds x y"
  shows "ufe_invars ufe_init ufe_ds'"
proof unfold_locales
  from assms have x_y_in_Field:
    "x \<in> Field (ufa_\<alpha> (uf_ds ufe_init))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_init))"
    using in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init by simp_all
  with valid_unions show "valid_unions (uf_ds ufe_init) (unions ufe_ds')"
    unfolding ufe_ds'_def ufe_union_sel
    by (cases x y rule: some_pair_cases) auto

  show "ufe_ds' = ufe_unions ufe_init (unions ufe_ds')"
    unfolding ufe_ds'_def using ufe_ds_eq_ufe_unions
    by (cases x y rule: some_pair_cases) (simp_all add: ufe_union_sel ufe_union_commute)

  show "eff_unions (uf_ds ufe_init) (unions ufe_ds')"
  proof(cases "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y")
    case True
    then have "unions ufe_ds' = unions ufe_ds"
      by (simp add: ufe_union_sel ufe_ds'_def)
    with eff_unions show ?thesis
      by simp
  next
    case False
    from x_y_in_Field have "valid_unions (uf_ds ufe_init) (unions ufe_ds @ [(x, y)])"
      using assms valid_unions by auto
    note eff_unions_append[OF this]
    with False eff_unions \<open>valid_unions (uf_ds ufe_init) (unions ufe_ds')\<close>  show ?thesis
      unfolding ufe_ds'_def using uf_ds_ufe_ds_eq_ufa_unions
      by (cases x y rule: some_pair_cases) (fastforce simp: eff_unions_append)+
  qed
qed
                   
lemma lookup_au_ds_lt_length_unions:
  "au_ds ufe_ds x = Some i \<Longrightarrow> i < length (unions ufe_ds)"
proof(induction rule: ufe_ds_induct)
  case (ufe_union ufe_ds y z)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by simp
  from ufe_union show ?case
    unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
    by (auto simp: less_SucI split: if_splits)
qed simp

lemma dom_au_ds_subs_Field_ufa_\<alpha>:
  "dom (au_ds ufe_ds) \<subseteq> Field (ufa_\<alpha> (uf_ds ufe_ds))"
proof(induction rule: ufe_ds_induct)
  case (ufe_union ufe_ds y z)
  then interpret ufe_invars where ufe_ds = ufe_ds
    by simp
  from ufe_union show ?case
    unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)] Field_ufa_\<alpha>_ufa_union
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
      by (intro ufe_invars_ufe_union)

    from ufe_union.prems have "(a, b) \<in> set (unions (ufe_union ufe_ds y z))"
      by (metis nth_mem ufe_invars_union.lookup_au_ds_lt_length_unions)
    with ufe_invars_union.valid_unions have
      a_in_Field_\<alpha>: "a \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" and
      b_in_Field_\<alpha>: "b \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
      unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
      unfolding in_Field_uf_ds_iff_in_Field_uf_ds_ufe_init
      by (auto simp: valid_unions_def)
    from ufe_union have x_in_Field_\<alpha>: "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
      using ufe_invars_union.dom_au_ds_subs_Field_ufa_\<alpha>
      using Field_ufa_\<alpha>_uf_ds_ufe_union by blast

    show ?case
    proof(cases "i < length (unions ufe_ds)")
      case False

      note ufe_invars_union.lookup_au_ds_lt_length_unions[OF ufe_union.prems(1)]
      with False ufe_union.hyps(4) have "i = length (unions ufe_ds)"
        by simp
      moreover from calculation have "au_ds ufe_ds x \<noteq> Some i"
        using lookup_au_ds_lt_length_unions by blast
      ultimately show ?thesis
        using ufe_union.prems ufe_union.hyps(2-4) a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)] \<open>some_pair y z = (y, z)\<close>
        by (simp add: ufa_rep_of_ufa_union) (metis ufa_rep_of_ufa_rep_of)
    next
      case True
      with ufe_union.prems ufe_union.hyps have "au_ds ufe_ds x = Some i"
        unfolding ufe_union_sel_if_rep_of_neq[OF "ufe_union.hyps"(4)]
        by (simp split: if_splits)
      moreover from True ufe_union.hyps(4) have "unions (ufe_union ufe_ds y z) ! i = unions ufe_ds ! i"
        by (simp add: nth_append)
      ultimately show ?thesis
        using a_in_Field_\<alpha> b_in_Field_\<alpha> x_in_Field_\<alpha>
        using ufe_union.IH ufe_union.hyps(2-5) ufe_union.prems(2)
        by (force simp: ufa_rep_of_ufa_union)+
    qed
  qed
  then show
    "ufe_rep_of ufe_ds a = ufe_rep_of ufe_ds x"
    "ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds x"
    by blast+
qed

lemma lookup_au_ds_eq_None_iff:
  assumes "z \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
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
    unfolding ufe_union_sel_if_rep_of_neq[OF ufe_union.hyps(4)]
    by (simp_all add: ufa_rep_of_ufa_union) (metis ufa_rep_of_ufa_rep_of)
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
  assumes x_in_Field_\<alpha>[simp, intro]: "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
begin

sublocale ufa_tree where uf = "uf_ds ufe_ds" and x = x
  using x_in_Field_\<alpha> valid_unions
  by unfold_locales

context
  fixes a b
  assumes a_b_in_Field_\<alpha>: "a \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "b \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
begin

interpretation ufe_invars_union: ufe_invars where ufe_ds = "ufe_union ufe_ds a b"
  using a_b_in_Field_\<alpha> ufe_invars_ufe_union by blast

interpretation ufe_tree_union: ufe_tree where
  ufe_ds = "ufe_union ufe_ds a b" and x = x
  using Field_ufa_\<alpha>_uf_ds_ufe_union[OF a_b_in_Field_\<alpha>]
  by unfold_locales blast

lemma in_verts_ufa_tree_of_ufe_union_if_in_verts[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "y \<in> verts (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x)"
  using assms a_b_in_Field_\<alpha> 
  using in_verts_ufa_tree_of_union_if_in_verts
  by (cases a b rule: some_pair_cases) (auto simp: ufe_union_sel)

lemma in_arcs_ufa_tree_of_ufe_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "e \<in> arcs (ufa_tree_of (uf_ds (ufe_union ufe_ds a b)) x)"
  using assms a_b_in_Field_\<alpha> 
  using in_arcs_ufa_tree_of_union_if_in_arcs
  by (cases a b rule: some_pair_cases) (auto simp: ufe_union_sel)

lemma ufe_union_awalk_if_awalk:
  assumes "awalk y p z"
  shows "ufe_tree_union.awalk y p z"
  using assms a_b_in_Field_\<alpha> union_awalk_if_awalk
  by (cases a b rule: some_pair_cases) (auto simp: ufe_union_sel)

lemma awalk_if_ufe_union_awalk:
  assumes "ufe_tree_union.awalk x p y"
  assumes "ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y"
  shows "awalk x p y"
proof (cases a b rule: some_pair_cases)
  case 1
  with awalk_if_union_awalk[OF a_b_in_Field_\<alpha> _ assms(2)] assms(1) show ?thesis
    by (simp add: ufe_union_sel  split: if_splits)
next
  case 2
  with awalk_if_union_awalk[OF a_b_in_Field_\<alpha>(2,1) _ assms(2)] assms(1) show ?thesis
    by (simp add: ufe_union_sel split: if_splits)
qed

end

definition "au_of a \<equiv> the (au_ds ufe_ds (head (ufa_tree_of (uf_ds ufe_ds) x) a))"

lemma head_in_dom_lookup_if_in_arcs:
  assumes "e \<in> arcs (ufa_tree_of (uf_ds ufe_ds) x)"
  shows "head (ufa_tree_of (uf_ds ufe_ds) x) e \<in> dom (au_ds ufe_ds)"
  using assms
proof -
  from assms have
    "head (ufa_tree_of (uf_ds ufe_ds) x) e \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" (is "?a \<in> _")
    using head_in_verts by blast
  moreover from assms have "ufe_rep_of ufe_ds ?a \<noteq> ?a"
    using adj_in_verts(2) not_root_if_dominated by (cases e) fastforce
  ultimately obtain i where "au_ds ufe_ds ?a = Some i"
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
    "au_ds ufe_ds (head (ufa_tree_of (uf_ds ufe_ds) x) e) = Some (au_of e)"
    unfolding au_of_def by auto
  from ufe_rep_of_eq_if_au[OF this assms(2)] assms(1) show
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
    by (intro inj_au_ds[THEN inj_onD]) (auto simp: au_of_def)
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
  shows "a \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "b \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
proof -
  from assms have "(a, b) \<in> set (unions ufe_ds)"
    using newest_on_walk_lt_length_unions by (metis nth_mem)
  then show "a \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "b \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
    using uf_ds_ufe_ds_eq_ufa_unions valid_unions valid_unions_def by auto
qed

lemma ufe_rep_of_eq_if_newest_on_walk:
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