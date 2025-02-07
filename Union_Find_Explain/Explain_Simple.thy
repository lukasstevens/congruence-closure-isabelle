theory Explain_Simple
  imports
    "Union_Find.Union_Find"
    "Equality_Proof"
begin

definition "ufa_unions \<equiv> foldl (\<lambda>uf (x, y). ufa_union uf x y)"

lemma
  ufa_unions_Nil[simp]: "ufa_unions uf [] = uf" and
  ufa_unions_Cons[simp]: "ufa_unions uf (u # us) = ufa_unions (ufa_union uf (fst u) (snd u)) us"
  unfolding ufa_unions_def by (simp_all split: prod.splits)

lemma ufa_unions_append:
  "ufa_unions uf (us1 @ us2) = ufa_unions (ufa_unions uf us1) us2"
  by (induction us1 arbitrary: uf) simp_all

definition "valid_union uf a b \<equiv> a \<in> Field (ufa_\<alpha> uf) \<and> b \<in> Field (ufa_\<alpha> uf)"

definition "eff_union uf a b \<equiv> 
  valid_union uf a b \<and> ufa_rep_of uf a \<noteq> ufa_rep_of uf b"

lemma valid_unionI[intro]:
  assumes "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
  shows "valid_union uf a b"
  using assms unfolding valid_union_def by simp

lemma valid_unionD[simp]:
  assumes "valid_union uf a b"
  shows "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
  using assms unfolding valid_union_def by simp_all

lemma valid_unionE[elim]:
  assumes "valid_union uf a b"
  obtains "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
  using assms unfolding valid_union_def by simp

definition "valid_unions uf us \<equiv> \<forall>(x, y) \<in> set us. valid_union uf x y"

lemma valid_unions_Cons_prod[simp]:
  "valid_unions uf (u # us) \<longleftrightarrow>
    valid_union uf (fst u) (snd u) \<and> valid_unions uf us"
  by (cases u) (simp add: valid_unions_def)

lemma valid_unions_append[simp]:
  "valid_unions uf (us1 @ us2) \<longleftrightarrow> valid_unions uf us1 \<and> valid_unions uf us2"
  unfolding valid_unions_def by auto

lemma valid_union_if_in_set_valid_unions:
  assumes "valid_unions uf us"
  assumes "(x, y) \<in> set us"
  shows "valid_union uf x y"
  using assms valid_unions_def by fastforce

lemma subs_Field_if_valid_unions:
  assumes "valid_unions uf us"
  shows "Field (set us) \<subseteq> Field (ufa_\<alpha> uf)"
  using assms unfolding valid_unions_def valid_union_def
  by (auto simp: Field_iff)

lemma eff_unionI[intro]:
  assumes "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of uf a \<noteq> ufa_rep_of uf b"
  shows "eff_union uf a b"
  using assms unfolding eff_union_def valid_union_def by force

lemma eff_unionD[simp, dest?]:
  assumes "eff_union uf a b"
  shows
    "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
    "ufa_rep_of uf a \<noteq> ufa_rep_of uf b"
  using assms unfolding eff_union_def valid_union_def by blast+

lemma eff_unionE[elim]:
  assumes "eff_union uf a b"
  obtains
    "a \<in> Field (ufa_\<alpha> uf)" "b \<in> Field (ufa_\<alpha> uf)"
    "ufa_rep_of uf a \<noteq> ufa_rep_of uf b"
  using assms unfolding eff_union_def valid_union_def by blast

fun eff_unions where
  "eff_unions uf [] \<longleftrightarrow> True"
| "eff_unions uf ((a, b) # us) \<longleftrightarrow> eff_union uf a b \<and> eff_unions (ufa_union uf a b) us"

lemma eff_unions_Cons_prod[simp]:
  "eff_unions uf (u # us) \<longleftrightarrow>
    eff_union uf (fst u) (snd u) \<and> eff_unions (ufa_union uf (fst u) (snd u)) us"
  by (cases u) simp

lemma eff_unions_append:
  "eff_unions uf (us1 @ us2) \<longleftrightarrow> eff_unions uf us1 \<and> eff_unions (ufa_unions uf us1) us2"
  by (induction uf us1 rule: eff_unions.induct) simp_all

lemma eff_unions_butlastI:
  "eff_unions uf us \<Longrightarrow> eff_unions uf (butlast us)"
  by (cases us rule: rev_exhaust) (simp_all add: eff_unions_append)

lemma valid_unions_if_eff_unions:
  assumes "eff_unions uf us"
  shows "valid_unions uf us"
  using assms
  by (induction uf us rule: eff_unions.induct) 
    (use Field_ufa_\<alpha>_ufa_union in \<open>(fastforce simp: valid_unions_def)+\<close>)

lemma in_Field_ufa_\<alpha>_if_in_eff_unions:
  assumes "eff_unions uf us"
  assumes "u \<in> set us"
  shows "fst u \<in> Field (ufa_\<alpha> uf)" "snd u \<in> Field (ufa_\<alpha> uf)"
  using assms
  by (induction uf us rule: eff_unions.induct) auto

lemma Field_ufa_\<alpha>_ufa_unions:
  assumes "valid_unions uf us"
  shows "Field (ufa_\<alpha> (ufa_unions uf us)) = Field (ufa_\<alpha> uf)"
  using assms
  by (induction uf us rule: eff_unions.induct) 
    (use Field_ufa_\<alpha>_ufa_union in \<open>(fastforce simp: valid_unions_def)+\<close>)

lemmas Field_ufa_\<alpha>_ufa_unions_if_eff_unions[simp] =
  Field_ufa_\<alpha>_ufa_unions[OF valid_unions_if_eff_unions]

typedef ufe = "{(ufa_init, us). ufa_\<alpha> ufa_init \<subseteq> Id \<and> eff_unions ufa_init us}"
  by (intro exI[where x="(ufa_init 0, [])"]) (auto simp: ufa_\<alpha>_ufa_init)
setup_lifting type_definition_ufe

lift_definition uf_init_ds :: "ufe \<Rightarrow> ufa" is
  "\<lambda>(ufa_init, us). ufa_init" .

lift_definition unions :: "ufe \<Rightarrow> (nat \<times> nat) list" is
  "\<lambda>(ufa_init, us). us" .

lift_definition uf_ds :: "ufe \<Rightarrow> ufa" is
  "\<lambda>(ufa_init, us). ufa_unions ufa_init us" .

abbreviation "ufe_rep_of ufe_ds x \<equiv> ufa_rep_of (uf_ds ufe_ds) x"
abbreviation "ufe_parent_of ufe_ds x \<equiv> ufa_parent_of (uf_ds ufe_ds) x"
abbreviation "ufe_\<alpha> ufe_ds \<equiv> ufa_\<alpha> (uf_ds ufe_ds)"

lift_definition ufe_init :: "nat \<Rightarrow> ufe" is
  "\<lambda>n. (ufa_init n, [])"
  by (auto simp: ufa_\<alpha>_ufa_init)

lemma unions_ufe_init_eq[simp]:
  "unions (ufe_init n) = []"
  by transfer auto

lemma uf_ds_ufe_init_eq[simp]:
  "uf_ds (ufe_init n) = ufa_init n"
  by transfer auto

lift_definition ufe_union :: "ufe \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe" is
  "\<lambda>(ufa_init, us) x y.
    if eff_unions ufa_init (us @ [(x, y)]) then (ufa_init, us @ [(x, y)])
    else (ufa_init, us)"
  by (auto split: if_splits)

lift_definition rollback :: "ufe \<Rightarrow> ufe" is
  "\<lambda>(ufa_init, us). (ufa_init, butlast us)"
  by (simp add: eff_unions_butlastI split: prod.splits)

lemma uf_init_ds_rollback_eq[simp]:
  "uf_init_ds (rollback ufe) = uf_init_ds ufe"
  by transfer auto

lemma unions_rollback_eq[simp]:
  "unions (rollback ufe) = butlast (unions ufe)"
  by transfer auto

lemma Field_ufe_\<alpha>_rollback_eq[simp]:
  "Field (ufe_\<alpha> (rollback ufe)) = Field (ufe_\<alpha> ufe)"
  by transfer (auto simp: eff_unions_butlastI)

lemma rollback_ufe_union_eq_if_eff_union[simp]:
  assumes "eff_union (uf_ds ufe) x y"
  shows "rollback (ufe_union ufe x y) = ufe"
  using assms
  by transfer (force simp: eff_unions_append)

lemma uf_init_ds_ufe_union[simp]:
  "uf_init_ds (ufe_union ufe x y) = uf_init_ds ufe"
  by transfer auto

lemma unions_ufe_union_eq_if_eff_union[simp]:
  assumes "eff_union (uf_ds ufe) x y"
  shows "unions (ufe_union ufe x y) = unions ufe @ [(x, y)]"
  using assms
  by transfer (force simp: eff_unions_append split: if_splits)

lemma uf_ds_ufe_union_eq:
  "uf_ds (ufe_union ufe x y) =
    (if eff_union (uf_ds ufe) x y then ufa_union (uf_ds ufe) x y
    else uf_ds ufe)"
  by transfer (auto simp: eff_unions_append ufa_unions_append)

lemma uf_ds_ufe_union_eq_if_eff_union:
  assumes "eff_union (uf_ds ufe) x y"
  shows "uf_ds (ufe_union ufe x y) = ufa_union (uf_ds ufe) x y"
  using assms uf_ds_ufe_union_eq by simp

lemma ufe_union_eq_if_ufe_rep_of_eq[simp]:
  assumes "ufe_rep_of ufe x = ufe_rep_of ufe y"
  shows "ufe_union ufe x y = ufe"
  using assms by transfer (auto simp: eff_unions_append)

lemma Field_ufe_\<alpha>_ufe_union_eq[simp]:
  "Field (ufe_\<alpha> (ufe_union ufe x y)) = Field (ufe_\<alpha> ufe)"
  by transfer (auto simp: eff_unions_append split: if_splits)

lemma ufa_\<alpha>_uf_ds_ufe_union_eq_per_union:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  shows "ufe_\<alpha> (ufe_union ufe_ds x y) = per_union (ufe_\<alpha> ufe_ds) x y"
  using assms per_union_cmp[OF part_equiv_ufa_\<alpha>, OF ufa_\<alpha>I]
  apply transfer
  apply (auto simp: eff_unions_append ufa_unions_append split: if_splits)
  by (metis Field_ufa_\<alpha>_ufa_unions_if_eff_unions eff_unionI)

lemma Field_unions_subs_Field_ufe_\<alpha>:
  "Field (set (unions ufe)) \<subseteq> Field (ufe_\<alpha> ufe)"
  using subs_Field_if_valid_unions[OF valid_unions_if_eff_unions]
  by transfer fastforce
  
lemma ufe_induct[case_names init ufe_union]:
  assumes "\<And>ufe. ufe_\<alpha> ufe \<subseteq> Id \<Longrightarrow> unions ufe = [] \<Longrightarrow> P ufe"
  assumes "\<And>ufe x y. \<lbrakk> eff_union (uf_ds ufe) x y; P ufe \<rbrakk>
    \<Longrightarrow> P (ufe_union ufe x y)"
  shows "P ufe"
proof(induction "length (unions ufe)" arbitrary: ufe)
  case 0
  with assms(1) show ?case
    by transfer force
next
  case (Suc n)
  then have "P (rollback ufe)"
    by simp
  moreover from Suc obtain us x y where
    unions_ufe: "unions ufe = us @ [(x, y)]"
    by (cases "unions ufe" rule: rev_exhaust) auto
  moreover from this have
    "x \<in> Field (ufe_\<alpha> (rollback ufe))"
    "y \<in> Field (ufe_\<alpha> (rollback ufe))"
    using Field_unions_subs_Field_ufe_\<alpha> by force+
  moreover from unions_ufe have
    "ufe_rep_of (rollback ufe) x \<noteq> ufe_rep_of (rollback ufe) y"
    by transfer (auto simp: eff_unions_append)
  moreover from calculation have "ufe_union (rollback ufe) x y = ufe"
    by transfer auto
  ultimately show ?case
    using assms(2) eff_unionI by metis
qed

lifting_update ufe.lifting
lifting_forget ufe.lifting

function au_ds :: "ufe \<Rightarrow> (nat \<rightharpoonup> nat)" where
  "au_ds ufe =
    (if unions ufe = [] then Map.empty
    else
      let (x, y) = last (unions ufe); ufe0 = rollback ufe
      in (au_ds ufe0)(ufe_rep_of ufe0 x \<mapsto> length (unions ufe0)))"
  by auto
termination 
  by (relation "measure (\<lambda>ufe. length (unions ufe))") simp_all

declare au_ds.simps[simp del]

lemma au_ds_if_unions_eq_Nil[simp]:
  assumes "unions ufe = []"
  shows "au_ds ufe = Map.empty"
  using assms by (subst au_ds.simps) simp

lemma au_ds_ufe_union_eq_if_eff_union[simp]:
  assumes "eff_union (uf_ds ufe) x y"
  shows "au_ds (ufe_union ufe x y) = (au_ds ufe)(ufe_rep_of ufe x \<mapsto> length (unions ufe))"
  using assms
  by (subst au_ds.simps) simp

function explain :: "ufe \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf" where
  "explain ufe x y =
    (if unions ufe = [] then ReflP x
    else
      let
        ufe0 = rollback ufe;
        (a, b) = last (unions ufe);
        a_b_P = AssmP (length (unions ufe0))
      in
        (if ufe_rep_of ufe0 x = ufe_rep_of ufe0 y then explain ufe0 x y
        else if ufe_rep_of ufe0 x = ufe_rep_of ufe0 a then
          TransP (TransP (explain ufe0 x a) a_b_P) (explain ufe0 b y)
        else
          TransP (TransP (explain ufe0 x b) (SymP a_b_P)) (explain ufe0 a y)))"
  by auto
termination
  by (relation "measure (\<lambda>(ufe, _, _). length (unions ufe))") simp_all

declare explain.simps[simp del]

definition "explain_partial ufe x y \<equiv>
  if (x, y) \<in> equivcl (set (unions ufe)) then Some (explain ufe x y) else None"

lemma explain_refl[simp]:
  "explain ufe x x = ReflP x"
  by (induction ufe rule: ufe_induct) (simp_all add: explain.simps)

lemma per_union_eq_trancl:
  assumes "part_equiv R"
  assumes "x \<in> Field R" "y \<in> Field R"
  shows "per_union R x y = (insert (x, y) (insert (y, x) R))\<^sup>+"
  using assms unfolding part_equiv_def per_union_def
  by (auto simp: trancl_insert2) (meson Field_iff symD transD)+

lemma inverse_insert_prod_eq:
  "(insert (a, b) A)\<inverse> = insert (b, a) (A\<inverse>)"
  by blast

lemma foldl_per_union_eq_trancl:
  assumes "part_equiv R"
  assumes "Field (set us) \<subseteq> Field R"
  shows "foldl (\<lambda>R (x, y). per_union R x y) R us = (R \<union> symcl (set us))\<^sup>+"
  using assms
proof(induction us arbitrary: R rule: rev_induct)
  case Nil
  then show ?case
    unfolding symcl_def by (auto simp: part_equiv_def)
next
  case (snoc u us)
  then obtain a b where "u = (a, b)"
    by force
  from snoc have "foldl (\<lambda>R (x, y). per_union R x y) R us = (R \<union> symcl (set us))\<^sup>+"
    by (metis Field_Un le_sup_iff set_append)
  moreover from snoc have "part_equiv ((R \<union> symcl (set us))\<^sup>+)"
    unfolding part_equiv_def symcl_def
    by (auto intro!: sym_trancl sym_Un[OF _ sym_Un_converse])
  from per_union_eq_trancl[OF this] snoc.prems(2) have
    "per_union ((R \<union> symcl (set us))\<^sup>+) a b =
    (insert (a, b) (insert (b, a) ((R \<union> symcl (set us))\<^sup>+)))\<^sup>+"
    unfolding \<open>u = (a, b)\<close> by (auto simp: Field_iff)
  ultimately show ?case
    unfolding \<open>u = (a, b)\<close> symcl_def
    by (auto simp: Un_assoc inverse_insert_prod_eq trancl_insert2)
qed

lemma ufa_\<alpha>_ufa_unions:
  "ufa_\<alpha> (ufa_unions uf_init us) = foldl (\<lambda>R (x, y). per_union R x y) (ufa_\<alpha> uf_init) us"
  by (induction us arbitrary: uf_init rule: rev_induct) (auto simp: ufa_unions_append)

lemma ufa_rep_of_ufa_unions_eq_if_in_equivcl:
  assumes "valid_unions uf_init us" "(x, y) \<in> equivcl (set us)"
  defines "uf \<equiv> ufa_unions uf_init us"
  shows "ufa_rep_of uf x = ufa_rep_of uf y"
proof(cases "x = y")
  case False
  with subs_Field_if_valid_unions[OF assms(1)] have
    "ufa_\<alpha> (ufa_unions uf_init us) = (ufa_\<alpha> uf_init \<union> symcl (set us))\<^sup>+"
    using foldl_per_union_eq_trancl[OF part_equiv_ufa_\<alpha>] ufa_\<alpha>_ufa_unions
    using subs_Field_if_valid_unions by blast
  moreover from False assms have "(x, y) \<in> (ufa_\<alpha> uf_init \<union> symcl (set us))\<^sup>+"
    unfolding equivcl_def
    by (metis in_rtrancl_UnI rtranclD)
  ultimately show ?thesis
    unfolding uf_def
    by (intro ufa_rep_of_eq_if_in_ufa_\<alpha>) simp
qed simp

lemma in_Field_ufa_\<alpha>_if_in_equivcl:
  assumes "valid_unions uf_init us"
  assumes "(x, y) \<in> equivcl (set us)" "x \<noteq> y"
  shows "x \<in> Field (ufa_\<alpha> uf_init)" "y \<in> Field (ufa_\<alpha> uf_init)"
  using assms subs_Field_if_valid_unions in_Field_if_in_equivcl
  by fast+

context
  fixes uf_init us
  assumes valid_unions: "valid_unions uf_init us"
  assumes ufa_\<alpha>_uf_init: "ufa_\<alpha> uf_init \<subseteq> Id"
begin

lemma ufa_rep_of_ufa_unions_neq_if_not_in_equivcl:
  assumes "(x, y) \<notin> equivcl (set us)"
  defines "uf \<equiv> ufa_unions uf_init us"
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  shows "ufa_rep_of uf x \<noteq> ufa_rep_of uf y"
  using assms valid_unions
proof(induction us arbitrary: x y uf rule: rev_induct)
  case Nil
  with ufa_\<alpha>_uf_init show ?case
    unfolding equivcl_def symcl_def by (auto intro!: ufa_\<alpha>I)
next
  case (snoc u us)
  then have "(x, y) \<notin> equivcl (set us)"
    using equivcl_mono by (metis in_mono set_append sup_ge1)
  with snoc have ufa_rep_of_neq:
    "ufa_rep_of (ufa_unions uf_init us) x \<noteq> ufa_rep_of (ufa_unions uf_init us) y"
    using Field_ufa_\<alpha>_ufa_unions by force
  show ?case
  proof(rule notI)
    assume 
      "ufa_rep_of (ufa_unions uf_init (us @ [u])) x =
      ufa_rep_of (ufa_unions uf_init (us @ [u])) y"
    moreover from snoc have in_Field_ufa_\<alpha>:
      "x \<in> Field (ufa_\<alpha> (ufa_unions uf_init us))"
      "y \<in> Field (ufa_\<alpha> (ufa_unions uf_init us))"
      "fst u \<in> Field (ufa_\<alpha> (ufa_unions uf_init us))"
      "snd u \<in> Field (ufa_\<alpha> (ufa_unions uf_init us))"
      using Field_ufa_\<alpha>_ufa_unions by auto
    ultimately consider
      "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) (fst u)"
      "ufa_rep_of (ufa_unions uf_init us) y = ufa_rep_of (ufa_unions uf_init us) (snd u)" |
      "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) (snd u)"
      "ufa_rep_of (ufa_unions uf_init us) y = ufa_rep_of (ufa_unions uf_init us) (fst u)"
      using ufa_rep_of_neq
      by (auto simp: ufa_rep_of_ufa_union ufa_unions_append split: if_splits)
    then show False
    proof cases
      case 1
      with snoc in_Field_ufa_\<alpha> have
        "(x, fst u) \<in> equivcl (set us)" "(snd u, y) \<in> equivcl (set us)"
        using Field_ufa_\<alpha>_ufa_unions by fastforce+
      then have "(x, y) \<in> equivcl (set (us @ [u]))"
        unfolding equivcl_def
        by (cases u) (auto simp: rtrancl_insert symcl_insert)
      with snoc show False
        by blast
   next
     case 2
      with snoc in_Field_ufa_\<alpha> have
        "(x, snd u) \<in> equivcl (set us)" "(fst u, y) \<in> equivcl (set us)"
        using Field_ufa_\<alpha>_ufa_unions by fastforce+
      then have "(x, y) \<in> equivcl (set (us @ [u]))"
        unfolding equivcl_def
        by (cases u) (auto simp: rtrancl_insert symcl_insert)
      with snoc show False
        by blast
    qed
  qed
qed

lemma in_equivcl_iff_eq_or_ufa_rep_of_eq:
  defines "uf \<equiv> ufa_unions uf_init us"
  shows "(x, y) \<in> equivcl (set us) \<longleftrightarrow>
    x = y \<or> x \<in> Field (ufa_\<alpha> uf) \<and> y \<in> Field (ufa_\<alpha> uf) \<and> ufa_rep_of uf x = ufa_rep_of uf y"
  using ufa_rep_of_ufa_unions_eq_if_in_equivcl[OF valid_unions]
  using ufa_rep_of_ufa_unions_neq_if_not_in_equivcl
  using in_Field_ufa_\<alpha>_if_in_equivcl[OF valid_unions]
  by (auto simp: uf_def Field_ufa_\<alpha>_ufa_unions[OF valid_unions])

end

lemma in_equivcl_iff_eq_or_ufe_rep_of_eq:
  "(x, y) \<in> equivcl (set (unions ufe)) \<longleftrightarrow>
    x = y \<or>
    x \<in> Field (ufe_\<alpha> ufe) \<and> y \<in> Field (ufe_\<alpha> ufe) \<and> ufe_rep_of ufe x = ufe_rep_of ufe y"
  using in_equivcl_iff_eq_or_ufa_rep_of_eq including ufe.lifting
  by transfer (fastforce intro: valid_unions_if_eff_unions)

lemma ufe_rep_of_eq_if_in_equivcl_unions:
  assumes "(x, y) \<in> equivcl (set (unions ufe))"
  shows "ufe_rep_of ufe x = ufe_rep_of ufe y"
  using assms in_equivcl_iff_eq_or_ufe_rep_of_eq by metis

lemma ufe_rep_of_neq_if_not_in_equivcl_unions:
  assumes "(x, y) \<notin> equivcl (set (unions ufe))"
  assumes "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  shows "ufe_rep_of ufe x \<noteq> ufe_rep_of ufe y"
  using assms in_equivcl_iff_eq_or_ufe_rep_of_eq by metis

theorem explain_complete:
  assumes "(x, y) \<in> equivcl (set (unions ufe))"
  shows "unions ufe \<turnstile>\<^sub>= explain ufe x y : (x, y)"
  using assms
proof(induction ufe arbitrary: x y rule: ufe_induct)
  case (init ufe)
  then have "x = y"
    using ufa_rep_of_eq_iff_in_ufa_\<alpha> unfolding equivcl_def symcl_def by auto
  then show ?case
    using proves_eq.refl explain_refl by fastforce
next
  case (ufe_union ufe a b)
  show ?case
  proof(cases "(x, y) \<in> equivcl (set (unions ufe))")
    case True
    moreover from ufe_union True have
      "ufe_rep_of ufe x = ufe_rep_of ufe y"
      by (intro ufe_rep_of_eq_if_in_equivcl_unions) simp
    ultimately show ?thesis
      using ufe_union
      by (subst explain.simps) (auto simp: Let_def weaken_proves_eq)
  next
    case False
    with ufe_union have
      "x \<in> Field (ufe_\<alpha> (ufe_union ufe a b))" "y \<in> Field (ufe_\<alpha> (ufe_union ufe a b))"
      using Field_unions_subs_Field_ufe_\<alpha> in_Field_if_in_equivcl
      by fast+
    with ufe_union False have ufe_rep_of_neq:
      "ufe_rep_of ufe x \<noteq> ufe_rep_of ufe y"
      by (intro ufe_rep_of_neq_if_not_in_equivcl_unions) auto

    from ufe_union False consider
      "(x, a) \<in> equivcl (set (unions ufe))" "(b, y) \<in> equivcl (set (unions ufe))" |
      "(x, b) \<in> equivcl (set (unions ufe))" "(a, y) \<in> equivcl (set (unions ufe))"
      unfolding equivcl_def symcl_def
      by (auto simp: rtrancl_insert inverse_insert_prod_eq intro: rtrancl_trans)
    then show ?thesis
    proof cases
      case 1
      moreover from this ufe_union have
        "ufe_rep_of ufe x = ufe_rep_of ufe a"
        "ufe_rep_of ufe y = ufe_rep_of ufe b"
        by (simp_all add: ufe_rep_of_eq_if_in_equivcl_unions)
      moreover note proves_eq_a_b = proves_eq.assm[where i = "length (unions ufe)"]
      from ufe_union 1 have
        "unions (ufe_union ufe a b) \<turnstile>\<^sub>= explain ufe x a : (x, a)"
        "unions (ufe_union ufe a b) \<turnstile>\<^sub>= explain ufe b y : (b, y)"
        using weaken_proves_eq[where bs="[(a, b)]"]
        by force+
      note proves_eq.trans[OF proves_eq.trans[OF this(1) proves_eq_a_b] this(2)]
      ultimately show ?thesis
        using ufe_union.prems ufe_union.hyps False ufe_rep_of_neq
        by (subst explain.simps) (simp add: Let_def)
    next
      case 2
      moreover from this ufe_union have
        "ufe_rep_of ufe x = ufe_rep_of ufe b"
        "ufe_rep_of ufe y = ufe_rep_of ufe a"
        by (simp_all add: ufe_rep_of_eq_if_in_equivcl_unions)
      moreover note proves_eq_a_b = proves_eq.assm[where i = "length (unions ufe)"]
      from ufe_union 2 have
        "unions (ufe_union ufe a b) \<turnstile>\<^sub>= explain ufe x b : (x, b)"
        "unions (ufe_union ufe a b) \<turnstile>\<^sub>= explain ufe a y : (a, y)"
        using weaken_proves_eq[where bs="[(a, b)]"]
        by force+
      note proves_eq.trans[OF proves_eq.trans[OF this(1) proves_eq.sym[OF proves_eq_a_b]] this(2)]
      ultimately show ?thesis
        using ufe_union.prems ufe_union.hyps False ufe_rep_of_neq
        by (subst explain.simps) (simp add: Let_def)
    qed
  qed
qed

theorem explain_partial_sound:
  assumes "explain_partial ufe x y = Some p"
  shows "unions ufe \<turnstile>\<^sub>= p : (x, y)"
  using assms explain_complete unfolding explain_partial_def
  by (cases "(x, y) \<in> equivcl (set (unions ufe))") auto

theorem explain_partial_complete:
  assumes "explain_partial ufe x y = None"
  shows "\<not> unions ufe \<turnstile>\<^sub>= p : (x, y)"
  using assms proves_eq_sound unfolding explain_partial_def by force

end