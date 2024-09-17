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

lemma valid_unionD[simp, dest?]:
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

context
  fixes uf_init :: ufa
begin

function explain :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf" where
  "explain [] x _ = ReflP x"
| "explain (us @ [(a, b)]) x y =
    (let
      uf = ufa_unions uf_init us;
      a_b_P = AssmP (length us)
    in
      (if ufa_rep_of uf x = ufa_rep_of uf y then explain us x y
      else if ufa_rep_of uf x = ufa_rep_of uf a then
        TransP (TransP (explain us x a) a_b_P) (explain us b y)
      else
        TransP (TransP (explain us x b) (SymP a_b_P)) (explain us a y))
    )"
  by (metis prod.exhaust rev_exhaust, simp_all)
termination by (relation "measure (\<lambda>(us, _, _). size us)") auto

definition "explain_partial us x y \<equiv>
  if (x, y) \<in> equivcl (set us) then Some (explain us x y) else None"

lemma explain_refl[simp]:
  "explain us x x = ReflP x"
proof(induction "size us" arbitrary: us)
  case 0
  then show ?case
    by simp
next
  case (Suc l)
  then show ?case
    by (cases "(us, x, x)" rule: explain.cases) auto
qed

end

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
  assumes "valid_unions uf_init us"
  assumes "(x, y) \<in> equivcl (set us)"
  defines "uf \<equiv> ufa_unions uf_init us"
  shows "ufa_rep_of uf x = ufa_rep_of uf y"
proof(cases "x = y")
  case False
  note subs_Field_if_valid_unions[OF assms(1)]
  with assms have
    "ufa_\<alpha> (ufa_unions uf_init us) = (ufa_\<alpha> uf_init \<union> symcl (set us))\<^sup>+"
    using foldl_per_union_eq_trancl[OF part_equiv_ufa_\<alpha>] ufa_\<alpha>_ufa_unions
    by blast
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

theorem explain_complete:
  assumes "(x, y) \<in> equivcl (set us)"
  shows "us \<turnstile>\<^sub>= explain uf_init us x y : (x, y)"
  using assms valid_unions
proof(induction us arbitrary: x y rule: rev_induct)
  case Nil
  then have "x = y"
    using ufa_rep_of_eq_iff_in_ufa_\<alpha> unfolding equivcl_def symcl_def by auto
  then show ?case
    using proves_eq.refl by force
next
  case (snoc u us)
  then obtain a b where u:
    "u = (a, b)" "valid_unions uf_init us" 
    "a \<in> Field (ufa_\<alpha> (ufa_unions uf_init us))"
    "b \<in> Field (ufa_\<alpha> (ufa_unions uf_init us))"
    by (cases u) (auto simp: Field_ufa_\<alpha>_ufa_unions)

  from snoc.prems have
    "ufa_rep_of (ufa_unions uf_init (us @ [u])) x =
    ufa_rep_of (ufa_unions uf_init (us @ [u])) y"
    by (intro ufa_rep_of_ufa_unions_eq_if_in_equivcl)

  show ?case
  proof(cases "(x, y) \<in> equivcl (set us)")
    case True
    with snoc.prems \<open>valid_unions uf_init us\<close> have
      "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) y"
      by (intro ufa_rep_of_ufa_unions_eq_if_in_equivcl)
    moreover from True snoc u have "us \<turnstile>\<^sub>= explain uf_init us x y : (x, y)"
      by simp
    ultimately show ?thesis
      unfolding \<open>u = (a, b)\<close>
      by (simp add: weaken_proves_eq Let_def)
  next
    case False
    with snoc u have ufa_rep_of_neq:
      "ufa_rep_of (ufa_unions uf_init us) x \<noteq> ufa_rep_of (ufa_unions uf_init us) y"
      using Explain_Simple.in_equivcl_iff_eq_or_ufa_rep_of_eq
      by (metis Field_ufa_\<alpha>_ufa_unions ufa_\<alpha>_uf_init)

    from False snoc.prems u consider
      "(x, a) \<in> equivcl (set us)" "(b, y) \<in> equivcl (set us)" |
      "(x, b) \<in> equivcl (set us)" "(a, y) \<in> equivcl (set us)"
      unfolding equivcl_def symcl_def
      by (auto simp: rtrancl_insert inverse_insert_prod_eq intro: rtrancl_trans)
    then show ?thesis
    proof cases
      case 1
      with snoc.prems u have
        "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) a"
        "ufa_rep_of (ufa_unions uf_init us) y = ufa_rep_of (ufa_unions uf_init us) b"
        using ufa_rep_of_ufa_unions_eq_if_in_equivcl
        by simp_all
      moreover note proves_eq_a_b = proves_eq.assm[where i = "length us"]
      from 1 snoc u have
        "us @ [u] \<turnstile>\<^sub>= explain uf_init us x a : (x, a)"
        "us @ [u] \<turnstile>\<^sub>= explain uf_init us b y : (b, y)"
        using weaken_proves_eq[where as=us and bs="[u]"] by force+
      note proves_eq.trans[OF proves_eq.trans[OF this(1) proves_eq_a_b] this(2)]
      ultimately show ?thesis
        using False 1 ufa_rep_of_neq
        unfolding \<open>u = (a, b)\<close> by (simp add: Let_def)
    next
      case 2
      with snoc.prems u have
        "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) b"
        "ufa_rep_of (ufa_unions uf_init us) y = ufa_rep_of (ufa_unions uf_init us) a"
        using ufa_rep_of_ufa_unions_eq_if_in_equivcl
        by simp_all
      moreover note proves_eq_b_a = proves_eq.sym[OF proves_eq.assm[where i = "length us"]]
      from 2 snoc u have
        "us @ [u] \<turnstile>\<^sub>= explain uf_init us x b : (x, b)"
        "us @ [u] \<turnstile>\<^sub>= explain uf_init us a y : (a, y)"
        using weaken_proves_eq[where as=us and bs="[u]"] by force+
      note proves_eq.trans[OF proves_eq.trans[OF this(1) proves_eq_b_a] this(2)]
      ultimately show ?thesis
        using False 2 ufa_rep_of_neq
        unfolding \<open>u = (a, b)\<close> by (simp add: Let_def)
    qed
  qed
qed

theorem explain_partial_sound:
  assumes "explain_partial uf_init us x y = Some p"
  shows "us \<turnstile>\<^sub>= p : (x, y)"
  using assms explain_complete unfolding explain_partial_def
  by (cases "(x, y) \<in> equivcl (set us)") auto

theorem explain_partial_complete:
  assumes "explain_partial uf_init us x y = None"
  shows "\<not> us \<turnstile>\<^sub>= p : (x, y)"
  using assms proves_eq_sound unfolding explain_partial_def by force

end

end
