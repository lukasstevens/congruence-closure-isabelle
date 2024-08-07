theory Explain_Simple
  imports
    "Union_Find"
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

lemma in_Field_ufa_\<alpha>_if_in_eff_unions:
  assumes "eff_unions uf us"
  assumes "u \<in> set us"
  shows "fst u \<in> Field (ufa_\<alpha> uf)" "snd u \<in> Field (ufa_\<alpha> uf)"
  using assms
  by (induction uf us rule: eff_unions.induct) auto

lemma Field_ufa_\<alpha>_ufa_unions[simp]:
  assumes "eff_unions uf us"
  shows "Field (ufa_\<alpha> (ufa_unions uf us)) = Field (ufa_\<alpha> uf)"
  using assms
  by (induction uf us rule: eff_unions.induct) simp_all

context
  fixes ufa_init :: ufa
begin

function explain :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf" where
  "explain [] x _ = ReflP x"
| "explain (us @ [(a, b)]) y z =
    (let
      uf = ufa_unions ufa_init us
    in
      (if ufa_rep_of uf y = ufa_rep_of uf z then explain us y z
      else if ufa_rep_of uf b = ufa_rep_of uf y then
        TransP (TransP (explain us y b) (SymP (AssmP (length us)))) (explain us a z)
      else
        TransP (TransP (explain us y a) (AssmP (length us))) (explain us b z))
    )"
  by auto (metis prod.exhaust rev_exhaust)
termination by (relation "measure (\<lambda>(us, y, z). size us)") auto

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

lemma proves_eq_explain:
  assumes "eff_unions uf_init us"
  assumes "ufa_\<alpha> uf_init \<subseteq> Id"
  defines "uf \<equiv> ufa_unions uf_init us"
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "us \<turnstile>\<^sub>= explain uf_init us x y : (x, y)"
  using assms
proof(induction us arbitrary: uf x y rule: rev_induct)
  case Nil
  then have "x = y"
    using ufa_rep_of_eq_iff_in_ufa_\<alpha> by auto
  then show ?case
    using proves_eq.refl by force
next
  case (snoc u us)
  then obtain a b where u:
    "u = (a, b)" "eff_union (ufa_unions uf_init us) a b"
    by (cases u) (auto simp: eff_unions_append)
  show ?case
  proof(cases "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) y")
    case True
    with snoc u have "us \<turnstile>\<^sub>= explain uf_init us x y : (x, y)"
      using Field_ufa_\<alpha>_ufa_unions eff_unions_append by simp
    with True show ?thesis
      unfolding \<open>u = (a, b)\<close>
      by (simp add: weaken_proves_eq Let_def)
  next
    case False
    with snoc u consider
      "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) a"
      "ufa_rep_of (ufa_unions uf_init us) b = ufa_rep_of (ufa_unions uf_init us) y" |
      "ufa_rep_of (ufa_unions uf_init us) x = ufa_rep_of (ufa_unions uf_init us) b"
      "ufa_rep_of (ufa_unions uf_init us) a = ufa_rep_of (ufa_unions uf_init us) y"
      by (simp add: ufa_unions_append ufa_rep_of_ufa_union) metis
    then show ?thesis
    proof cases
      case 1
      note proves_eq_a_b = proves_eq.assm[where i = "length us"]
      from snoc eff_unionD[OF u(2)] 1 have
        "us @ [(a, b)] \<turnstile>\<^sub>= explain uf_init us x a : (x, a)"
        "us @ [(a, b)] \<turnstile>\<^sub>= explain uf_init us b y : (b, y)"
        by (auto simp: eff_unions_append weaken_proves_eq)
      note proves_eq.trans[OF proves_eq.trans[OF this(1) proves_eq_a_b] this(2)]
      with False 1 show ?thesis
        unfolding \<open>u = (a, b)\<close> by (simp add: Let_def)
    next
      case 2
      note proves_eq_b_a =
        proves_eq.sym[OF proves_eq.assm[where i = "length us"]]
      from snoc eff_unionD[OF u(2)] 2 have
        "us @ [(a, b)] \<turnstile>\<^sub>= explain uf_init us x b : (x, b)"
        "us @ [(a, b)] \<turnstile>\<^sub>= explain uf_init us a y : (a, y)"
        by (auto simp: eff_unions_append weaken_proves_eq)
      note proves_eq.trans[OF proves_eq.trans[OF this(1) proves_eq_b_a] this(2)]
      with False 2 show ?thesis
        unfolding \<open>u = (a, b)\<close> by (simp add: Let_def)
    qed
  qed
qed

lemma proves_eq_explain_ufa_init:
  assumes "eff_unions (ufa_init n) us"
  defines "uf \<equiv> ufa_unions (ufa_init n) us"
  assumes "x \<in> Field (ufa_\<alpha> uf)" "y \<in> Field (ufa_\<alpha> uf)"
  assumes "ufa_rep_of uf x = ufa_rep_of uf y"
  shows "us \<turnstile>\<^sub>= explain (ufa_init n) us x y : (x, y)"
  using assms proves_eq_explain 
  by (simp add: ufa_\<alpha>_ufa_init subset_iff)

end