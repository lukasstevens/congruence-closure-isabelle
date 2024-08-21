theory Equality_Proof
  imports Main
begin

definition "symcl r \<equiv> r \<union> r\<inverse>"

definition "equivcl r \<equiv> (symcl r)\<^sup>*"

lemma symcl_mono:
  assumes "r \<subseteq> s"
  shows "symcl r \<subseteq> symcl s"
  using assms unfolding symcl_def by blast

lemma equivcl_mono:
  assumes "r \<subseteq> s"
  shows "equivcl r \<subseteq> equivcl s"
  using assms rtrancl_mono symcl_mono
  unfolding equivcl_def by blast

lemma symcl_insert:
  "symcl (insert p r) = insert (snd p, fst p) (insert p (symcl r))"
  unfolding symcl_def by auto

lemma Field_symcl[simp]:
  "Field (symcl r) = Field r"
  unfolding symcl_def by simp

lemma Field_trancl[simp]:
  "Field (trancl r) = Field r"
  by (simp add: Field_def)

lemma in_Field_if_in_equivcl:
  assumes "(x, y) \<in> equivcl r" "x \<noteq> y"
  shows "x \<in> Field r" "y \<in> Field r"
  using assms unfolding equivcl_def
  by (fastforce dest: FieldI1 FieldI2 simp: rtrancl_eq_or_trancl)+

lemma refl_in_equivcl[simp, intro!]:
  "(x, x) \<in> equivcl r"
  unfolding equivcl_def by simp

datatype 'a eq_prf = AssmP nat | ReflP 'a | TransP "'a eq_prf" "'a eq_prf" | SymP "'a eq_prf"

inductive proves_eq :: "('a \<times> 'a) list \<Rightarrow> 'a eq_prf \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" ("_ \<turnstile>\<^sub>= _ : _" [60,0,60] 60) where
  assm: "i < length as \<Longrightarrow> as ! i = (x, y) \<Longrightarrow> as \<turnstile>\<^sub>= AssmP i : (x, y)"
| refl: "as \<turnstile>\<^sub>= ReflP x : (x, x)"
| trans: "as \<turnstile>\<^sub>= p1 : (x, y) \<Longrightarrow> as \<turnstile>\<^sub>= p2 : (y, z) \<Longrightarrow> as \<turnstile>\<^sub>= TransP p1 p2 : (x, z)"
| sym: "as \<turnstile>\<^sub>= p : (x, y) \<Longrightarrow> as \<turnstile>\<^sub>= SymP p : (y, x)"

lemma weaken_proves_eq:
  assumes "as \<turnstile>\<^sub>= p : (x, y)"
  shows "as @ bs \<turnstile>\<^sub>= p : (x, y)"
  using assms
proof(induction arbitrary: bs rule: proves_eq.induct)
  case (assm i as x y)
  then show ?case
    by (intro proves_eq.assm) (simp_all add: nth_append)
next
  case (refl as x)
  then show ?case
    by (intro proves_eq.refl)
next
  case (trans as p1 x y p2 z)
  then show ?case
    by (intro proves_eq.trans) auto
next
  case (sym as p x y)
  then show ?case
    by (intro proves_eq.sym) auto
qed

lemma proves_eq_complete:
  assumes "(x, y) \<in> equivcl (set as)"
  shows "\<exists>p. as \<turnstile>\<^sub>= p : (x, y)"
  using assms unfolding equivcl_def
proof(induction rule: rtrancl_induct)
  case base
  then show ?case
    using proves_eq.refl by fast
next
  case (step y z)
  then show ?case
  proof(cases "(y, z) \<in> set as")
    case True
    with step obtain i where "as \<turnstile>\<^sub>= AssmP i : (y, z)"
      using proves_eq.assm in_set_conv_nth by metis
    from proves_eq.trans[OF _ this] step show ?thesis
      by fast
  next
    case False
    with step have "(z, y) \<in> set as"
      unfolding symcl_def by simp
    with step obtain i where "as \<turnstile>\<^sub>= AssmP i : (z, y)"
      using proves_eq.assm in_set_conv_nth by metis
    from proves_eq.trans[OF _ proves_eq.sym[OF this]] step show ?thesis
      by fast
  qed
qed

lemma proves_eq_sound:
  assumes "as \<turnstile>\<^sub>= p : (x, y)"
  shows "(x, y) \<in> equivcl (set as)"
  using assms
proof(induction rule: proves_eq.induct)
  case (assm i as x y)
  then show ?case
    using nth_mem unfolding equivcl_def symcl_def by fastforce
next
  case (sym as p x y)
  then show ?case
    unfolding equivcl_def symcl_def
    by (simp add: Un_commute converse_Un rtrancl_converseD)
qed (auto simp: equivcl_def symcl_def)

end