theory UF_ADT
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
begin

lemma Field_per_union[simp]: "Field (per_union R a b) = Field R"
  unfolding per_union_def Field_def
  by auto

lemma finite_eq_class_per_union_if_finite_eq_class:
  assumes "part_equiv R"
  assumes "\<And>a. finite (R `` {a})"
  shows "finite (per_union R b c `` {a})"
proof -
  from \<open>part_equiv R\<close>[THEN part_equiv_sym] have "{d. (d, c) \<in> R} = (R `` {c})" for c
    unfolding Image_singleton by blast
  with assms have "finite {d. (d, c) \<in> R}" for c
    by simp
  then have "finite {d. (a, b) \<in> R \<and> (d, c) \<in> R}" "finite {d. (d, b) \<in> R \<and> (a, c) \<in> R}"
    using finite_subset by simp_all
  with assms show ?thesis
    unfolding per_union_def
    by (auto simp: Image_singleton)
qed

lemma in_per_union_if_in_rel[simp]:
  "(x, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b"
  unfolding per_union_def by auto

lemma per_union_eq_if_not_in_Field:
  assumes "x \<notin> Field R"
  shows "per_union R x y = R" "per_union R y x = R"
  using assms unfolding Field_def per_union_def
  by auto

lemma in_per_unionI:
  assumes "part_equiv R" "x \<in> Field R" "y \<in> Field R"
  shows "(x, y) \<in> per_union R x y"
  using assms(2,3)
  using part_equiv_sym[OF assms(1)] part_equiv_trans[OF assms(1)]
  unfolding per_union_def Field_def
  by blast

record ('uf, 'dom) union_find_adt =
  init :: 'uf ("uf'_init\<index>")
  rep_of :: "'uf \<Rightarrow> 'dom \<Rightarrow> 'dom" ("uf'_rep'_of\<index>")
  union :: "'uf \<Rightarrow> 'dom \<Rightarrow> 'dom \<Rightarrow> 'uf" ("uf'_union\<index>")
  invar :: "'uf \<Rightarrow> bool" ("uf'_invar\<index>")
  \<alpha> :: "'uf \<Rightarrow> 'dom rel" ("uf'_\<alpha>\<index>")

record ('uf, 'dom) union_find_parent_adt =
  "('uf, 'dom) union_find_adt" +
  parent_of :: "'uf \<Rightarrow> 'dom \<Rightarrow> 'dom" ("uf'_parent'_of\<index>")
  
record ('uf, 'dom) union_find_explain_adt =
  "('uf, 'dom) union_find_adt" +
  explain :: "'uf \<Rightarrow> 'dom \<Rightarrow> 'dom \<Rightarrow> 'dom rel" ("uf'_explain\<index>")

locale union_find_adt =
  fixes uf_adt :: "('uf, 'dom, 'more) union_find_adt_scheme" (structure)
begin

definition "uf_unions \<equiv> foldl (\<lambda>uf (x, y). uf_union uf x y)"

lemma
  unions_Nil[simp]: "uf_unions uf [] = uf" and
  unions_Cons[simp]: "uf_unions uf (u # us) = uf_unions (uf_union uf (fst u) (snd u)) us"
  unfolding uf_unions_def by (simp_all split: prod.splits)

lemma unions_append:
  "uf_unions uf (us1 @ us2) = uf_unions (uf_unions uf us1) us2"
  by (induction us1 arbitrary: uf) simp_all

definition
  "valid_unions uf us \<equiv> \<forall>(x, y) \<in> set us. x \<in> Field (uf_\<alpha> uf) \<and> y \<in> Field (uf_\<alpha> uf)"

lemma valid_unions_Nil[simp]:
  "valid_unions uf []"
  unfolding valid_unions_def by simp

lemma valid_unions_Cons[simp]:
  "valid_unions uf (x # xs) \<longleftrightarrow>
    fst x \<in> Field (uf_\<alpha> uf) \<and> snd x \<in> Field (uf_\<alpha> uf) \<and> valid_unions uf xs"
  unfolding valid_unions_def by (simp split: prod.splits)

lemma valid_unions_append[simp]:
  "valid_unions uf (xs @ ys) \<longleftrightarrow> valid_unions uf xs \<and> valid_unions uf ys"
  unfolding valid_unions_def by auto

lemma valid_unions_takeI[simp, intro]:
  "valid_unions uf us \<Longrightarrow> valid_unions uf (take i us)"
  unfolding valid_unions_def using in_set_takeD by fast

fun eff_unions where
  "eff_unions uf [] \<longleftrightarrow> True"
| "eff_unions uf ((x, y) # us) \<longleftrightarrow>
    uf_rep_of uf x \<noteq> uf_rep_of uf y \<and> eff_unions (uf_union uf x y) us"

end

locale union_find = union_find_adt +
  assumes part_equiv_\<alpha>:
    "uf_invar uf \<Longrightarrow> part_equiv (uf_\<alpha> uf)"
  assumes invar_init: "uf_invar uf_init"
  assumes \<alpha>_init: "uf_\<alpha> uf_init \<subseteq> Id" 
  assumes \<alpha>_rep_of:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_rep_of uf x = uf_rep_of uf y \<longleftrightarrow> (x, y) \<in> uf_\<alpha> uf"
  assumes invar_union:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_invar (uf_union uf x y)"
  assumes \<alpha>_union:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_\<alpha> (uf_union uf x y) = per_union (uf_\<alpha> uf) x y"

locale union_find_parent_adt =
  union_find_adt where uf_adt = uf_adt for uf_adt ::
    "('uf, 'dom, 'more) union_find_parent_adt_scheme" (structure)


locale union_find_parent =
  union_find_parent_adt where uf_adt = uf_adt +
  union_find where uf_adt = uf_adt
  for uf_adt (structure)  +

  assumes parent_of_init[simp]:
    "x \<in> Field (uf_\<alpha> uf_init) \<Longrightarrow> uf_parent_of uf_init x = x"
  assumes refl_parent_of_iff_refl_rep_of:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_parent_of uf x = x \<longleftrightarrow> uf_rep_of uf x = x"
  assumes parent_of_union:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf); z \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_parent_of (uf_union uf x y) z =
          (if z = uf_rep_of uf x then uf_rep_of uf y else uf_parent_of uf z)"
begin

definition (in union_find_parent_adt)
  "uf_parent_of_rel uf \<equiv> {(uf_parent_of uf x, x) |x. x \<in> Field (uf_\<alpha> uf)} - Id"

lemma parent_of_rel_init_eq[simp]: "uf_parent_of_rel uf_init = {}"
  unfolding uf_parent_of_rel_def using parent_of_init by blast

lemma wf_parent_of_rel_init:
  "wf (uf_parent_of_rel uf_init)"
  by simp

end
(*
locale union_find_explain = union_find_explain_adt + union_find +
  assumes \<alpha>_explain:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf); (x, y) \<in> uf_\<alpha> uf \<rbrakk>
    \<Longrightarrow> (x, y) \<in> (uf_explain uf x y)\<^sup>*"
*)

locale union_find_invar = union_find +
  fixes uf
  assumes invar_uf: "uf_invar uf"
begin

lemmas
  part_equiv_\<alpha>[simp, intro] = part_equiv_\<alpha>[OF invar_uf] and
  \<alpha>_rep_of = \<alpha>_rep_of[OF invar_uf] and
  invar_union[simp, intro] = invar_union[OF invar_uf] and
  \<alpha>_union[simp] = \<alpha>_union[OF invar_uf]

lemma Field_\<alpha>_union[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "Field (uf_\<alpha> (uf_union uf x y)) = Field (uf_\<alpha> uf)"
  using assms by auto

lemma Pair_rep_of_in_\<alpha>_if_in_Field_\<alpha>:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "(x, uf_rep_of uf x) \<in> uf_\<alpha> uf"
  sorry

lemma rep_of_Pair_in_\<alpha>_if_in_Field_\<alpha>:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "(uf_rep_of uf x, x) \<in> uf_\<alpha> uf"
  using Pair_rep_of_in_\<alpha>_if_in_Field_\<alpha>[OF assms] part_equiv_\<alpha>
  by (meson part_equiv_sym)

lemma rep_of_in_Field_\<alpha>_if_in_Field_\<alpha>[simp, intro]:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "uf_rep_of uf x \<in> Field (uf_\<alpha> uf)"
  using assms Pair_rep_of_in_\<alpha>_if_in_Field_\<alpha> by (fastforce simp: Field_iff)

lemma rep_of_rep_of[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "uf_rep_of uf (uf_rep_of uf x) = uf_rep_of uf x"
  using assms rep_of_Pair_in_\<alpha>_if_in_Field_\<alpha>
  by (subst \<alpha>_rep_of) auto

lemma Pair_rep_of_in_\<alpha>_union:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "(uf_rep_of uf x, uf_rep_of uf y) \<in> uf_\<alpha> (uf_union uf x y)"
proof -
  from assms have
    "(uf_rep_of uf x, x) \<in> uf_\<alpha> (uf_union uf x y)"
    "(y, uf_rep_of uf y) \<in> uf_\<alpha> (uf_union uf x y)"
    using rep_of_Pair_in_\<alpha>_if_in_Field_\<alpha> Pair_rep_of_in_\<alpha>_if_in_Field_\<alpha>
    by simp_all
  moreover have "(x, y) \<in> uf_\<alpha> (uf_union uf x y)"
    using assms by (simp add: in_per_unionI)
  ultimately show ?thesis
    using assms
    by (metis FieldI1 FieldI2 invar_union union_find.\<alpha>_rep_of union_find_axioms)
qed
 
lemma rep_of_neq_if_rep_of_union_neq:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  assumes "j \<in> Field (uf_\<alpha> uf)" "k \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_union uf x y) j \<noteq> uf_rep_of (uf_union uf x y) k"
  shows "uf_rep_of uf j \<noteq> uf_rep_of uf k"
proof -
  from assms interpret uf_union: union_find_invar where uf = "uf_union uf x y"
    by unfold_locales auto
  from assms show ?thesis
    by (auto simp: \<alpha>_rep_of uf_union.\<alpha>_rep_of)
qed
  

end

context union_find_invar
begin

lemma valid_union_union[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "valid_unions (uf_union uf x y) us \<longleftrightarrow> valid_unions uf us"
  using assms
  by (induction us) auto

lemma valid_unions_nthD[simp, dest]:
  assumes "valid_unions uf us" "i < length us"
  shows "fst (us ! i) \<in> Field (uf_\<alpha> uf)" "snd (us ! i) \<in> Field (uf_\<alpha> uf)"
  using assms unfolding valid_unions_def
  using nth_mem by fastforce+

lemma valid_unions_nth_eq_pairD:
  assumes "valid_unions uf us" "i < length us"
  assumes "us ! i = (a, b)"
  shows "a \<in> Field (uf_\<alpha> uf)" "b \<in> Field (uf_\<alpha> uf)"
  using assms valid_unions_nthD by force+

lemma valid_unions_induct[consumes 1, case_names init union]:
  assumes "valid_unions uf us"
  assumes "P uf"
  assumes "\<And>uf x y.
    \<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf) ; P uf \<rbrakk>
    \<Longrightarrow> P (uf_union uf x y)"
  shows "P (uf_unions uf us)"
  using assms(1,2) invar_uf
proof(induction us arbitrary: uf)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from Cons show ?case
    using assms(3) by simp
qed

lemma Field_\<alpha>_unions[simp]:
  assumes "valid_unions uf us"
  shows "Field (uf_\<alpha> (uf_unions uf us)) = Field (uf_\<alpha> uf)"
  using assms
proof(induction rule: valid_unions_induct)
  case (union uf x y)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from union show ?case by simp
qed simp

lemma valid_union_unions[simp]:
  assumes "valid_unions uf us"
  shows "valid_unions (uf_unions uf us) ous \<longleftrightarrow> valid_unions uf ous"
  using assms Field_\<alpha>_unions unfolding valid_unions_def by simp

lemma invar_unions:
  assumes "valid_unions uf us"
  shows "uf_invar (uf_unions uf us)"
  using assms
proof(induction rule: valid_unions_induct)
  case init
  then show ?case by (fact invar_uf)
next
  case (union uf x y)
  then interpret union_find_invar where uf = uf
    by unfold_locales
  from union show ?case by simp
qed

end

locale union_find_parent_invar = union_find_parent +
  fixes uf
  assumes invar_uf: "uf_invar uf"
begin

sublocale union_find_invar where uf = uf
  using invar_uf by unfold_locales

lemmas
  parent_of_union[simp] = parent_of_union[OF invar_uf] and
  refl_parent_of_iff_refl_rep_of = refl_parent_of_iff_refl_rep_of[OF invar_uf]
  
end

locale union_find_parent_unions = union_find_parent +
  fixes uf us
  assumes valid_unions: "valid_unions uf_init us"
  assumes uf_eq_unions_init: "uf = uf_unions uf_init us"
begin

sublocale ufp_invar_init: union_find_parent_invar where uf = uf_init
  using invar_init by unfold_locales

sublocale union_find_parent_invar where uf = uf
  unfolding uf_eq_unions_init using ufp_invar_init.invar_unions[OF valid_unions]
  by unfold_locales

lemma uf_induct[case_names init union]:
  assumes "P uf_init"
  assumes "\<And>uf us x y.
    \<lbrakk> union_find_parent_unions uf_adt uf us; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf)
    ; P uf \<rbrakk> \<Longrightarrow> P (uf_union uf x y)"
  shows "P uf"
  using valid_unions uf_eq_unions_init
proof(induction us arbitrary: uf rule: rev_induct)
  case Nil
  with assms show ?case by simp
next
  case (snoc u us)
  then have "valid_unions uf_init us"
    by simp
  note IH = snoc.IH[OF this HOL.refl]
  with \<open>valid_unions uf_init us\<close> have "uf_invar (uf_unions uf_init us)"
    by (simp add: ufp_invar_init.invar_unions)
  then interpret union_find_invar where uf = "uf_unions uf_init us"
    by unfold_locales
  from \<open>valid_unions uf_init us\<close> have ufp_unions:
    "union_find_parent_unions uf_adt (uf_unions uf_init us) us"
    by unfold_locales simp_all
  from snoc.prems(1) show ?case
    unfolding snoc
    by (auto simp: unions_append intro!: assms(2) IH ufp_unions)
qed

lemma union_find_parent_unions_union:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "union_find_parent_unions uf_adt (uf_union uf x y) (us @ [(x, y)])"
  using assms valid_unions uf_eq_unions_init
  by unfold_locales (auto simp: unions_append)

lemma parent_of_in_Field_\<alpha>I[simp, intro]:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "uf_parent_of uf x \<in> Field (uf_\<alpha> uf)"
  using assms
proof(induction rule: uf_induct)
  case (union uf us y z)
  then interpret union_find_parent_unions where uf = uf and us = us
    by blast
  from union show ?case
    by simp
qed simp

lemma parent_of_Pair_in_\<alpha>:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "(uf_parent_of uf x, x) \<in> uf_\<alpha> uf"
  using assms
proof(induction arbitrary: x rule: uf_induct)
  case init
  then show ?case
   using ufp_invar_init.\<alpha>_rep_of by auto
next
  case (union uf us x y z)
  then interpret union_find_parent_unions where uf = uf and us = us
    by blast
  from union have "(uf_parent_of uf x, x) \<in> uf_\<alpha> uf"
    by simp
  with union show ?case
    using Pair_rep_of_in_\<alpha>_union by force
qed

lemma Pair_parent_of_in_\<alpha>:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "(x, uf_parent_of uf x) \<in> uf_\<alpha> uf"
  using assms
  by (meson parent_of_Pair_in_\<alpha> part_equiv_\<alpha> part_equiv_sym)

lemma parent_of_rep_of[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "uf_parent_of uf (uf_rep_of uf x) = uf_rep_of uf x"
  using assms refl_parent_of_iff_refl_rep_of by simp

lemma rep_of_parent_of[simp]:
  assumes "x \<in> Field (uf_\<alpha> uf)"
  shows "uf_rep_of uf (uf_parent_of uf x) = uf_rep_of uf x"
  using assms
proof(induction arbitrary: x rule: uf_induct)
  case (union uf us x y z)
  then interpret union_find_parent_unions where uf = uf and us = us
    by blast
  from union interpret uf_invar_union: union_find_invar where uf = "uf_union uf x y"
    by unfold_locales blast

  from union have "z \<in> Field (uf_\<alpha> uf)"
    by simp
  from union have "(uf_rep_of uf y, uf_rep_of uf x) \<in> uf_\<alpha> (uf_union uf x y)"
    using Pair_rep_of_in_\<alpha>_union uf_invar_union.part_equiv_\<alpha>[THEN part_equiv_sym]
    by blast
  with union have "uf_rep_of (uf_union uf x y) (uf_rep_of uf y)
    = uf_rep_of (uf_union uf x y) (uf_rep_of uf x)"
    using uf_invar_union.\<alpha>_rep_of by force
  with union show ?case
    unfolding parent_of_union[OF union.hyps(2,3) \<open>z \<in> Field (uf_\<alpha> uf)\<close>]
    using rep_of_neq_if_rep_of_union_neq[OF _ _ parent_of_in_Field_\<alpha>I]
    by fastforce
qed simp


lemma rep_of_union_rep_of_y:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  shows "uf_rep_of (uf_union uf x y) (uf_rep_of uf y) = uf_rep_of uf y"
proof -
  interpret ufp_unions: union_find_parent_unions where
    uf = "uf_union uf x y" and us = "us @ [(x, y)]"
    using assms by (intro union_find_parent_unions_union)

  from assms show ?thesis
    by (subst ufp_unions.refl_parent_of_iff_refl_rep_of[symmetric]) auto
qed

lemma rep_of_union:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)" "z \<in> Field (uf_\<alpha> uf)"
  shows "uf_rep_of (uf_union uf x y) z =
    (if uf_rep_of uf z = uf_rep_of uf x \<or> uf_rep_of uf z = uf_rep_of uf y
      then uf_rep_of uf y
      else uf_rep_of uf z)" (is "_ = ?rhs")
proof -
  interpret ufp_unions: union_find_parent_unions where
    uf = "uf_union uf x y" and us = "us @ [(x, y)]"
    using assms by (intro union_find_parent_unions_union)

  from assms have rep_of_z_in_Field_\<alpha>_union:
    "uf_rep_of uf z \<in> Field (uf_\<alpha> (uf_union uf x y))"
    by simp

  from assms have "uf_rep_of (uf_union uf x y) (uf_rep_of uf z) =
    uf_rep_of (uf_union uf x y) z"
    using rep_of_in_Field_\<alpha>_if_in_Field_\<alpha>
    using rep_of_neq_if_rep_of_union_neq rep_of_rep_of
    by metis
  moreover
  from assms have "uf_rep_of (uf_union uf x y) (uf_rep_of uf z) = ?rhs"
  proof(cases "uf_rep_of uf z = uf_rep_of uf x")
    case False
    note ufp_unions.refl_parent_of_iff_refl_rep_of[
        OF rep_of_z_in_Field_\<alpha>_union, THEN iffD1]
    with assms False show ?thesis
      by auto
  next
    case True
    then have "uf_rep_of (uf_union uf x y) (uf_rep_of uf x) =
      uf_rep_of (uf_union uf x y) (uf_parent_of (uf_union uf x y) (uf_rep_of uf x))"
      using rep_of_z_in_Field_\<alpha>_union by auto
    also have "\<dots> = uf_rep_of (uf_union uf x y) (uf_rep_of uf y)"
      using assms True parent_of_union by simp
    also have "\<dots> = uf_rep_of uf (uf_rep_of uf y)"
      using assms rep_of_union_rep_of_y by simp
    finally show ?thesis
      using assms True by simp
  qed
  ultimately show ?thesis
    by auto
qed

lemma wf_parent_of_rel:
  "wf (uf_parent_of_rel uf)"
  sorry

lemma finite_eq_class_\<alpha>:
  "finite (uf_\<alpha> uf `` {y})"
proof(induction arbitrary: y rule: uf_induct)
  case init
  then show ?case
    by (metis Image_Id \<alpha>_init finite.emptyI finite_Image_subset finite_insert)
next
  case (union uf us x y)
  then interpret union_find_parent_unions where uf = uf and us = us
    by blast
  from union show ?case
    unfolding \<alpha>_union[OF union.hyps(2,3)]
    by (auto intro!: finite_eq_class_per_union_if_finite_eq_class)
qed

end

context union_find_invar
begin

(*
lemma rep_of_uf_unions_take_neq_if_rep_of_uf_unions_neq:
  assumes "valid_unions uf us"
  assumes "j \<in> Field (uf_\<alpha> uf)" "k \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_unions uf us) j \<noteq> uf_rep_of (uf_unions uf us) k"
  shows "uf_rep_of (uf_unions uf (take i us)) j \<noteq> uf_rep_of (uf_unions uf (take i us)) k"
  using assms
proof(induction us arbitrary: i rule: rev_induct)
  case (snoc u us)
  from snoc interpret uf_unions: union_find_invar where uf = "uf_unions uf us"
    by unfold_locales auto
  from snoc have rep_of_ufa_union:
    "uf_rep_of (uf_union (uf_unions uf us) (fst u) (snd u)) j
    \<noteq> uf_rep_of (uf_union (uf_unions uf us) (fst u) (snd u)) k"
    by (cases u) simp
  note uf_unions.rep_of_neq_if_rep_of_ufa_union_neq[OF _ _ _  _ this]
  with snoc.prems have "uf_rep_of (uf_unions uf us) j \<noteq> uf_rep_of (uf_unions uf us) k"
    by auto
  note snoc.IH[OF _ snoc.prems(2,3) this]
  with snoc.prems(1) rep_of_ufa_union show ?case
    by (cases "i \<le> length us") (auto split: prod.splits)
qed simp
*)
end

lemma (in union_find) eff_unions_append:
  assumes "uf_invar uf"
  assumes "valid_unions uf (us1 @ us2)"
  shows "eff_unions uf (us1 @ us2)
    \<longleftrightarrow> eff_unions uf us1 \<and> eff_unions (uf_unions uf us1) us2"
  using assms
proof(induction us1 arbitrary: uf)
  case Nil
  then show ?case by simp
next
  case (Cons u1 us1)
  let ?uf' = "uf_union uf (fst u1) (snd u1)"
  from Cons interpret union_find_invar where uf = uf
    by unfold_locales
  from Cons have "uf_invar ?uf'"
    using invar_union by simp
  from Cons have "valid_unions ?uf' (us1 @ us2)"
    by simp
  note IH = Cons.IH[OF \<open>uf_invar ?uf'\<close> this]
  then show ?case
    by (cases u1) simp
qed

end
