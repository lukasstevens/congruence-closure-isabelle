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
  union_find where uf_adt = uf_adt +
  union_find_parent_adt where uf_adt = uf_adt for uf_adt (structure) +

  assumes wf_parent_of:
    "uf_invar uf \<Longrightarrow> wf {(uf_parent_of uf x, x) |x. x \<in> Field (uf_\<alpha> uf) \<and> uf_parent_of uf x \<noteq> x}"
  assumes parent_of_in_\<alpha>:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk> \<Longrightarrow> (uf_parent_of uf x, x) \<in> uf_\<alpha> uf"
  assumes parent_of_refl_iff_rep_of_refl:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_parent_of uf x = x \<longleftrightarrow> uf_rep_of uf x = x"
  assumes rep_of_parent_of:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_rep_of uf (uf_parent_of uf x) = uf_rep_of uf x"
  assumes parent_of_union:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf); z \<in> Field (uf_\<alpha> uf) \<rbrakk>
    \<Longrightarrow> uf_parent_of (uf_union uf x y) z =
          (if z = uf_rep_of uf x then uf_rep_of uf y else uf_parent_of uf z)"

(*
locale union_find_explain = union_find_explain_adt + union_find +
  assumes \<alpha>_explain:
    "\<lbrakk> uf_invar uf; x \<in> Field (uf_\<alpha> uf); y \<in> Field (uf_\<alpha> uf); (x, y) \<in> uf_\<alpha> uf \<rbrakk>
    \<Longrightarrow> (x, y) \<in> (uf_explain uf x y)\<^sup>*"
*)

locale union_find_invar = union_find +
  fixes uf :: 'uf
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


lemma rep_of_neq_if_rep_of_union_neq:
  assumes "x \<in> Field (uf_\<alpha> uf)" "y \<in> Field (uf_\<alpha> uf)"
  assumes "j \<in> Field (uf_\<alpha> uf)" "k \<in> Field (uf_\<alpha> uf)"
  assumes "uf_rep_of (uf_union uf x y) j \<noteq> uf_rep_of (uf_union uf x y) k"
  shows "uf_rep_of uf j \<noteq> uf_rep_of uf k"
  using assms
proof -
  from assms interpret uf_union: union_find_invar where uf = "uf_union uf x y"
    by unfold_locales auto
  from assms show ?thesis
    by (auto simp: \<alpha>_rep_of uf_union.\<alpha>_rep_of)
qed  

end

locale union_find_parent_invar = union_find_parent +
  fixes uf :: 'uf
  assumes invar_uf: "uf_invar uf"
begin
                     
sublocale union_find_invar where uf = uf
  using invar_uf by unfold_locales

lemmas
  wf_parent_of = wf_parent_of[OF invar_uf] and
  parent_of_in_\<alpha>[intro] = parent_of_in_\<alpha>[OF invar_uf] and
  parent_of_refl_iff_rep_of_refl = parent_of_refl_iff_rep_of_refl[OF invar_uf] and
  rep_of_parent_of[simp] = rep_of_parent_of[OF invar_uf] and
  parent_of_union[simp] = parent_of_union[OF invar_uf]

lemma parent_of_in_Field_\<alpha>I[intro]:
  "x \<in> Field (uf_\<alpha> uf) \<Longrightarrow> uf_parent_of uf x \<in> Field (uf_\<alpha> uf)"
  using parent_of_in_\<alpha> by (meson FieldI1)

lemma parent_of_in_\<alpha>_sym:
  "x \<in> Field (uf_\<alpha> uf) \<Longrightarrow> (x, uf_parent_of uf x) \<in> uf_\<alpha> uf"
  using part_equiv_\<alpha> parent_of_in_\<alpha> part_equiv_sym by metis

end

definition (in union_find_adt)
  "valid_unions uf us \<equiv> \<forall>(x, y) \<in> set us. x \<in> Field (uf_\<alpha> uf) \<and> y \<in> Field (uf_\<alpha> uf)"

context union_find
begin

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

end