chapter \<open>Union-Find Data-Structure with Explain Operation\<close>
theory Explain_Definition
  imports 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Tree"
    "Refine_Monadic.Refine_Monadic"
begin

subsection \<open>Definitions\<close>

record union_find_explain_ds =
  uf_ds :: ufa
  au_ds :: "nat \<rightharpoonup> nat"
  unions :: "(nat \<times> nat) list"

definition "some_pair x y \<equiv> SOME p. p = (x, y) \<or> p = (y, x)"

lemma some_pair_eq:
  "some_pair x y = (x, y) \<or> some_pair x y = (y, x)"
  unfolding some_pair_def by (metis (mono_tags, lifting) someI)
  
lemma some_pair_commute: "some_pair x y = some_pair y x"
  unfolding some_pair_def by metis

lemma some_pair_cases:
  assumes "some_pair x y = (x, y) \<Longrightarrow> P"
  assumes "some_pair x y = (y, x) \<Longrightarrow> P"
  shows "P"
  using assms some_pair_eq by fast

fun ufe_union where
  "ufe_union \<lparr> uf_ds = uf, au_ds = au, unions = u \<rparr> x y =
    (if ufa_rep_of uf x \<noteq> ufa_rep_of uf y then do {
        (x', y') \<leftarrow> SPEC (\<lambda>(x', y'). (x', y') = (x, y) \<or> (x', y') = (y, x));
        RETURN
          \<lparr> uf_ds = ufa_union uf x' y'
          , au_ds = au(ufa_rep_of uf x' \<mapsto> length u)
          , unions = u @ [(x', y')]
          \<rparr>
      }
    else RETURN \<lparr> uf_ds = uf, au_ds = au, unions = u \<rparr>)"

definition ufe_init :: "nat \<Rightarrow> union_find_explain_ds" where
  "ufe_init n \<equiv> \<lparr> uf_ds = ufa_init n, au_ds = Map.empty, unions = [] \<rparr>"

definition "ufe_unions ufe_ds us \<equiv> nfoldli us (\<lambda>_. True) (\<lambda>(x, y) ufe_ds. ufe_union ufe_ds x y)"

abbreviation "ufe_rep_of ufe_ds x \<equiv> ufa_rep_of (uf_ds ufe_ds) x"
abbreviation "ufe_parent_of ufe_ds x \<equiv> ufa_parent_of (uf_ds ufe_ds) x"

lemma uf_ds_ufe_union:
  "uf_ds (ufe_union ufe_ds x y) =
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
      then uf_ds ufe_ds
      else
        let (x', y') = some_pair x y
        in ufa_union (uf_ds ufe_ds) x' y')"
  by (cases ufe_ds) (simp split: prod.splits)

lemma au_ds_ufe_union:
  "au_ds (ufe_union ufe_ds x y) =
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
      then au_ds ufe_ds
      else
        let (x', y') = some_pair x y
        in (au_ds ufe_ds)(ufe_rep_of ufe_ds x' \<mapsto> length (unions ufe_ds)))"
  by (cases ufe_ds) (simp split: prod.splits)

lemma unions_ufe_union:
  "unions (ufe_union ufe_ds x y) =
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
      then unions ufe_ds
      else unions ufe_ds @ [some_pair x y])"
  by (cases ufe_ds) (simp split: prod.splits)

lemmas ufe_union_sel = uf_ds_ufe_union au_ds_ufe_union unions_ufe_union

lemma ufe_union_sel_if_rep_of_neq[simp]:
  assumes "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  shows
    "uf_ds (ufe_union ufe_ds x y) =
      (let (x', y') = some_pair x y in ufa_union (uf_ds ufe_ds) x' y')"
    "au_ds (ufe_union ufe_ds x y) =
      (let (x', y') = some_pair x y
      in (au_ds ufe_ds)(ufe_rep_of ufe_ds x' \<mapsto> length (unions ufe_ds)))"
    "unions (ufe_union ufe_ds x y) = unions ufe_ds @ [some_pair x y]"
  using assms
  by (simp_all add: ufe_union_sel)

lemma ufe_init_sel[simp]:
  "uf_ds (ufe_init n) = ufa_init n"
  "au_ds (ufe_init n) = Map.empty"
  "unions (ufe_init n) = []"
  unfolding ufe_init_def by simp_all

lemma ufe_union_commute: "ufe_union ufe_ds x y = ufe_union ufe_ds y x"
  by (cases ufe_ds) (auto simp: some_pair_commute)

lemma ufa_\<alpha>_uf_ds_ufe_union_eq_per_union:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  shows "ufa_\<alpha> (uf_ds (ufe_union ufe_ds x y)) = per_union (ufa_\<alpha> (uf_ds ufe_ds)) x y"
  using assms per_union_cmp[OF part_equiv_ufa_\<alpha>, OF ufa_\<alpha>I]
  unfolding ufe_union_sel ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha>
  by (cases x y rule: some_pair_cases) simp_all

lemma Field_ufa_\<alpha>_uf_ds_ufe_union:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  shows "Field (ufa_\<alpha> (uf_ds (ufe_union ufe_ds x y))) = Field (ufa_\<alpha> (uf_ds ufe_ds))"
  using assms
  by (simp add: ufa_\<alpha>_uf_ds_ufe_union_eq_per_union)

lemma ufe_unions_append[simp]:
  "ufe_unions ufe_ds (us1 @ us2) = ufe_unions (ufe_unions ufe_ds us1) us2"
  unfolding ufe_unions_def by simp

lemma ufe_unions_Cons[simp]:
  "ufe_unions ufe_ds (u # us) = ufe_unions (ufe_union ufe_ds (fst u) (snd u)) us"
  unfolding ufe_unions_def by (simp add: case_prod_unfold)

lemma ufe_unions_Nil[simp]:
  "ufe_unions ufe_ds [] = ufe_ds"
  unfolding ufe_unions_def by simp

definition ufa_lca where
  "ufa_lca uf x y \<equiv>
    last (longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y))"

lemma ufa_lca_symmetric:
  "ufa_lca uf x y = ufa_lca uf y x"
proof -
  have
    "longest_common_prefix (awalk_verts_from_rep uf x) (awalk_verts_from_rep uf y)
    = longest_common_prefix (awalk_verts_from_rep uf y) (awalk_verts_from_rep uf x)"
    by (simp add: longest_common_prefix_max_prefix longest_common_prefix_prefix1
          longest_common_prefix_prefix2 prefix_order.eq_iff)
  then show ?thesis
    unfolding ufa_lca_def
    by auto
qed


text \<open>Finds the newest edge on the path from x to y
      (where y is nearer to the root than x).\<close>
context
  fixes ufe_ds :: "union_find_explain_ds"
begin

function (domintros) find_newest_on_walk :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_newest_on_walk y x =
    (if y = x then None
    else 
      combine_options max 
        (au_ds ufe_ds x)
        (find_newest_on_walk y (ufe_parent_of ufe_ds x)))"
  by pat_completeness auto

lemma find_newest_on_walk_if_eq[simp]:
  "find_newest_on_walk x x = None"
  by (meson find_newest_on_walk.domintros find_newest_on_walk.psimps)

end

context
  fixes ufe_init :: union_find_explain_ds
begin

function explain :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "explain [] _ _ = {}"
| "explain (us @ [(a, b)]) y z =
    (let
      ufe_ds = ufe_unions ufe_init us
    in
      (if ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds z then explain us y z
      else {(a, b)} \<union>
        (if ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds y
          then explain us y b \<union> explain us a z
         else explain us y a \<union> explain us b z))
    )"
  by auto (metis prod.exhaust rev_exhaust)
termination by (relation "measure (\<lambda>(us, y, z). size us)") auto

lemma explain_refl[simp]:
  "explain us x x = {}"
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

end