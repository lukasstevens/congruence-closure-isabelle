chapter \<open>Union-Find Data-Structure with Explain Operation\<close>
theory Explain_Definition
  imports 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Tree"
    "Equality_Proof"
begin

subsection \<open>Definitions\<close>

record ufe_ds =
  uf_ds :: ufa
  au_ds :: "nat \<rightharpoonup> nat"
  unions :: "(nat \<times> nat) list"

fun ufe_union where
  "ufe_union \<lparr> uf_ds = uf, au_ds = au, unions = u \<rparr> x y =
    \<lparr> uf_ds = ufa_union uf x y
    , au_ds = au(ufa_rep_of uf x \<mapsto> length u)
    , unions = u @ [(x, y)]
    \<rparr>"

definition ufe_init :: "nat \<Rightarrow> ufe_ds" where
  "ufe_init n \<equiv> \<lparr> uf_ds = ufa_init n, au_ds = Map.empty, unions = [] \<rparr>"

definition "ufe_unions \<equiv> foldl (\<lambda>ufe_ds (x, y). ufe_union ufe_ds x y)"

abbreviation "ufe_rep_of ufe_ds x \<equiv> ufa_rep_of (uf_ds ufe_ds) x"
abbreviation "ufe_parent_of ufe_ds x \<equiv> ufa_parent_of (uf_ds ufe_ds) x"

lemma uf_ds_ufe_union:
  "uf_ds (ufe_union ufe_ds x y) = ufa_union (uf_ds ufe_ds) x y"
  by (cases ufe_ds) simp

lemma au_ds_ufe_union:
  "au_ds (ufe_union ufe_ds x y) = (au_ds ufe_ds)(ufe_rep_of ufe_ds x \<mapsto> length (unions ufe_ds))"
  by (cases ufe_ds) simp

lemma unions_ufe_union:
  "unions (ufe_union ufe_ds x y) = unions ufe_ds @ [(x, y)]"
  by (cases ufe_ds) (simp split: prod.splits)

lemmas ufe_union_sel[simp] = uf_ds_ufe_union au_ds_ufe_union unions_ufe_union

declare ufe_union.simps[simp del]

lemma ufe_init_sel[simp]:
  "uf_ds (ufe_init n) = ufa_init n"
  "au_ds (ufe_init n) = Map.empty"
  "unions (ufe_init n) = []"
  unfolding ufe_init_def by simp_all

lemma ufa_\<alpha>_uf_ds_ufe_union_eq_per_union:
  assumes "x \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))" "y \<in> Field (ufa_\<alpha> (uf_ds ufe_ds))"
  shows "ufa_\<alpha> (uf_ds (ufe_union ufe_ds x y)) = per_union (ufa_\<alpha> (uf_ds ufe_ds)) x y"
  using assms per_union_cmp[OF part_equiv_ufa_\<alpha>, OF ufa_\<alpha>I]
  unfolding ufe_union_sel ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha>
  by simp

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
  fixes ufe_ds :: "ufe_ds"
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
  fixes ufe_init :: ufe_ds
begin

function explain :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat eq_prf" where
  "explain [] x _ = ReflP x"
| "explain (us @ [(a, b)]) y z =
    (let
      ufe_ds = ufe_unions ufe_init us
    in
      (if ufe_rep_of ufe_ds y = ufe_rep_of ufe_ds z then explain us y z
      else if ufe_rep_of ufe_ds b = ufe_rep_of ufe_ds y then
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

end