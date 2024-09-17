theory Explain_Efficient
  imports 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Tree"
    "UFA_LCA"
    "Equality_Proof"
begin

record ufe_ds =
  uf_ds :: ufa
  au_ds :: "nat \<rightharpoonup> nat"
  unions :: "(nat \<times> nat) list"

fun ufe_union :: "ufe_ds \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe_ds" where
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
abbreviation "ufe_\<alpha> ufe_ds \<equiv> ufa_\<alpha> (uf_ds ufe_ds)"
abbreviation "ufe_lca ufe_ds \<equiv> ufa_lca (uf_ds ufe_ds)"
abbreviation "ufe_tree_of ufe_ds \<equiv> ufa_tree_of (uf_ds ufe_ds)"

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
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  shows "ufe_\<alpha> (ufe_union ufe_ds x y) = per_union (ufe_\<alpha> ufe_ds) x y"
  using assms per_union_cmp[OF part_equiv_ufa_\<alpha>, OF ufa_\<alpha>I]
  unfolding ufe_union_sel ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha>
  by simp

lemma Field_ufa_\<alpha>_uf_ds_ufe_union:
  assumes "x \<in> Field (ufe_\<alpha> ufe_ds)" "y \<in> Field (ufe_\<alpha> ufe_ds)"
  shows "Field (ufe_\<alpha> (ufe_union ufe_ds x y)) = Field (ufe_\<alpha> ufe_ds)"
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

context
  fixes ufe_ds :: ufe_ds
begin

function (domintros) find_newest_on_path :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_newest_on_path y x =
    (if y = x then None
    else max (au_ds ufe_ds x) (find_newest_on_path y (ufe_parent_of ufe_ds x)))"
  by pat_completeness auto

lemma find_newest_on_path_if_eq[simp]:
  "find_newest_on_path x x = None"
  by (meson find_newest_on_path.domintros find_newest_on_path.psimps)

function (domintros) explain' :: "nat \<Rightarrow> nat \<Rightarrow> nat eq_prf" where
  "explain' x y =
    (if x = y then ReflP x
    else 
      let
        lca = ufe_lca ufe_ds x y;
        newest_x = find_newest_on_path lca x;
        newest_y = find_newest_on_path lca y
      in
        if newest_x \<ge> newest_y then
          let (ax, bx) = unions ufe_ds ! the newest_x
          in TransP
            (TransP (explain' x ax) (AssmP (the newest_x)))
            (explain' bx y)
        else
          let (ay, by) = unions ufe_ds ! the newest_y
          in TransP
            (TransP (explain' x by) (SymP (AssmP (the newest_y))))
            (explain' ay y))"
  by pat_completeness auto

lemma explain'_refl[simp]:
  "explain' x x = ReflP x"
  using explain'.domintros explain'.psimps by fastforce

end

end