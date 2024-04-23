chapter \<open>Union-Find Data-Structure with Explain Operation\<close>
theory Explain_Definition
  imports 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Tree"
begin
 

no_notation Ref.update ("_ := _" 62)

subsection \<open>Definitions\<close>

record ('uf, 'au, 'dom) union_find_explain_ds =
  uf_ds :: 'uf
  au_ds :: 'au
  unions :: "('dom \<times> 'dom) list"

locale union_find_explain_adts =
  union_find_parent_adt where uf_adt = uf_adt +
  map_mono_adt where mm_adt = au_adt
  for
    uf_adt :: "('uf, 'dom, _) union_find_parent_adt_scheme" (structure) and
    au_adt :: "('au, 'dom, nat, _) map_mono_adt_scheme"
begin

fun ufe_union where
  "ufe_union \<lparr> uf_ds = uf, au_ds = au, unions = u \<rparr> x y =
    (if uf_rep_of uf x \<noteq> uf_rep_of uf y then
      \<lparr> uf_ds = uf_union uf x y
      , au_ds = mm_update\<^bsub>au_adt\<^esub> au (uf_rep_of uf x) (length u)
      , unions = u @ [(x, y)]
      \<rparr>
    else \<lparr> uf_ds = uf, au_ds = au, unions = u \<rparr>)"

definition "ufe_init \<equiv>
  \<lparr> uf_ds = uf_init, au_ds = mm_empty\<^bsub>au_adt\<^esub>, unions = ([] :: ('dom \<times> 'dom) list) \<rparr>"

definition "ufe_unions \<equiv> foldl (\<lambda>ufe_ds (x, y). ufe_union ufe_ds x y)"

abbreviation "ufe_rep_of ufe_ds x \<equiv> uf_rep_of (uf_ds ufe_ds) x"
abbreviation "ufe_parent_of ufe_ds x \<equiv> uf_parent_of (uf_ds ufe_ds) x"

lemma uf_ds_ufe_union:
  "uf_ds (ufe_union ufe_ds x y) =
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
      then uf_ds ufe_ds
      else uf_union (uf_ds ufe_ds) x y)"
  by (cases ufe_ds) simp

lemma au_ds_ufe_union:
  "au_ds (ufe_union ufe_ds x y) =
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
      then au_ds ufe_ds
      else mm_update\<^bsub>au_adt\<^esub> (au_ds ufe_ds) (ufe_rep_of ufe_ds x) (length (unions ufe_ds)))"
  by (cases ufe_ds) simp

lemma unions_ufe_union:
  "unions (ufe_union ufe_ds x y) =
    (if ufe_rep_of ufe_ds x = ufe_rep_of ufe_ds y
      then unions ufe_ds
      else unions ufe_ds @ [(x, y)])"
  by (cases ufe_ds) simp

lemmas ufe_union_sel = uf_ds_ufe_union au_ds_ufe_union unions_ufe_union

lemma ufe_union_sel_if_rep_of_neq[simp]:
  assumes "ufe_rep_of ufe_ds x \<noteq> ufe_rep_of ufe_ds y"
  shows
    "uf_ds (ufe_union ufe_ds x y) = uf_union (uf_ds ufe_ds) x y"
    "au_ds (ufe_union ufe_ds x y) =
      mm_update\<^bsub>au_adt\<^esub> (au_ds ufe_ds) (ufe_rep_of ufe_ds x) (length (unions ufe_ds))"
    "unions (ufe_union ufe_ds x y) = unions ufe_ds @ [(x, y)]"
  using assms
  by (simp_all add: ufe_union_sel)

lemma ufe_init_sel[simp]:
  "uf_ds ufe_init = uf_init"
  "au_ds ufe_init = mm_empty\<^bsub>au_adt\<^esub>"
  "unions ufe_init = []"
  unfolding ufe_init_def by simp_all

lemma ufe_unions_append[simp]:
  "ufe_unions ufe_ds (us1 @ us2) = ufe_unions (ufe_unions ufe_ds us1) us2"
  unfolding ufe_unions_def by simp

lemma ufe_unions_Cons[simp]:
  "ufe_unions ufe_ds (u # us) = ufe_unions (ufe_union ufe_ds (fst u) (snd u)) us"
  unfolding ufe_unions_def by (simp add: case_prod_unfold)

lemma ufe_unions_Nil[simp]:
  "ufe_unions ufe_ds [] = ufe_ds"
  unfolding ufe_unions_def by simp

end

context union_find_parent_adt
begin

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

end

text \<open>Finds the newest edge on the path from x to y
      (where y is nearer to the root than x).\<close>
context union_find_explain_adts
begin

context
  fixes ufe_ds :: "('uf, 'au, 'dom) union_find_explain_ds"
begin

function (domintros) find_newest_on_walk :: "'dom \<Rightarrow> 'dom \<Rightarrow> nat option" where
  "find_newest_on_walk y x =
    (if y = x then None
    else 
      combine_options max 
        (mm_lookup\<^bsub>au_adt\<^esub> (au_ds ufe_ds) x)
        (find_newest_on_walk y (uf_parent_of (uf_ds ufe_ds) x)))"
  by pat_completeness auto

lemma find_newest_on_walk_if_eq[simp]:
  "find_newest_on_walk x x = None"
  by (meson find_newest_on_walk.domintros find_newest_on_walk.psimps)

end

function explain :: "('dom \<times> 'dom) list \<Rightarrow> 'dom \<Rightarrow> 'dom \<Rightarrow> ('dom \<times> 'dom) set" where
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