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
  fixes uf :: 'uf
  fixes au :: 'au
begin

function (domintros) find_newest_on_walk :: "'dom \<Rightarrow> 'dom \<Rightarrow> nat option" where
  "find_newest_on_walk y x =
    (if y = x then None else combine_options max (mm_lookup\<^bsub>au_adt\<^esub> au x) (find_newest_on_walk y (uf_parent_of uf x)))"
  by pat_completeness auto

lemma find_newest_on_walk_if_eq[simp]:
  "find_newest_on_walk x x = None"
  by (meson find_newest_on_walk.domintros find_newest_on_walk.psimps)

context
  fixes unions :: "('dom \<times> 'dom) list"
begin

text \<open>Explain operation, as described in the paper.\<close>
function (domintros) explain :: "'dom \<Rightarrow> 'dom \<Rightarrow> ('dom \<times> 'dom) set" where
  "explain x y = 
    (if x = y \<or> uf_rep_of uf x \<noteq> uf_rep_of uf y then {}
    else 
      let
        lca = ufa_lca uf x y;
        newest_x = find_newest_on_walk lca x;
        newest_y = find_newest_on_walk lca y
      in
        if newest_x \<ge> newest_y then
          let (ax, bx) = unions ! the newest_x
          in {(ax, bx)} \<union> explain x ax \<union> explain bx y
        else
          let (ay, by) = unions ! the newest_y
          in {(ay, by)} \<union> explain x by \<union> explain ay y)"
  by pat_completeness auto

lemma explain_pinduct[consumes 1, case_names eq neq_rep_of newest_x newest_y]:
  assumes "explain_dom (x, y)"
  assumes "\<And>x y. x = y \<Longrightarrow> P x y"
  assumes "\<And>x y. uf_rep_of uf x \<noteq> uf_rep_of uf y \<Longrightarrow> P x y"
  assumes "\<And>x y ulca newest_x newest_y ax bx.
     \<lbrakk> explain_dom (x, y)
     ; x \<noteq> y; uf_rep_of uf x = uf_rep_of uf y
     ; ulca = ufa_lca uf x y
     ; newest_x = find_newest_on_walk ulca x
     ; newest_y = find_newest_on_walk ulca y
     ; newest_x \<ge> newest_y
     ; unions ! the newest_x = (ax, bx)
     ; P x ax; P bx y
     \<rbrakk> \<Longrightarrow> P x y"
  assumes "\<And>x y ulca newest_x newest_y ay by.
     \<lbrakk> explain_dom (x, y)
     ; x \<noteq> y; uf_rep_of uf x = uf_rep_of uf y
     ; ulca = ufa_lca uf x y
     ; newest_x = find_newest_on_walk ulca x
     ; newest_y = find_newest_on_walk ulca y
     ; newest_x < newest_y
     ; unions ! the newest_y = (ay, by)
     ; P x by; P ay y
     \<rbrakk> \<Longrightarrow> P x y"
  shows "P x y"
  using assms(1)
proof(induction rule: explain.pinduct)
  case (1 x y)
  note assms(2,3) assms(4,5)[OF this(1)]
  with "1"(2-)[OF _ HOL.refl HOL.refl HOL.refl _ HOL.refl] show ?case
    by (smt (z3) find_newest_on_walk.cases linorder_not_le)
qed

lemma explain_base_domintros[simp, intro]:
  shows "x = y \<Longrightarrow> explain_dom (x, y)"
    and "uf_rep_of uf x \<noteq> uf_rep_of uf y \<Longrightarrow> explain_dom (x, y)"
  using explain.domintros[where ?x=x and ?y=y]
  by simp_all

lemma explain_newest_x_domintro:
  assumes "x \<noteq> y" "uf_rep_of uf x = uf_rep_of uf y"
  assumes "ulca = ufa_lca uf x y"
  assumes "newest_x = find_newest_on_walk ulca x"
  assumes "newest_y = find_newest_on_walk ulca y"
  assumes "newest_x \<ge> newest_y"
  assumes "unions ! the newest_x = (ax, bx)"
  assumes "explain_dom (x, ax)" "explain_dom (bx, y)"
  shows "explain_dom (x, y)"
  apply(rule explain.domintros)
  using assms by simp_all

lemma explain_newest_y_domintro:
  assumes "x \<noteq> y" "uf_rep_of uf x = uf_rep_of uf y"
  assumes "ulca = ufa_lca uf x y"
  assumes "newest_x = find_newest_on_walk ulca x"
  assumes "newest_y = find_newest_on_walk ulca y"
  assumes "newest_x < newest_y"
  assumes "unions ! the newest_y = (ay, by)"
  assumes "explain_dom (x, by)" "explain_dom (ay, y)"
  shows "explain_dom (x, y)"
  apply(rule explain.domintros)
  using assms by simp_all

lemma explain_dom_newest_xD:
  assumes "explain_dom (x, y)"
  assumes "x \<noteq> y" "uf_rep_of uf x = uf_rep_of uf y"
  assumes "ulca = ufa_lca uf x y"
  assumes "newest_x = find_newest_on_walk ulca x"
  assumes "newest_y = find_newest_on_walk ulca y"
  assumes "unions ! the newest_x = (ax, bx)"
  assumes "newest_x \<ge> newest_y"
  shows "explain_dom (x, ax)" "explain_dom (bx, y)"
  using assms
  by (auto intro: accp_downward[OF assms(1)] simp: explain_rel.intros)

lemma explain_dom_newest_yD:
  assumes "explain_dom (x, y)"
  assumes "x \<noteq> y" "uf_rep_of uf x = uf_rep_of uf y"
  assumes "ulca = ufa_lca uf x y"
  assumes "newest_x = find_newest_on_walk ulca x"
  assumes "newest_y = find_newest_on_walk ulca y"
  assumes "unions ! the newest_y = (ay, by)"
  assumes "newest_x < newest_y"
  shows "explain_dom (x, by)" "explain_dom (ay, y)"
  using assms
  by (auto intro: accp_downward[OF assms(1)] simp: explain_rel.intros)

(*
lemma explain_dom_cases:
  assumes "explain_dom (x, y)"
  obtains
    (eq) "x = y"
  | (neq_rep_of) "rep_of l x \<noteq> rep_of l y"
  | (step) ulca newest_x newest_y ax bx where
      "x \<noteq> y" "rep_of l x = rep_of l y"
      "ulca = ufa_lca uf x y"
      "newest_x = find_newest_on_walk ulca x"
      "newest_y = find_newest_on_walk ulca y"
      "newest_x \<ge> newest_y"
      "unions ! nat newest_x = (ax, bx)"
      "explain_dom (x, ax)" "explain_dom (bx, y)"
  | (sym) ulca newest_x newest_y ay "by" where
      "x \<noteq> y" "rep_of l x = rep_of l y"
      "ulca = ufa_lca uf x y"
      "newest_x = find_newest_on_walk ulca x"
      "newest_y = find_newest_on_walk ulca y"
      "newest_x < newest_y"
      "unions ! nat newest_y = (ay, by)"
      "explain_dom (x, by)" "explain_dom (ay, y)"
  using explain_pinduct[OF assms]  *)


end

end

(*
text \<open>The \<open>explain.cases\<close> theorem is not very useful, we define a better one.
      It also defines variables which will be useful in the proofs. \<close>
thm explain.cases
lemma explain_cases:
  obtains (base) ufe 
  where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x = y \<or> rep_of l x \<noteq> rep_of l y"
  | (case_x) ufe lca newest_index_x newest_index_y ax bx ay "by"
  where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = ufa_lca uf x y"
    and "newest_index_x = find_newest_on_walk l a x lca"
    and "newest_index_y = find_newest_on_walk l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)" 
    and "(ay, by) = u ! the (newest_index_y)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)" 
    and "newest_index_x \<ge> newest_index_y"
  | (case_y) ufe lca newest_index_x newest_index_y ax bx ay "by"
  where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = ufa_lca uf x y"
    and "newest_index_x = find_newest_on_walk l a x lca"
    and "newest_index_y = find_newest_on_walk l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)" 
    and "(ay, by) = u ! the (newest_index_y)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "\<not>(newest_index_x \<ge> newest_index_y)"
  by (metis prod.exhaust)

text \<open>We also rewrite the \<open>explain.domintros\<close> to a simpler form.\<close>
thm explain.domintros
lemma explain_empty_domain:
  "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr> 
  \<Longrightarrow> x = y \<or> rep_of l x \<noteq> rep_of l y  
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y)"
  using explain.domintros by blast

lemma explain_case_x_domain:
  "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr> 
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, ax)
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, bx, y)
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = ufa_lca uf x y
  \<Longrightarrow> newest_index_x = find_newest_on_walk l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_walk l a y lca
  \<Longrightarrow> (ax, bx) = u ! the (newest_index_x)
  \<Longrightarrow> newest_index_x \<ge> newest_index_y
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) "
  using explain.domintros 
  by (smt (verit, best) Pair_inject ufa_lca_def)

lemma explain_case_y_domain:
  "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr> 
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, by)
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, ay, y)
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = ufa_lca uf x y
  \<Longrightarrow> newest_index_x = find_newest_on_walk l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_walk l a y lca
  \<Longrightarrow> (ay, by) = u !  the (newest_index_y)
  \<Longrightarrow> \<not>(newest_index_x \<ge> newest_index_y)
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) "
  using explain.domintros
  by (smt (verit, best) ufa_lca_def prod.inject)

text \<open>And we also rewrite the simp rules:\<close>
lemma explain_empty[simp]:
  "x = y \<or> rep_of (uf_list ufe) x \<noteq> rep_of (uf_list ufe) y  
  \<Longrightarrow> explain ufe x y = {}"
  using explain_empty_domain ufe_data_structure.cases explain.psimps
  by (metis (no_types, opaque_lifting) ufe_data_structure.select_convs(1))

lemma explain_case_x[simp]:
  "explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) 
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = ufa_lca uf x y
  \<Longrightarrow> newest_index_x = find_newest_on_walk l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_walk l a y lca
  \<Longrightarrow> (ax, bx) = u ! the (newest_index_x)
  \<Longrightarrow> newest_index_x \<ge> newest_index_y
  \<Longrightarrow> explain  \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
          {(ax, bx)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax 
             \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y"
  by (auto simp add: explain.psimps Let_def) 

lemma explain_case_y[simp]:
  "explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) 
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = ufa_lca uf x y
  \<Longrightarrow> newest_index_x = find_newest_on_walk l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_walk l a y lca
  \<Longrightarrow> (ay, by) = u !  the (newest_index_y)
  \<Longrightarrow> \<not>(newest_index_x \<ge> newest_index_y)
  \<Longrightarrow> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
          {(ay, by)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by 
            \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y"
  by (auto simp add: explain.psimps Let_def)  
*)

(*
subsection \<open>Lemmas about \<open>rep_of\<close>\<close>

lemma rep_of_domain: "rep_of_dom (l, i) \<Longrightarrow> l ! i \<noteq> i \<Longrightarrow> rep_of_dom (l, l ! i)"
  apply(induction rule: rep_of.pinduct)
  using rep_of.domintros by blast

lemma rep_of_idx2: 
  "rep_of_dom (l, i) \<Longrightarrow> rep_of l (l ! i) = rep_of l i"
  by (simp add: rep_of.psimps)

lemma ufe_union_uf_list:
  assumes "ufa_invar (uf_list ufe)" "x < length (uf_list ufe)"
    shows "uf_list (ufe_union ufe x y) = ufa_union (uf_list ufe) x y"
proof (cases "uf_rep_of (uf_list ufe) x = uf_rep_of (uf_list ufe) y")
  case True
  with assms rep_of_min have
    "(uf_list ufe) ! uf_rep_of (uf_list ufe) x = uf_rep_of (uf_list ufe) y" 
    by metis
  with True have "ufa_union (uf_list ufe) x y = uf_list ufe" 
    by (metis list_update_id)
  with True show ?thesis
    by (cases ufe) simp
next
  case False
  then show ?thesis
    by (cases ufe) simp_all
qed
*)

end

end