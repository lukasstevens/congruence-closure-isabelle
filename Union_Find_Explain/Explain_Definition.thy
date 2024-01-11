chapter \<open>Union-Find Data-Structure with Explain Operation\<close>
theory Explain_Definition
  imports 
    "Separation_Logic_Imperative_HOL.Union_Find" 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Tree"
begin
 

no_notation Ref.update ("_ := _" 62)

text \<open>
  Formalization of an explain operation, based on the Union Find implementation
  of \<open>Separation_Logic_Imperative_HOL.Union_Find\<close>. Path compression is omitted.
  Reference paper: Proof-Producing Congruence Closure, Robert Nieuwenhuis and Albert Oliveras
\<close>

subsection \<open>Definitions\<close>
text \<open>
Data structure for the union, find and explain operations:
  \<open>uf_list\<close>: parents of the tree data structure without path compression
  \<open>unions\<close>: list of all the union operations made 
  \<open>au\<close>: (associated union) contains which union corresponds to each edge
\<close>
record ufe_data_structure =
  uf_list :: "nat list"
  unions :: "(nat * nat) list"
  au :: "int list"

text \<open>For the initialisation of the union find algorithm.\<close>
term upto
abbreviation "initial_ufe n \<equiv> \<lparr> uf_list = [0..<n], unions = []
                              , au = [-n .. -1] \<rparr>"

paragraph \<open>Union\<close>
text \<open>Extension of the union operations to the \<open>ufe_data_structure\<close>.\<close>
fun ufe_union :: "ufe_data_structure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe_data_structure" where
  "ufe_union \<lparr> uf_list = l, unions = u, au = a \<rparr> x y =
    (if rep_of l x \<noteq> rep_of l y then
      \<lparr> uf_list = ufa_union l x y
      , unions = u @ [(x, y)]
      , au = a[rep_of l x := length u]
      \<rparr>
    else \<lparr> uf_list = l, unions = u, au = a \<rparr>)"

text \<open>Helper lemmata for \<open>ufe_union\<close>.\<close>
(*
lemma ufe_union1[simp]:
  "rep_of l x = rep_of l y \<Longrightarrow> ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
  by simp
lemma ufe_union1_ufe[simp]:
  "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y \<Longrightarrow> ufe_union ufe x y = ufe"
  by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
lemma ufe_union1_uf_list[simp]:
  "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y \<Longrightarrow> uf_list (ufe_union ufe x y) = uf_list ufe"
  by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
lemma ufe_union1_unions[simp]:
  "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y \<Longrightarrow> unions (ufe_union ufe x y) = unions ufe"
  by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
lemma ufe_union1_au[simp]:
  "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y \<Longrightarrow> au (ufe_union ufe x y) = au ufe"
  by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
lemma ufe_union2[simp]:
  "rep_of l x \<noteq> rep_of l y \<Longrightarrow> ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = \<lparr>uf_list = ufa_union l x y,
     unions = u @ [(x,y)],
     au =  a[rep_of l x := Some (length u)]\<rparr>"
  by simp
lemma ufe_union2_uf_list[simp]:
  "rep_of (uf_list ufe) x \<noteq> rep_of (uf_list ufe) y \<Longrightarrow> uf_list (ufe_union ufe x y) = ufa_union (uf_list ufe) x y"
  using ufe_data_structure.cases ufe_union2 by (metis ufe_data_structure.select_convs(1))
lemma ufe_union2_unions[simp]:
  "rep_of (uf_list ufe) x \<noteq> rep_of (uf_list ufe) y \<Longrightarrow> unions (ufe_union ufe x y) = unions ufe @ [(x,y)]"
  using ufe_data_structure.cases ufe_union2 by (metis ufe_data_structure.select_convs(1,2))
lemma ufe_union2_au[simp]:
  "rep_of (uf_list ufe) x \<noteq> rep_of (uf_list ufe) y \<Longrightarrow> au (ufe_union ufe x y) = (au ufe)[rep_of (uf_list ufe) x := Some (length (unions ufe))]"
  using ufe_data_structure.cases ufe_union2 by (metis ufe_data_structure.select_convs(1,2,3))

lemma P_ufe_unionE[consumes 1, case_names rep_neq]:
  assumes "P l u a"
  assumes "\<And> x y. rep_of l x \<noteq> rep_of l y \<Longrightarrow> 
          P (ufa_union l x y) (u @ [(x,y)]) (a[rep_of l x := length u])"
  shows "P (uf_list (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y)) 
           (unions (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y)) 
           (au (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y))"
  using assms by auto
*)

text \<open>For the application of a list of unions.\<close>
fun apply_unions :: "(nat * nat) list \<Rightarrow> ufe_data_structure \<Rightarrow> ufe_data_structure" where
  "apply_unions [] p = p"
| "apply_unions ((x, y) # u) p = apply_unions u (ufe_union p x y)"

lemma apply_unions_append:
  "apply_unions u1 a = b \<Longrightarrow> apply_unions u2 b = c \<Longrightarrow> apply_unions (u1 @ u2) a = c"
  by (induction u1 a rule: apply_unions.induct) simp_all

paragraph \<open>Explain\<close>

text \<open>Finds the lowest common ancestor of x and y in the
      tree represented by the array l.\<close>
context union_find_parent
begin

definition ufa_lca :: "'uf \<Rightarrow> 'dom \<Rightarrow> 'dom \<Rightarrow> 'dom" where
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
context union_find_explain
begin

context
  fixes uf :: 'uf
  fixes au :: 'au
begin

term combine_options
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