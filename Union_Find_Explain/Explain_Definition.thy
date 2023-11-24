chapter \<open>Union-Find Data-Structure with Explain Operation\<close>
theory Explain_Definition
  imports 
    "Separation_Logic_Imperative_HOL.Union_Find" 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Tree"
begin

locale union_find =
  fixes init :: 'c
    and rep_of :: "'c \<Rightarrow> 'a \<Rightarrow> 'a"
    and union :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'c"
    and invar :: "'c \<Rightarrow> bool"
    and \<alpha> :: "'c \<Rightarrow> 'a rel"
  assumes invar_init: "invar init"
      and \<alpha>_init: "\<alpha> init \<subseteq> Id" 
      and \<alpha>_rep_of:
        "\<lbrakk> invar l; x \<in> Field (\<alpha> l); y \<in> Field (\<alpha> l) \<rbrakk>
        \<Longrightarrow> rep_of l x = rep_of l y \<longleftrightarrow> (x, y) \<in> \<alpha> l"
      and invar_union:
        "\<lbrakk> invar l; x \<in> Field (\<alpha> l); y \<in> Field (\<alpha> l) \<rbrakk>
        \<Longrightarrow> invar (union l x y)"
      and \<alpha>_union:
        "\<lbrakk> invar l; x \<in> Field (\<alpha> l); y \<in> Field (\<alpha> l) \<rbrakk>
        \<Longrightarrow> \<alpha> (union l x y) = per_union (\<alpha> l) x y"

lemma union_find_ufa:
  "union_find [0..<n] rep_of ufa_union ufa_invar ufa_\<alpha>"
proof -
  note [simp] = ufa_init_invar ufa_init_correct
    ufa_find_correct ufa_union_invar ufa_union_correct
  show ?thesis
    by unfold_locales (auto simp: Field_iff ufa_\<alpha>_lenD)
qed

locale union_find_explain =
  union_find init rep_of union invar "\<alpha> :: 'c \<Rightarrow> 'a rel" for init rep_of union invar \<alpha> +

fixes explain :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set"
assumes \<alpha>_explain:
  "\<lbrakk> invar l; x \<in> Field (\<alpha> l); y \<in> Field (\<alpha> l); (x, y) \<in> \<alpha> l \<rbrakk>
  \<Longrightarrow> (x, y) \<in> (explain l x y)\<^sup>*"
    

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
  au :: "nat option list"

text \<open>For the initialisation of the union find algorithm.\<close>
abbreviation "initial_ufe n \<equiv> \<lparr> uf_list = [0..<n], unions = [], au = replicate n None \<rparr>"

paragraph \<open>Union\<close>
text \<open>Extension of the union operations to the \<open>ufe_data_structure\<close>.\<close>
fun ufe_union :: "ufe_data_structure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe_data_structure" where
  "ufe_union \<lparr> uf_list = l, unions = u, au = a \<rparr> x y =
    (if rep_of l x \<noteq> rep_of l y then
      \<lparr> uf_list = ufa_union l x y
      , unions = u @ [(x,y)]
      , au = a[rep_of l x := Some (length u)]
      \<rparr>
    else \<lparr> uf_list = l, unions = u, au = a \<rparr>)"

text \<open>Helper lemmata for \<open>ufe_union\<close>.\<close>
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
          P (ufa_union l x y) (u @ [(x,y)]) (a[rep_of l x := Some (length u)])"
  shows "P (uf_list (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y)) 
           (unions (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y)) 
           (au (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y))"
  using assms by auto

text \<open>For the application of a list of unions.\<close>
fun apply_unions :: "(nat * nat) list \<Rightarrow> ufe_data_structure \<Rightarrow> ufe_data_structure" where
  "apply_unions [] p = p"
| "apply_unions ((x, y) # u) p = apply_unions u (ufe_union p x y)"

lemma apply_unions_cons:
  "apply_unions u1 a = b \<Longrightarrow> apply_unions u2 b = c \<Longrightarrow> apply_unions (u1 @ u2) a = c"
  by (induction u1 a rule: apply_unions.induct) simp_all

paragraph \<open>Explain\<close>

text \<open>Finds the lowest common ancestor of x and y in the
      tree represented by the array l.\<close>
definition lowest_common_ancestor :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lowest_common_ancestor l x y \<equiv> 
    snd (last (longest_common_prefix (awalk_from_rep l x) (awalk_from_rep l y)))"

lemma lowest_common_ancestor_symmetric:
  "lowest_common_ancestor l x y = lowest_common_ancestor l y x"
proof -
  have
    "longest_common_prefix (awalk_from_rep l x) (awalk_from_rep l y)
    = longest_common_prefix (awalk_from_rep l y) (awalk_from_rep l x)"
    by (simp add: longest_common_prefix_max_prefix longest_common_prefix_prefix1
          longest_common_prefix_prefix2 prefix_order.eq_iff)
  then show ?thesis
    unfolding lowest_common_ancestor_def by auto
qed

text \<open>Finds the newest edge on the path from x to y
      (where y is nearer to the root than x).\<close>
function (domintros) find_newest_on_path ::
  "nat list \<Rightarrow> nat option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_newest_on_path l a x y = 
    (if x = y then None else max (a ! x) (find_newest_on_path l a (l ! x) y))"
  by pat_completeness auto

text \<open>Explain operation, as described in the paper.\<close>
function (domintros) explain :: "ufe_data_structure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat * nat) set" where
  "explain \<lparr> uf_list = l, unions = u, au = a \<rparr> x y = 
    (if x = y \<or> rep_of l x \<noteq> rep_of l y then {}
    else 
      let
        lca = lowest_common_ancestor l x y;
        newest_index_x = find_newest_on_path l a x lca;
        newest_index_y = find_newest_on_path l a y lca
      in
      if newest_index_x \<ge> newest_index_y then
        let (ax, bx) = u ! the (newest_index_x) in
          {(ax, bx)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax 
            \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y
      else 
        let (ay, by) = u ! the (newest_index_y) in
          {(ay, by)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by 
            \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y
  )"
  by pat_completeness auto

text \<open>The \<open>explain.cases\<close> theorem is not very useful, we define a better one.
      It also defines variables which will be useful in the proofs. \<close>
thm explain.cases
lemma explain_cases:
  obtains (base) ufe 
  where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x = y \<or> rep_of l x \<noteq> rep_of l y"
  | (case_x) ufe lca newest_index_x newest_index_y ax bx ay "by"
  where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)" 
    and "(ay, by) = u ! the (newest_index_y)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)" 
    and "newest_index_x \<ge> newest_index_y"
  | (case_y) ufe lca newest_index_x newest_index_y ax bx ay "by"
  where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
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
  \<Longrightarrow> lca = lowest_common_ancestor l x y
  \<Longrightarrow> newest_index_x = find_newest_on_path l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_path l a y lca
  \<Longrightarrow> (ax, bx) = u ! the (newest_index_x)
  \<Longrightarrow> newest_index_x \<ge> newest_index_y
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) "
  using explain.domintros 
  by (smt (verit, best) Pair_inject lowest_common_ancestor_def)

lemma explain_case_y_domain:
  "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr> 
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, by)
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, ay, y)
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = lowest_common_ancestor l x y
  \<Longrightarrow> newest_index_x = find_newest_on_path l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_path l a y lca
  \<Longrightarrow> (ay, by) = u !  the (newest_index_y)
  \<Longrightarrow> \<not>(newest_index_x \<ge> newest_index_y)
  \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) "
  using explain.domintros
  by (smt (verit, best) lowest_common_ancestor_def prod.inject)

text \<open>And we also rewrite the simp rules:\<close>
lemma explain_empty[simp]:
  "x = y \<or> rep_of (uf_list ufe) x \<noteq> rep_of (uf_list ufe) y  
  \<Longrightarrow> explain ufe x y = {}"
  using explain_empty_domain ufe_data_structure.cases explain.psimps
  by (metis (no_types, opaque_lifting) ufe_data_structure.select_convs(1))

lemma explain_case_x[simp]:
  "explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) 
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = lowest_common_ancestor l x y
  \<Longrightarrow> newest_index_x = find_newest_on_path l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_path l a y lca
  \<Longrightarrow> (ax, bx) = u ! the (newest_index_x)
  \<Longrightarrow> newest_index_x \<ge> newest_index_y
  \<Longrightarrow> explain  \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
          {(ax, bx)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax 
             \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y"
  by (auto simp add: explain.psimps Let_def) 

lemma explain_case_y[simp]:
  "explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, y) 
  \<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)   
  \<Longrightarrow> lca = lowest_common_ancestor l x y
  \<Longrightarrow> newest_index_x = find_newest_on_path l a x lca
  \<Longrightarrow> newest_index_y = find_newest_on_path l a y lca
  \<Longrightarrow> (ay, by) = u !  the (newest_index_y)
  \<Longrightarrow> \<not>(newest_index_x \<ge> newest_index_y)
  \<Longrightarrow> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
          {(ay, by)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by 
            \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y"
  by (auto simp add: explain.psimps Let_def)  

subsection \<open>Lemmas about \<open>rep_of\<close>\<close>

lemma rep_of_domain: "rep_of_dom (l, i) \<Longrightarrow> l ! i \<noteq> i \<Longrightarrow> rep_of_dom (l, l ! i)"
  apply(induction rule: rep_of.pinduct)
  using rep_of.domintros by blast

lemma rep_of_idx2: 
  "rep_of_dom (l, i) \<Longrightarrow> rep_of l (l ! i) = rep_of l i"
  by (simp add: rep_of.psimps)

lemma ufe_union_uf_list:
  "ufa_invar (uf_list ufe) \<Longrightarrow> x < length (uf_list ufe) 
  \<Longrightarrow> uf_list (ufe_union ufe x y) = ufa_union (uf_list ufe) x y"
proof (cases "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y")
  case True
  assume invar: "ufa_invar (uf_list ufe)" "x < length (uf_list ufe)"
  from True invar rep_of_min have "(uf_list ufe) ! rep_of (uf_list ufe) x = rep_of (uf_list ufe) y" 
    by metis
  with True have "ufa_union (uf_list ufe) x y = uf_list ufe" 
    by (metis list_update_id)
  then show ?thesis 
    by (simp add: True)
next
  case False
  then show ?thesis
    using ufe_data_structure.cases ufe_union2
    by (metis ufe_data_structure.select_convs(1))
qed

lemma ufa_union_root: 
  assumes "ufa_union l a b ! i = i" "ufa_invar l" 
      and "a < length l" "b < length l"
  shows "l ! i = i"
  using assms by (metis nth_list_update_neq rep_of_min)

end