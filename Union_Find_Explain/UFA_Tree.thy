theory UFA_Tree
  imports
    "Separation_Logic_Imperative_HOL.Union_Find"
    "Tree_Theory.LCA_Directed_Tree"
begin

definition "ufa_tree_of l x \<equiv>
  let
    vs = {y. y < length l \<and> rep_of l y = rep_of l x}
  in
    \<lparr> pverts = vs
    , parcs = {(l ! x, x) |x. x \<in> vs \<and> l ! x \<noteq> x}
    \<rparr>"

function (domintros) awalk_from_rep :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "awalk_from_rep l x =
    (if l ! x = x then [] else awalk_from_rep l (l ! x) @ [(l ! x, x)])"
  by auto

function (domintros) awalk_verts_from_rep :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "awalk_verts_from_rep l x =
    (if l ! x = x then [] else awalk_verts_from_rep l (l ! x)) @ [x]"
  by auto

lemma awalk_from_rep_dom_if_rep_of_dom[simp, intro]:
  "rep_of_dom (l, x) \<Longrightarrow> awalk_from_rep_dom (l, x)"
  using awalk_from_rep.domintros rep_of.pinduct
  by (metis curryE curryI)

lemma awalk_verts_from_rep_dom_if_rep_of_dom[simp, intro]:
  "rep_of_dom (l, x) \<Longrightarrow> awalk_verts_from_rep_dom (l, x)"
  using awalk_verts_from_rep.domintros rep_of.pinduct
  by (metis curryE curryI)

locale ufa_invars =
  fixes l
  assumes ufa_invar: "ufa_invar l"
begin

lemmas
  rep_of_dom_if_lt_length[simp, intro] = ufa_invarD(1)[OF ufa_invar] and
  idx_lt_length_if_lt_length[simp, intro] = ufa_invarD(2)[OF ufa_invar] and
  rep_of_idx[simp] = rep_of_idx[OF ufa_invar] and
  rep_of_idem[simp] = rep_of_idem[OF ufa_invar] and
  rep_of_iff = rep_of_iff[OF ufa_invar] and
  rep_of_min = rep_of_min[OF ufa_invar] and
  rep_of_bound[simp, intro] = rep_of_bound[OF ufa_invar] and
  rep_of_induct = rep_of_induct[OF ufa_invar, case_names base step, consumes 1] and
  ufa_union_invar[simp, intro] = ufa_union_invar[OF ufa_invar] and
  ufa_union_aux = ufa_union_aux[OF ufa_invar]
 
lemma verts_ufa_tree_of:
  "verts (ufa_tree_of l x) = {y. y < length l \<and> rep_of l y = rep_of l x}"
  unfolding ufa_tree_of_def by simp

lemma in_vertsI[intro]:
  assumes "y < length l" "rep_of l y = rep_of l x"
  shows "y \<in> verts (ufa_tree_of l x)"
  using assms unfolding verts_ufa_tree_of by blast

lemma ufa_tree_of_eq_if_in_verts:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "ufa_tree_of l y = ufa_tree_of l x"
  using assms unfolding ufa_tree_of_def by auto

lemma in_verts_ufa_tree_ofD:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "y < length l" "rep_of l y = rep_of l x"
  using assms verts_ufa_tree_of by simp_all

lemmas
  rep_of_dom_if_in_verts = rep_of_dom_if_lt_length[OF in_verts_ufa_tree_ofD(1)] and
  idx_lt_length_if_in_verts = idx_lt_length_if_lt_length[OF in_verts_ufa_tree_ofD(1)]

lemma idx_in_verts_ufa_tree_ofI[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "l ! y \<in> verts (ufa_tree_of l x)"
  using assms by (fastforce simp: in_verts_ufa_tree_ofD)

end

locale ufa_tree = ufa_invars l for l + 
  fixes x assumes lt_length[simp, intro]: "x < length l"
begin

sublocale fin_digraph "ufa_tree_of l x"
  using ufa_invar lt_length
  by (unfold_locales) (auto simp: ufa_tree_of_def)

lemma x_in_verts[simp, intro]: "x \<in> verts (ufa_tree_of l x)"
  using lt_length unfolding verts_ufa_tree_of by simp

lemma ufa_tree_of_idx[simp]:
  "ufa_tree_of l (l ! x) = ufa_tree_of l x"
  unfolding ufa_tree_of_def by auto

lemma ufa_tree_of_rep_of[simp]:
  "ufa_tree_of l (rep_of l x) = ufa_tree_of l x"
  unfolding ufa_tree_of_def by auto

lemma awalk_idx:
  assumes "y \<in> verts (ufa_tree_of l x)"
  assumes "l ! y \<noteq> y"
  shows "awalk (l ! y) [(l ! y, y)] y"
  using assms arc_implies_awalk
  unfolding ufa_tree_of_def by auto

lemma awalk_from_rep_rep_of:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awalk_from_rep l (rep_of l y) = []"
proof -
  from in_verts_ufa_tree_ofD(2)[OF assms] have "rep_of l y = rep_of l x" .
  with rep_of_min[OF lt_length, folded this] show ?thesis
    by (metis awalk_from_rep.domintros awalk_from_rep.psimps)
qed

lemma rep_of_if_idx_same:
  assumes "y \<in> verts (ufa_tree_of l x)" "z \<in> verts (ufa_tree_of l x)"
  assumes "l ! y = y"
  shows "rep_of l z = y"
  using assms
  by (metis in_verts_ufa_tree_ofD rep_of_iff)
                        
lemma awlast_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awlast (rep_of l x) (awalk_from_rep l y) = y"
proof -
  from assms have "awalk_from_rep_dom (l, y)"
    by (simp add: in_verts_ufa_tree_ofD(1))
  then show ?thesis
    using assms rep_of_if_idx_same[OF _ x_in_verts]
    by (induction rule: awalk_from_rep.pinduct)
      (auto simp: awalk_from_rep.psimps pre_digraph.awalk_verts_conv)
qed

lemma awalk_awalk_from_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awalk (rep_of l y) (awalk_from_rep l y) y"
  using in_verts_ufa_tree_ofD(1)[OF assms] assms
proof(induction rule: rep_of_induct)
  case (base i)
  from base have "awalk_from_rep l i = []"
    by (metis awalk_from_rep_rep_of rep_of_refl)
  with base show "?case"
    by (simp add: awalk_Nil_iff rep_of_simps)
next
  case (step i)
  from step have "awalk (rep_of l i) (awalk_from_rep l (l ! i)) (l ! i)"
    by fastforce
  moreover have "awalk (l ! i) [(l ! i, i)] i"
    using step by (metis awalk_idx ufa_tree_of_eq_if_in_verts)
  ultimately show ?case
    using step by (simp add: awalk_from_rep.psimps)
qed

lemma unique_awalk_ufa_tree_of_rep:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "\<exists>!p. awalk (rep_of l x) p y"
proof
  note in_verts_ufa_tree_ofD[OF assms]
  then interpret y: ufa_tree l y
    by (unfold_locales) auto
  from \<open>rep_of l y = rep_of l x\<close> show "awalk (rep_of l x) (awalk_from_rep l y) y"
    using assms y.awalk_awalk_from_rep
    using ufa_tree_of_eq_if_in_verts by force

  show "p = awalk_from_rep l y" if "awalk (rep_of l x) p y" for p
    using that \<open>y < length l\<close> \<open>rep_of l y = rep_of l x\<close>
  proof(induction p arbitrary: y rule: rev_induct)
    case Nil
    then show ?case
      using awalk_from_rep_rep_of
      by (fastforce simp: awalk_Nil_iff)
  next
    case (snoc a p)
    then have "awalk (rep_of l x) p (fst a)" "a \<in> arcs (ufa_tree_of l x)"
      by auto
    then have "a = (l ! y, y)" "l ! y \<noteq> y"
      unfolding ufa_tree_of_def using snoc.prems(1) by auto
    note snoc.IH[OF \<open>awalk (rep_of l x) p (fst a)\<close>]
    with snoc.prems have "p = awalk_from_rep l (l ! y)"
      unfolding \<open>a = (l ! y, y)\<close> by simp
    with \<open>a = (l ! y, y)\<close> \<open>l ! y \<noteq> y\<close> snoc.prems show ?case
      by (auto simp: awalk_from_rep.psimps[where ?x=y])
  qed
qed

lemma eq_awalk_from_rep_if_awalk_rep_of:
  assumes "y \<in> verts (ufa_tree_of l x)"
  assumes "awalk (rep_of l y) p y"
  shows "p = awalk_from_rep l y"
  using assms awalk_awalk_from_rep unique_awalk_ufa_tree_of_rep
  using in_verts_ufa_tree_ofD(2) by auto

sublocale fin_directed_tree "ufa_tree_of l x" "rep_of l x"
  using unique_awalk_ufa_tree_of_rep
  by unfold_locales (use verts_ufa_tree_of in auto)

lemma awalk_verts_from_rep_eq_awalk_verts:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "awalk_verts_from_rep l y = awalk_verts (rep_of l y) (awalk_from_rep l y)"
proof -
  from in_verts_ufa_tree_ofD(1)[OF assms] show ?thesis
    using assms
  proof(induction rule: rep_of_induct)
    case (base i)
    from base show ?case
      using rep_of_refl
      by (simp add: awalk_verts_from_rep.psimps awalk_from_rep.psimps)
  next
    case (step i)
    from step have "rep_of l (l ! i) = rep_of l i"
      by simp
    with step have "awalk (rep_of l i) (awalk_from_rep l (l ! i)) (l ! i)"
      using awalk_awalk_from_rep by (metis idx_in_verts_ufa_tree_ofI)
    note awalk_appendI[OF this awalk_idx]
    with step have "awalk (rep_of l i) (awalk_from_rep l (l ! i) @ [(l ! i, i)]) i"
      by blast
    note awalk_verts_append[OF this]
    moreover from step have "awalk_verts_from_rep l (l ! i)
      = awalk_verts (rep_of l i) (awalk_from_rep l (l ! i))"
      using idx_in_verts_ufa_tree_ofI by simp
    ultimately show ?case
      using step
      by (auto simp: awalk_verts_from_rep.psimps[where ?x=i] awalk_from_rep.psimps[where ?x=i])
  qed
qed

lemma awalk_idx_sameD:
  assumes "awalk z p y"
  assumes "l ! y = y"
  shows "y = z" "p = []"
proof -
  from assms(1) have
    "z \<in> verts (ufa_tree_of l x)" and
    y_in_verts: "y \<in> verts (ufa_tree_of l x)"
    by blast+
  with \<open>l ! y = y\<close> have "\<not> z \<rightarrow>\<^sup>+\<^bsub>ufa_tree_of l x\<^esub> y" for z
    using not_root_if_dominated rep_of_if_idx_same
    by (metis tranclD2 x_in_verts)
  with assms have "z = rep_of l y"
    using rep_of_refl
    by (metis reachable_awalkI reachable_neq_reachable1)
  moreover from \<open>awalk z p y\<close> have "z \<in> verts (ufa_tree_of l x)"
    by blast
  moreover note awalk_awalk_from_rep[OF y_in_verts]
  moreover from \<open>l ! y = y\<close> have "awalk_from_rep l y = []"
    by (meson awalk_from_rep.domintros awalk_from_rep.psimps)
  moreover note eq_awalk_from_rep_if_awalk_rep_of[OF y_in_verts]
  moreover note in_verts_ufa_tree_ofD[OF y_in_verts]
  ultimately show "y = z" "p = []"
    using assms by (metis awalk_ends)+
qed

lemma awlast_butlast_eq_idx_if_awalk:
  assumes "awalk z p y"
  assumes "p \<noteq> []"
  shows "awlast z (butlast p) = l ! y"
proof(cases "l ! y = y")
  case True
  with assms awalk_idx_sameD show ?thesis
    by simp
next
  case False
  from assms have "p = butlast p @ [last p]"
    by simp
  with assms have "awalk (awlast z (butlast p)) [last p] y"
    using awalk_not_Nil_butlastD by blast
  from assms have "y \<in> verts (ufa_tree_of l x)"
    by blast
  with awalk_idx[OF this False] \<open>awalk (awlast z (butlast p)) [last p] y\<close>
  show "awlast z (butlast p) = l ! y"
    by (metis awalk_Cons_iff awalk_empty_ends two_in_arcs_contr)
qed

context
  fixes a b
  assumes a_b_lt_length: "a < length l" "b < length l"
begin

interpretation ufa_tree_union: ufa_tree "ufa_union l a b" x
  using ufa_invar lt_length a_b_lt_length
  by unfold_locales auto

lemma in_verts_ufa_tree_of_union_if_in_verts[simp, intro]:
  assumes "y \<in> verts (ufa_tree_of l x)"
  shows "y \<in> verts (ufa_tree_of (ufa_union l a b) x)"
  using assms a_b_lt_length lt_length ufa_union_aux
  unfolding ufa_tree_of_def
  by auto

lemma in_arcs_ufa_tree_of_union_if_in_arcs[simp, intro]:
  assumes "e \<in> arcs (ufa_tree_of l x)"
  shows "e \<in> arcs (ufa_tree_of (ufa_union l a b) x)"
  using assms lt_length a_b_lt_length rep_of_min
  unfolding ufa_tree_of_def
  by (auto simp: ufa_union_aux) (metis nth_list_update_neq)+

lemma awalk_ufa_union_if_awalk:
  assumes "awalk y p z"
  shows "ufa_tree_union.awalk y p z"
  using assms
proof(induction p arbitrary: y)
  case Nil
  then show ?case
    using in_verts_ufa_tree_of_union_if_in_verts
    by (auto simp: awalk_Nil_iff ufa_tree_union.awalk_Nil_iff)
next
  case (Cons a p)
  then show ?case
    unfolding awalk_Cons_iff ufa_tree_union.awalk_Cons_iff
    using in_arcs_ufa_tree_of_union_if_in_arcs
    by auto
qed

end

end


abbreviation "ufa_unions \<equiv> foldl (\<lambda>l (x, y). ufa_union l x y)"

definition "valid_unions l us \<equiv> \<forall>(x, y) \<in> set us. x < l \<and> y < l"

lemma valid_unions_Nil[simp]:
  "valid_unions l []"
  unfolding valid_unions_def by simp

lemma valid_unions_Cons[simp]:
  "valid_unions l (x # xs) \<longleftrightarrow> fst x < l \<and> snd x < l \<and> valid_unions l xs"
  unfolding valid_unions_def by (simp split: prod.splits)

lemma valid_unions_append[simp]:
  "valid_unions l (xs @ ys) \<longleftrightarrow> valid_unions l xs \<and> valid_unions l ys"
  unfolding valid_unions_def by auto

lemma length_ufa_unions[simp]:
  "length (ufa_unions l as) = length l"
  by (induction as rule: rev_induct) (simp_all split: prod.splits)

lemma valid_unions_takeI[simp, intro]:
  "valid_unions l us \<Longrightarrow> valid_unions l (take i us)"
  unfolding valid_unions_def using in_set_takeD by fast

lemma valid_unions_nthD[simp, dest]:
  assumes "valid_unions (length l) us" "i < length us"
  shows "fst (us ! i) < length l" "snd (us ! i) < length l"
  using assms unfolding valid_unions_def
  using nth_mem by fastforce+

lemma ufa_invar_ufa_unions[simp, intro]:
  assumes "ufa_invar l" "valid_unions (length l) us"
  shows "ufa_invar (ufa_unions l us)"
  using assms
proof(induction us arbitrary: l)
  case (Cons u us)
  then show ?case
    by (cases u) (auto intro: Cons.IH simp: ufa_union_invar)
qed simp

lemma rep_of_neq_if_rep_of_ufa_union_neq:
  assumes "ufa_invar l"
  assumes "x < length l" "y < length l" "j < length l" "k < length l"
  assumes "rep_of (ufa_union l x y) j \<noteq> rep_of (ufa_union l x y) k"
  shows "rep_of l j \<noteq> rep_of l k"
  by (metis assms ufa_union_aux)

lemma rep_of_ufa_unions_take_neq_if_rep_of_ufa_unions_neq:
  assumes "ufa_invar l" "valid_unions (length l) us"
  assumes "j < length l" "k < length l"
  assumes "rep_of (ufa_unions l us) j \<noteq> rep_of (ufa_unions l us) k"
  shows "rep_of (ufa_unions l (take i us)) j \<noteq> rep_of (ufa_unions l (take i us)) k"
  using assms
proof(induction us arbitrary: i rule: rev_induct)
  case (snoc u us)
  from snoc have "ufa_invar (ufa_unions l us)"
    by auto
  from snoc have rep_of_ufa_union:
    "rep_of (ufa_union (ufa_unions l us) (fst u) (snd u)) j
    \<noteq> rep_of (ufa_union (ufa_unions l us) (fst u) (snd u)) k"
    by (cases u) simp
  note rep_of_neq_if_rep_of_ufa_union_neq[OF \<open>ufa_invar (ufa_unions l us)\<close> _ _ _  _ this]
  with snoc.prems have "rep_of (ufa_unions l us) j \<noteq> rep_of (ufa_unions l us) k"
    by (simp split: prod.splits)
  note snoc.IH[OF snoc.prems(1) _ snoc.prems(3,4) this]
  with snoc.prems(2) rep_of_ufa_union show ?case
    by (cases "i \<le> length us") (auto split: prod.splits)
qed simp

locale ufe_invars = ufa_invars l for l +
  fixes unions :: "(nat \<times> nat) list"
  fixes au :: "int list"

  assumes valid_unions: "valid_unions (length l) unions"
  assumes eq_ufa_unions:
    "l = ufa_unions [0..<length l] unions"
  assumes valid_au:
    "\<And>i. i \<in> set au \<Longrightarrow> i \<ge> 0 \<Longrightarrow> i < length unions"
  assumes length_au:
    "length au = length l"
  assumes distinct_au:
    "distinct au"
  assumes nth_au_nonneg_if_not_rep:
    "\<And>y. y < length l \<Longrightarrow> l ! y \<noteq> y \<Longrightarrow> au ! y \<ge> 0"
  assumes rep_of_before_au:
    "\<And>i j k.
      \<lbrakk> i \<in> set au; i \<ge> 0; unions ! i = (j, k)
      ; before = ufa_unions [0..<length l] (take i unions) \<rbrakk>
      \<Longrightarrow> rep_of before j \<noteq> rep_of before k"
begin

lemma rep_of_after_au:
  assumes "i \<in> set au" "i \<ge> 0" "unions ! i = (j, k)"
  assumes "i' > i"
  assumes "after = ufa_unions [0..<length l] (take i' unions)"
  shows "rep_of after j = rep_of after k"
  using assms
proof(induction "i' - Suc i" arbitrary: i' after)
  case 0
  then have "i' = Suc i"
    by simp
  with 0 valid_au have take_i'_unions_eq:
    "take i' unions = take (i' - 1) unions @ [(j, k)]"
    by (metis diff_Suc_1 take_Suc_conv_app_nth)

  from assms valid_unions valid_au have j_k_lt_length:
    "j < length (ufa_unions [0..<length l] (take (i' - 1) unions))"
    "k < length (ufa_unions [0..<length l] (take (i' - 1) unions))"
    by force+
  from ufa_init_invar have "ufa_invar (ufa_unions [0..<length l] (take (i' - 1) unions))"
    using valid_unions by fastforce
  note Union_Find.ufa_union_aux[OF this j_k_lt_length]
  note ufa_union = this[OF j_k_lt_length(1)] this[OF j_k_lt_length(2)]
  with 0 show ?case
    unfolding take_i'_unions_eq by simp
next
  case (Suc i'')
  then have "i'' = (i' - 1) - Suc i" "i < i' - 1"
    by simp_all
  note IH = "Suc.hyps"(1)[OF this(1) Suc.prems(1,2,3) this(2) HOL.refl]
  then show ?case
  proof(cases "i' < Suc (length unions)")
    case False
    then have "take i' unions = unions"
      by simp
    moreover from False have "take (i' - 1) unions = unions"
      by simp
    ultimately show ?thesis
      using IH Suc.prems(5) by simp
  next
    case True
    with Suc have "i' - 1 < length unions" "Suc (i' - 1) = i'"
      by linarith+
    note take_Suc_conv_app_nth[OF this(1), unfolded this(2)]
    then have ufa_unions_eq: "ufa_unions [0..<length l] (take i' unions) =
      ufa_union (ufa_unions [0..<length l] (take (i' - 1) unions))
        (fst (unions ! (i' - 1))) (snd (unions ! (i' - 1)))" (is "_ = ufa_union ?l' ?a ?b")
      by (simp split: prod.split)

    have "ufa_invar ?l'"
      using ufa_init_invar ufa_invar_ufa_unions valid_unions by force
    from valid_unions have "valid_unions (length ?l') unions"
      by simp
    then have a_b_lt_length: "?a < length ?l'" "?b < length ?l'"
      using \<open>i' - 1 < length unions\<close> by blast+
    have "j < length ?l'" "k < length ?l'"
      using assms valid_au valid_unions by force+
    note rep_of_eq =
      Union_Find.ufa_union_aux[OF \<open>ufa_invar ?l'\<close> a_b_lt_length this(1)]
      Union_Find.ufa_union_aux[OF \<open>ufa_invar ?l'\<close> a_b_lt_length this(2)]

    from IH show ?thesis
      unfolding Suc.prems(5) ufa_unions_eq rep_of_eq by metis
  qed
qed

lemma rep_of_au:
  assumes "i \<in> set au" "i \<ge> 0" "unions ! i = (j, k)"
  shows "rep_of l j = rep_of l k"
proof -
  note eq_ufa_unions
  then have "l = ufa_unions [0..<length l] (take (length unions) unions)"
    by simp
  note rep_of_after_au[OF assms _  this]
  with assms valid_au show ?thesis
    by blast
qed

lemma rep_of_before_au':
  assumes "i \<in> set au" "i \<ge> 0" "unions ! i = (j, k)"
  assumes "i' \<le> i"
  assumes "before = ufa_unions [0..<length l] (take i' unions)"
  shows "rep_of before j \<noteq> rep_of before k"
  using assms
proof -
  from \<open>i' \<le> i\<close> obtain i'' where take_i''_i:
    "take i'' (take i unions) = take i' unions"
    by (metis min.orderE take_take)
  
  note rep_of_before_au[OF assms(1,2,3) HOL.refl]
  note rep_of_ufa_unions_take_neq_if_rep_of_ufa_unions_neq[OF _ _ _ _ this]
  note this[where ?i=i'', unfolded take_i''_i]
  with assms(1,2,3,5) show ?thesis
    using ufa_init_invar valid_au valid_unions
    by fastforce
qed
  

lemma ufe_invars_union:
  assumes "x < length l" "y < length l"
  assumes "rep_of l x \<noteq> rep_of l y"
  defines "l' \<equiv> ufa_union l x y"
  shows "ufe_invars l' (unions @ [(x, y)]) (au[rep_of l x := length unions])"
proof -
  from distinct_au valid_au have distinct_au_upd:
    "distinct (au[i := length unions])" for i
  proof(induction au arbitrary: i)
    case (Cons a au)
    then have "distinct (au[i := length unions])" for i
      by simp
    with "Cons.prems" show ?case
      by (cases "a \<ge> 0")
        (auto simp: comp_def elim!: in_set_upd_cases split: nat.splits)
  qed simp
  from nth_au_nonneg_if_not_rep length_au have nth_au_nonneg:
    "au[rep_of l x := length unions] ! y \<ge> 0"
    if "y < length l'" "l' ! y \<noteq> y" for y
    using that unfolding l'_def
    by (auto simp: nth_list_update')
  note axioms = ufe_invars_axioms[unfolded ufe_invars_def ufe_invars_axioms_def]
  with assms distinct_au_upd nth_au_nonneg show ?thesis
    by (unfold_locales)
      (fastforce simp: less_Suc_eq elim!: in_set_upd_cases)+
qed
    
end

locale ufe_tree = ufe_invars l unions au for l unions au +
  fixes x
  assumes lt_length[simp, intro]: "x < length l"
begin

sublocale ufa_tree l x
  using ufa_invar by unfold_locales simp_all

definition "newest_on_walk newest y p z \<equiv>
  awalk y p z \<and> newest = (MAX i \<in> set (tl (awalk_verts y p)). au ! i)"

end

end