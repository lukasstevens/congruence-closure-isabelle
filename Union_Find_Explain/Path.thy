section \<open>Path\<close>
theory Path
  imports Explain_Definition
begin 

text \<open>A path is defined from a node to a descendant, 
      the graph is represented by an array containing the parents of each node,
      as used in the union find algorithm.\<close>

inductive path :: "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  single: "n < length l \<Longrightarrow> path l n [] n"
| step: "r < length l \<Longrightarrow> l ! u = r \<Longrightarrow> l ! u \<noteq> u \<Longrightarrow> path l u p v \<Longrightarrow> path l r (r # p) v"

inductive_cases path_NilE[elim]: "path l u [] v" and path_singletonE[elim]: "path l u [k] v"

lemma path_lengthD:
  assumes "path l u p v"
  shows "u < length l" "v < length l" "\<forall>w \<in> set p. w < length l"
  using assms
  by (induction rule: path.induct) auto

lemma path_appendI: "path l u p1 v \<Longrightarrow> path l v p2 w \<Longrightarrow> path l u (p1 @ p2) w"
proof(induction rule: path.induct)
  case (single n l)
  then show ?case
    using path.cases by fastforce
qed (simp add: path.step)

lemma path_snocI: 
  assumes "path l u p (l ! v)"
      and "v < length l" "l ! v < length l" "l ! v \<noteq> v"
    shows "path l u (p @ [l ! v]) v"
  using assms
  by (intro path_appendI[where ?v="l ! v"]) (auto intro: path.intros)

lemma path_butlastI:
  assumes "path l u p v" "p \<noteq> []"
  shows "path l u (butlast p) (l ! v)"
  using assms
  by (induction rule: path.induct) (auto intro: path.intros)

lemma path_appendD:
  assumes "path l u (p1 @ p2) v"
  shows "path l u p1 (hd (p2 @ [v]))" "path l (hd (p2 @ [v])) p2 v"
proof -
  from assms have "path l u p1 (hd (p2 @ [v])) \<and> path l (hd (p2 @ [v])) p2 v"
  proof(induction l u "p1 @ p2" v arbitrary: p1 p2 rule: path.induct)
    case (step r l u p v)
    then show ?case
      unfolding Cons_eq_append_conv by (auto simp: path.intros)
  qed (simp add: path.single)
  then show "path l u p1 (hd (p2 @ [v]))" "path l (hd (p2 @ [v])) p2 v"
    by blast+
qed

lemma eq_snoc_butlastI_if_path:
  assumes "path l u p v" "p \<noteq> []"
  shows "p = butlast p @ [l ! v]"
proof -
  from assms have "last p = l ! v"
    by (induction rule: path.induct) auto
  with assms have "path l u (butlast p @ [l ! v]) v"
    by (metis snoc_eq_iff_butlast')
  from assms \<open>last p = l ! v\<close> path_appendD[OF this] show ?thesis
    by (simp add: snoc_eq_iff_butlast')
qed

lemma hd_if_path: "path l u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> hd p = u"
  by (induction rule: path.induct) auto

lemma path_unique_if_length_eq:
  assumes "path l x p1 v"
      and "path l y p2 v"
      and "ufa_invar l"
      and "length p1 = length p2"
    shows "p1 = p2 \<and> x = y"
  using assms
proof(induction arbitrary: p2 y rule: path.induct)
  case (single n l)
  then show ?case
    by auto
next
  case (step r l u p v)
  from step.prems obtain p2' where p2: "p2 = [y] @ p2'"
    by (auto elim: path.cases)
  note path_append = path_appendD[OF step.prems(1)[unfolded this]]
  from this(2)[THEN step.IH] p2 have "p = p2' \<and> u = hd (p2' @ [v])"
    using \<open>ufa_invar l\<close> \<open>length (r # p) = length p2\<close> by simp
  with path_append(1) p2 step.hyps(2) show ?case
    by auto
qed

lemma path_parent:
  assumes "path l x p y" "i < length p" "i > 0"
  shows "l ! (p ! i) = (p ! (i - 1))"
  using assms 
proof(induction arbitrary: i rule: path.induct)
  case (step r l u p v)
  then show ?case
    by (cases "i = 1") (auto elim: path.cases)
qed simp

lemma path_no_cycle: 
  assumes "ufa_invar l"
      and "n < length l"
      and "path l n p n"
    shows "p = []" 
proof(rule ccontr)
  assume "p \<noteq> []"
  with assms have "\<not> rep_of_dom (l, n)"
  proof(induction arbitrary: p rule: rep_of_induct)
    case (base i)
    from base(4,3) have "p = []"
      by (induction rule: path.induct) auto
    with \<open>p \<noteq> []\<close> show ?case
      by blast
  next
    case (step i)
    with path_butlastI[OF step.prems(1,2)]
    have "path l (l ! i) (l ! i # butlast p) (l ! i)"
      using path.step path_lengthD(2) by blast
    from step.IH[OF this] show ?case
      using assms ufa_invarD(2) by (metis neq_Nil_conv rep_of_domain)
  qed
  with assms show "False"
    using ufa_invarD(1) by blast
qed

lemma path_rootD:
  assumes "path l u p v"
      and "l ! v = v"
      and "ufa_invar l"
    shows "p = []" "u = v"
  using assms
  by (induction rule: path.induct) auto

text \<open>The path between two nodes is unique.\<close>

theorem path_unique:
  assumes "path l u p1 v" "path l u p2 v"
  assumes "ufa_invar l"
  shows "p1 = p2"
  using assms
proof -
  from assms have "v < length l"
    using path_lengthD by blast
  from assms(3) this assms(1,2) show "p1 = p2"
  proof(induction arbitrary: p1 p2 rule: rep_of_induct)
    case (base i)
    then show ?case
      using path_rootD(1) by blast
  next
    case (step i)
    then show ?case
    proof (cases "p1 = []"; cases "p2 = []")
      assume "p1 \<noteq> []" "p2 \<noteq> []"
      with step have "butlast p1 = butlast p2"
        by (intro step.IH) (auto elim: path_butlastI)
      with \<open>p1 \<noteq> []\<close> \<open>p2 \<noteq> []\<close> step show ?thesis
        using eq_snoc_butlastI_if_path path_unique_if_length_eq
        by metis
    qed (use step in \<open>auto dest: path_no_cycle\<close>)
  qed
qed

lemma rep_of_eq_if_path:
  "path l v p u \<Longrightarrow> ufa_invar l \<Longrightarrow> rep_of l v = rep_of l u"
proof(induction rule: path.induct)
  case (single n l)
  then show ?case by auto
next
  case (step r l u p v)
  then have "rep_of l u = rep_of l r"
    using path_lengthD rep_of_idx by auto
  with step show ?case 
    by simp
qed

lemma path_rep_of: 
  assumes "ufa_invar l"
      and "x < length l"
  obtains p where "path l (rep_of l x) p x"
  using assms proof(induction arbitrary: thesis rule: rep_of_induct)
  case (base i)
  then show ?case 
    using base single rep_of_refl by auto
next
  case (step i)
  from step(4) obtain p where "path l (rep_of l (l ! i)) p (l ! i)"
    by blast
  with step have "path l (rep_of l i) p (l ! i)"
    using rep_of_idx path_lengthD(2) by simp
  from path_snocI[OF this] step have "path l (rep_of l i) (p @ [l ! i]) i"
    using path_snocI by (metis ufa_invar_def)
  with step.prems show ?case
    by blast
qed

lemma path_root: "path l x p r \<Longrightarrow> l ! r = r \<Longrightarrow> x = r"
  by (induction rule: path.induct) auto

lemma path_not_root: "path l y p x \<Longrightarrow> x \<noteq> y \<Longrightarrow> l ! x \<noteq> x"
  using path_root by auto

lemma path_not_hd_not_root:
  assumes "path l x p y"
    and "i < length p"
    and "i > 0"
  shows "l ! (p ! i) \<noteq> p ! i"
  using assms
proof(induction arbitrary: i rule: path.induct)
  case (single n l)
  then show ?case by auto
next
  case (step r l u p v)
  have "(r # p) ! i = p ! (i - 1)" 
    by (simp add: step.prems(2))
  with step show ?case
    by (cases "i = 1") (auto elim: path.cases)
qed

lemma path_rep_ofD:
  assumes "path l x p y"
      and "i < length p"
      and "ufa_invar l"
    shows "rep_of l (p ! i) = rep_of l x"
      and "rep_of l (p ! i) = rep_of l y"
proof -
  from assms have "path l x (take i p @ drop i p) y"
    by auto
  note path_appendD[OF this]
  with assms show "rep_of l (p ! i) = rep_of l x" "rep_of l (p ! i) = rep_of l y"
    by (auto simp: hd_drop_conv_nth dest!: rep_of_eq_if_path)
qed

lemma path_root_rep_of_dom:
  "path l root p i \<Longrightarrow> l ! root = root \<Longrightarrow> rep_of_dom (l, i)"
proof(induction p arbitrary: i rule: rev_induct)
  case Nil
  then show ?case
    using rep_of.domintros by auto
next
  case (snoc x xs)
  then have "x = l ! i"
    using eq_snoc_butlastI_if_path by blast
  with snoc path_appendD[OF \<open>path l root (xs @ [x]) i\<close>] show ?case
    by (cases xs) (use rep_of.domintros in auto)
qed

lemma path_fun_upd_otherI:
  assumes "path l x p y" "i \<notin> insert y (set (tl p))"
  shows "path (l[i := k]) x p y"
  using assms
proof(induction rule: path.induct)
  case (single n l)
  then show ?case 
    by (simp add: path.single)
next
  case (step r l u p v)
  then have "path (l[i := k]) u p v"
    using in_set_tlD by fastforce
  with step show ?case
    by (intro path.step) (auto elim: path.cases)
qed

text \<open>The paths of nodes with a different root are disjoint.\<close>

lemma path_neq_rep_of_not_in_path: 
  assumes "path l y\<^sub>2 p\<^sub>2 x\<^sub>2"
      and "i\<^sub>2 < length p\<^sub>2"
      and "rep_of l n \<noteq> rep_of l x\<^sub>2"
      and "ufa_invar l"
  shows "n \<noteq> p\<^sub>2 ! i\<^sub>2"
proof
  assume n_in_path: "n = p\<^sub>2 ! i\<^sub>2"
  with assms have "rep_of l (p\<^sub>2 ! i\<^sub>2) = rep_of l x\<^sub>2" 
    using path_rep_ofD(2) by blast
  with n_in_path have "rep_of l x\<^sub>2 = rep_of l n" 
    by simp
  with assms show "False" 
    by argo
qed

lemma path_neq_rep_of_disjoint: 
  assumes "path l y\<^sub>1 p\<^sub>1 x\<^sub>1" "path l y\<^sub>2 p\<^sub>2 x\<^sub>2"
      and "i\<^sub>1 < length p\<^sub>1" "i\<^sub>2 < length p\<^sub>2"
      and "rep_of l x\<^sub>1 \<noteq> rep_of l x\<^sub>2"
      and "ufa_invar l"
  shows "p\<^sub>1 ! i\<^sub>1 \<noteq> p\<^sub>2 ! i\<^sub>2"
  using assms
proof(induction l y\<^sub>1 p\<^sub>1 x\<^sub>1 arbitrary: i\<^sub>1 rule: path.induct)
  case (single n l)
  then show ?case 
    using path_neq_rep_of_not_in_path by auto
next
  case (step r l u p v)
  then show ?case
  proof(cases "i\<^sub>1")
    case 0
    then have "(r # p) ! i\<^sub>1 = r" 
      by simp
    with step show ?thesis 
      by (metis path_lengthD(1) path_rep_ofD(2) rep_of_eq_if_path rep_of_idx)
  qed auto
qed

lemma path_remove_left: 
  assumes "path l i (i # pia) ia"
      and "ufa_invar l"
    shows "i \<notin> set pia"
proof
  assume "i \<in> set pia"
  then obtain p\<^sub>1 p\<^sub>2 where "pia = p\<^sub>1 @ [i] @ p\<^sub>2" 
    by (metis Cons_eq_append_conv append_Nil in_set_conv_decomp_first)
  with assms have "path l i ([i] @ p\<^sub>1 @ [i]) i" 
    by (metis Cons_eq_appendI append_is_Nil_conv empty_append_eq_id list.sel(1) path_divide2 snoc_eq_iff_butlast)
  with path_unique assms show "False" 
    by (metis append_self_conv last_ConsL path_divide1 snoc_eq_iff_butlast)
qed

lemma path_remove_right: 
  assumes "path l ia pia i"
    "ufa_invar l"
  shows "i \<notin> set (butlast pia)"
proof
  have pia: "pia = (butlast pia) @ [i]" 
    by (metis assms(1) path_last path_not_empty snoc_eq_iff_butlast)
  assume "i \<in> set (butlast pia)"
  then obtain p\<^sub>1 p\<^sub>2 where "butlast pia = p\<^sub>1 @ [i] @ p\<^sub>2" 
    by (metis Cons_eq_append_conv append_Nil in_set_conv_decomp_first)
  with assms have "path l i ([i] @ p\<^sub>2 @ [i]) i" 
    using pia path_divide2 by fastforce
  with path_unique assms show "False" 
    by (metis append_self_conv last_ConsL path_divide1 snoc_eq_iff_butlast)
qed

lemma path_remove_child: 
  assumes "path l ia pia (l ! i)"
    "ufa_invar l" "i < length l" "l ! i \<noteq> i"
  shows "i \<notin> set pia"
proof-
  from assms have "path l (l ! i) [l ! i, i] i" 
    by (metis path.step single ufa_invarD(2))
  have pia: "path l ia (pia @ [i]) i" 
    by (simp add: assms path_snoc ufa_invarD(2))
  with path_remove_right show ?thesis 
    by (metis assms(2) butlast_snoc)
qed

lemma path_previous_node: 
  assumes "path l y p x" "i < length p - 1" "p ! (i + 1) = n"
  shows "p ! i = l ! n"
  using assms proof(induction arbitrary: i rule: path.induct)
  case (single n l)
  then show ?case by auto 
next
  case (step r l u p v)
  then show ?case proof(cases i)
    case 0
    have "p \<noteq> []" 
      using path_not_empty step.hyps(4) by blast
    with step 0 have "hd p = n" 
      by (simp add: hd_conv_nth)
    with step have "u = n" 
      using hd_path by blast
    with step show ?thesis 
      by (metis "0" nth_Cons_0)
  next
    case (Suc nat)
    with step show ?thesis by auto
  qed
qed

lemma path_hd_and_last:
  assumes "path l y p x" "length p > 1"
  shows "p = y # (tl (butlast p)) @ [x]"
proof-
  have "p = butlast p @ [x]" 
    by (metis append_butlast_last_id assms(1) path_last path_not_empty)
  have "length (butlast p) > 0" 
    using add.right_neutral assms(2) by auto
  then have "butlast p @ [x] = y # (tl (butlast p) @ [x])" 
    by (metis Cons_eq_appendI assms(1) assms(2) hd_Cons_tl hd_butlast hd_path length_greater_0_conv) 
  then show ?thesis 
    using \<open>p = butlast p @ [x]\<close> by auto
qed

lemma path_longer:
  assumes "ufa_invar l" "path l b p1 a" "path l c p2 a" "length p1 > length p2"
  shows "path l b (take (length p1 - length p2 + 1) p1) c"
    (is "path l b ?p3 c")
proof-
  let ?p4 = "(drop (length p1 - length p2 + 1) p1)"
  have "path l b (?p3 @ ?p4) a" 
    by (simp add: assms(2))
  moreover have "?p3 \<noteq> []" 
    by (metis Suc_eq_plus1_left Zero_not_Suc ab_semigroup_add_class.add.commute assms(4) len_greater_imp_nonempty take_eq_Nil)
  ultimately have path_split: "path l b ?p3 (last ?p3)"  "path l (last ?p3) (last ?p3 # ?p4) a"
    using path_divide1 by blast+
  have "length (last ?p3 # ?p4) = length p2" 
    by (metis (no_types, lifting) One_nat_def ab_semigroup_add_class.add.commute add_diff_cancel_right add_diff_inverse_nat assms(3) assms(4) length_drop length_greater_0_conv less_Suc_eq list.discI list.size(4) not_less_eq path.simps)
  then have "(last ?p3) = c" 
    using path_unique_if_length_eq assms path_split by blast
  then show ?thesis 
    using path_split(1) by blast
qed

lemma complement_of_subpath:
  assumes "ufa_invar l" "path l b p1 a" "path l c p2 a" "b \<notin> set p2"
  shows "path l b (take (length p1 - length p2 + 1) p1) c"
    (is "path l b ?p3 c")
proof-
  let ?p4 = "(drop (length p1 - length p2 + 1) p1)"
  have "length p1 > length p2" 
  proof(rule ccontr)
    assume p2_longer: "\<not> length p2 < length p1"
    then have "b \<in> set p2" proof(cases "length p2 = length p1")
      case True
      then have "b = c" 
        using assms(1) assms(2) assms(3) path_unique_if_length_eq by auto
      then show ?thesis 
        by (metis assms(3) in_set_member member_rec(1) path.cases)
    next
      case False
      then have "length p1 < length p2" 
        using p2_longer by linarith
      then obtain p5 where "path l c p5 b" 
        using path_longer assms by blast
      then have "path l c (p5 @ tl p1) a" 
        using assms(2) paths_iff by blast
      then show ?thesis 
        by (metis (no_types, lifting) \<open>path l c p5 b\<close> assms(1) assms(2) assms(3) in_set_conv_decomp path.simps path_concat2 path_unique)
    qed
    then show "False" using assms(4) 
      by blast
  qed
  then show ?thesis 
    using assms(1) assms(2) assms(3) path_longer by blast
qed

lemma path_take_two:
  assumes "ufa_invar l" "i < length p" "i \<noteq> 0" "path l a p b"
  shows "path l (l ! (p ! i)) [l ! (p ! i), (p ! i)] (p ! i)"
proof
  show "l ! (p ! i) < length l" using assms 
    by (simp add: nodes_path_lt_length_l ufa_invarD(2))
  show "l ! (p ! i) = l ! (p ! i)" ..
  show "l ! (p ! i) \<noteq> (p ! i)"
    by (metis assms(2) assms(3) assms(4) bot_nat_0.not_eq_extremum path_not_first_no_root)
  show "path l (p ! i) [p ! i] (p ! i)" 
    using assms nodes_path_lt_length_l single by blast
qed

lemma path_contains_no_root:
  assumes "x \<in> set (tl p)" "ufa_invar l"
    "path l a p b"
  shows "l ! x \<noteq> x"
proof-
  from assms obtain i where "i < length (tl p)" "tl p ! i = x" 
    by (meson in_set_conv_nth)
  with path_not_first_no_root assms show ?thesis 
    by (metis List.nth_tl Suc_mono gr0_conv_Suc in_set_tlD length_Suc_conv length_pos_if_in_set list.sel(3))
qed

end
