section \<open>Correctness proofs for the helper functions\<close>
theory Helper_Functions
  imports Path 
begin 

subsection \<open>Proofs about the domain of the helper functions\<close>

theorem (in ufa_tree) lca_ufa_lca:    
  assumes "y \<in> verts (ufa_tree_of l x)"
    shows "lca (ufa_lca l x y) x y"
proof -
  from assms have "rep_of l x = rep_of l y"
    using in_verts_ufa_tree_ofD(2) by simp
  note awalk_awalk_from_rep[OF x_in_verts]
   and awalk_awalk_from_rep[OF assms, folded this]
  note lca_last_longest_common_prefix_awalk_verts[OF this]
  with \<open>rep_of l x = rep_of l y\<close> show ?thesis
    unfolding ufa_lca_def
    unfolding awalk_verts_from_rep_eq_awalk_verts[OF x_in_verts]
    unfolding awalk_verts_from_rep_eq_awalk_verts[OF assms]
    by simp
qed

subsection \<open>Correctness of \<open>find_newest_on_walk\<close>.\<close>

lemma find_newest_on_walk_dom_idx:
  assumes "find_newest_on_walk_dom l (y, x)" "x \<noteq> y"
  shows "find_newest_on_walk_dom l (y, l ! x)"
  using assms find_newest_on_walk.domintros
  by (induction rule: find_newest_on_walk.pinduct) blast

lemma (in ufa_tree) find_newest_on_walk_domain:
  assumes "awalk y p z"
  shows "find_newest_on_walk_dom l (y, z)"
proof -
  from assms have "z \<in> verts (ufa_tree_of l x)"
    by blast
  from in_verts_ufa_tree_ofD(1)[OF this(1)] assms show ?thesis
  proof(induction arbitrary: p rule: rep_of_induct)
    case (base i)
    then show ?case
      using find_newest_on_walk.domintros awalk_idx_sameD by blast
  next
    case (step i)
    then show ?case
    proof(cases "i = y")
      case True
      then show ?thesis 
        using find_newest_on_walk.domintros by blast
    next
      case False
      with step have "p \<noteq> []"
        using awalk_ends by blast
      note awalk_not_Nil_butlastD[OF _ this]
       and awlast_butlast_eq_idx_if_awalk[OF _ this]
      with step have "awalk y (butlast p) (l ! i)"
        by metis+
      with step have "find_newest_on_walk_dom l (y, l ! i)"
        by blast
      then show ?thesis
        using find_newest_on_walk.domintros by blast
    qed
  qed
qed

theorem (in ufe_tree) find_newest_on_walk_correct:
  assumes "awalk y p z"
      and "y \<noteq> z"
    shows "newest_on_walk (find_newest_on_walk l au y z) y p z"
proof -
  from assms have "l ! z \<noteq> z"
    using awalk_idx_sameD(1) by blast
  note find_newest_on_walk_domain[OF assms(1)]
  then show ?thesis 
    using assms
  proof(induction arbitrary: p rule: find_newest_on_walk.pinduct)
    case (1 y z)
    with nth_au_nonneg_if_not_rep have "au ! z \<ge> 0"
      by (metis awalk_idx_sameD(1) awalk_last_in_verts in_verts_ufa_tree_ofD(1))
    then show ?case
    proof(cases "y = l ! z")
      case True
      with 1 have "p = [(l ! z, z)]"
        by (metis awalkE' awalk_idx unique_awalk_All)
      with 1 \<open>au ! z \<ge> 0\<close> show ?thesis
        unfolding newest_on_walk_def
        using find_newest_on_walk.psimps[where ?x=z]
        using find_newest_on_walk.psimps[where ?x="l ! z"]
        by (auto simp: find_newest_on_walk_dom_idx)
    next
      case False
      with 1 have "p \<noteq> []"
        by auto
      with 1 have
        awalk_butlast: "awalk y (butlast p) (l ! z)" and
        awalk_last: "awalk (l ! z) [last p] z"
        using awalk_not_Nil_butlastD awlast_butlast_eq_idx_if_awalk
        by auto
      with awalk_verts_append[where ?p="butlast p" and ?q="[last p]"]
      have awalk_verts_p:
        "awalk_verts y p = awalk_verts y (butlast p) @ [z]"
        using \<open>awalk y p z\<close> \<open>p \<noteq> []\<close> by auto
      moreover
      note "1.IH"[OF \<open>y \<noteq> z\<close> \<open>awalk y (butlast p) (l ! z)\<close> \<open>y \<noteq> l ! z\<close>]
      moreover from \<open>p \<noteq> []\<close> have "p = butlast p @ [last p]"
        by simp
      moreover
      have "Max (insert (au ! z) ((!) au ` set (tl (awalk_verts y (butlast p)))))
        = max (au ! z) (Max ((!) au ` set (tl (awalk_verts y (butlast p)))))"
      proof(rule Max.insert_not_elem)
        from False awalk_butlast
        show "(!) au ` set (tl (awalk_verts y (butlast p))) \<noteq> {}"
          by (cases p) auto

        from \<open>awalk y p z\<close> awalk_butlast awalk_verts_p
        have "z \<notin> set (awalk_verts y (butlast p))"
          by (metis distinct_awalk_verts not_distinct_conv_prefix)
        then have "z \<notin> set (tl (awalk_verts y (butlast p)))"
          by (meson in_set_tlD)
        moreover from \<open>awalk y p z\<close> have "z < length au"
          using length_au
          by (metis awalk_last_in_verts in_verts_ufa_tree_ofD(1))
        moreover from awalk_butlast have
          "\<forall>x \<in> set (tl (awalk_verts y (butlast p))). x < length au"
          using length_au
          by (metis awalkE' awalk_verts_in_verts in_set_tlD in_verts_ufa_tree_ofD(1))
        ultimately show "au ! z \<notin> (!) au ` set (tl (awalk_verts y (butlast p)))"
          using distinct_au[unfolded distinct_conv_nth]
          by auto
      qed simp

      ultimately show ?thesis
        using "1.prems" "1.hyps"
        unfolding newest_on_walk_def
        using find_newest_on_walk.psimps[where ?x=z]
        by auto
    qed
  qed
qed

(*
subsection \<open>Invariant for the Union Find Data Structure\<close>

text \<open>This section introduces an invariant for the union find data structure and proves
several properties of the functions when invoked with valid parameters.\<close>

abbreviation "valid_unions u n \<equiv>
(\<forall> i < length u. fst (u ! i) < n \<and> snd (u ! i) < n)"

text \<open>The validity invariant of the data structure expresses that the data structure derived 
from subsequent union with \<open>ufe_union\<close>, starting from the initial empty data structure. 
It also says that the unions were made with valid variables, aka the numbers are less than 
the length of the union find list.\<close>

abbreviation "ufe_valid_invar ufe \<equiv> 
  valid_unions (unions ufe) (length (uf_list ufe)) \<and>
  apply_unions (unions ufe) (initial_ufe (length (uf_list ufe))) = ufe"

paragraph \<open>Lemmata about the length of \<open>uf_list\<close>, au and unions, if the invariant holds.\<close>

lemma ufe_union_length_au:
  "ufe_union ufe1 x y = ufe2 \<Longrightarrow> length (au ufe1) = length (au ufe2)"
  by(induction ufe1 x y rule: ufe_union.induct,auto)

lemma ufe_union_length_uf_list:
  "ufe_union ufe1 x y = ufe2 \<Longrightarrow> length (uf_list ufe1) = length (uf_list ufe2)"
  by(induction ufe1 x y rule: ufe_union.induct,auto)

lemma ufe_union_length_unions_Suc:
  "ufe_union ufe1 x y = ufe2 \<Longrightarrow> rep_of (uf_list ufe1) x \<noteq> rep_of (uf_list ufe1) y \<Longrightarrow> length (unions ufe1) + 1 = length (unions ufe2)"
  by(induction ufe1 x y rule: ufe_union.induct,auto)

lemma apply_unions_length_au:
  "apply_unions u ufe1 = ufe2 \<Longrightarrow> length (au ufe1) = length (au ufe2)"
  apply(induction u ufe1 rule: apply_unions.induct)
   apply simp_all
  apply (metis ufe_union_length_au)
  done

lemma apply_unions_length_uf_list:
  "apply_unions u ufe1 = ufe2 \<Longrightarrow> length (uf_list ufe1) = length (uf_list ufe2)"
  apply(induction u ufe1 rule: apply_unions.induct)
   apply simp_all
  apply (metis ufe_union_length_uf_list)
  done

lemma length_au:
  "ufe_valid_invar ufe \<Longrightarrow> length (au ufe) = length (uf_list ufe)"
  by (metis apply_unions_length_au length_replicate ufe_data_structure.select_convs(3))

lemma ufe_union_length_unions_le:
  assumes "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
  shows  "length u \<le> length (unions (ufe_union ufe x y))"
  apply(cases "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y")
   apply(simp_all add: assms)
  done

lemma apply_unions_length_unions:
  "ufe = apply_unions un ufe0 \<Longrightarrow> length (unions ufe) \<le> length (unions ufe0) + length un"
proof(induction "length un" arbitrary: un ufe)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain xy un' where un':"un = un' @ [xy]"
    by (metis length_Suc_rev_conv)
  let ?ufe = "apply_unions un' ufe0"
  have IH: "length (unions ?ufe) \<le> length (unions ufe0) + length un'"
    using Suc un' by auto
  have *:"apply_unions un ufe0 = apply_unions [xy] ?ufe" 
    by (simp add: un' apply_unions_append)
  obtain x2 y2 where xy:"xy = (x2,y2)"
    using prod_decode_aux.cases by blast
  then show ?case 
  proof(cases "rep_of (uf_list ?ufe) x2 = rep_of (uf_list ?ufe) y2")
    case True
    then have "ufe_union ?ufe x2 y2 = ?ufe" 
      by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
    then show ?thesis 
      using Suc.prems IH un' xy apply_unions_append by auto
  next
    case False
    obtain l1 u1 a1 where ufe: "?ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    with False have "rep_of l1 x2 \<noteq> rep_of l1 y2" by auto
    then have "unions (ufe_union ?ufe x2 y2) = u1 @ [(x2,y2)]"
      using ufe by auto 
    with un' xy * show ?thesis 
      by (metis IH Suc.prems add_Suc_right apply_unions.simps(1,2) length_append_singleton not_less_eq_eq ufe ufe_data_structure.select_convs(2))
  qed
qed

lemma length_uf_list_initial: "initial_ufe n = ufe \<Longrightarrow> length (uf_list ufe) = n"
  by auto

paragraph \<open>Lemmata about the preservation of the invariant\<close>

lemma union_ufe_valid_invar:
  assumes "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "ufe_valid_invar ufe"
    and "x < length l"
    and "y < length l"
  shows "ufe_valid_invar (ufe_union ufe x y)"
proof(cases "rep_of l x = rep_of l y")
  case True
  with assms ufe_union1 show ?thesis 
    by simp
next
  case False
  with assms ufe_union2 have unions: "unions (ufe_union ufe x y) = unions ufe @ [(x,y)]"
    by (metis ufe_data_structure.cases ufe_data_structure.select_convs(1,2))
  then have **: "i < length (unions (ufe_union ufe x y)) \<Longrightarrow>
       fst (unions (ufe_union ufe x y) ! i) < length (uf_list (ufe_union ufe x y)) \<and>
       snd (unions (ufe_union ufe x y) ! i) < length (uf_list (ufe_union ufe x y))" for i
  proof(cases "i < length (unions ufe)")
    case True
    then show ?thesis 
      using assms(2) ufe_union_length_uf_list unions by force
  next
    case False
    assume assm: "i < length (unions (ufe_union ufe x y))"
    with assms(1) unions have "length u + 1  = length (unions (ufe_union ufe x y))"
      by auto
    then have "i = length u" 
      using False assm assms(1) by (simp add: discrete)
    then have "fst (unions (ufe_union ufe x y) ! i) = x" 
      and "snd (unions (ufe_union ufe x y) ! i) = y"
      using assms(1) unions by auto
    with assms show ?thesis 
      by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  qed
  then have "apply_unions (u @ [(x,y)]) (initial_ufe (length l)) = apply_unions [(x, y)] ufe" 
    using apply_unions_append assms by fastforce
  then have "apply_unions (unions (ufe_union ufe x y)) 
(initial_ufe (length (uf_list (ufe_union ufe x y)))) = ufe_union ufe x y" 
    by (metis apply_unions.simps(1,2) assms(1) ufe_data_structure.select_convs(1,2) ufe_union_length_uf_list unions)
  with ** show ?thesis 
    by simp
qed

lemma union_ufe_valid_invar':
  assumes "ufe_valid_invar ufe"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
  shows "ufe_valid_invar (ufe_union ufe x y)"
proof-
  obtain l a u where "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    using ufe_data_structure.cases by blast
  with assms union_ufe_valid_invar show ?thesis 
    by auto
qed

theorem apply_unions_ufe_valid_invar:
  assumes "ufe_valid_invar ufe"
    and "valid_unions u (length (uf_list ufe))"
  shows "ufe_valid_invar (apply_unions u ufe)"
  using assms proof(induction "length u" arbitrary: u)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain xy un' where un': "u = un' @ [xy]"
    by (metis length_Suc_rev_conv)
  then obtain x2 y2 where xy: "xy = (x2, y2)"
    using old.prod.exhaust by blast
  have valid_unions: "valid_unions un' (length (uf_list ufe))" 
    by (metis Suc.prems(2) Suc_lessD Suc_mono un' length_append_singleton nth_append_first)
  let ?c = "apply_unions un' ufe"
  have c: "ufe_valid_invar ?c" 
    using Suc un' valid_unions assms(1) by auto
  have "apply_unions u ufe = apply_unions [xy] ?c" 
    by (simp add: un' apply_unions_append)
  then have *: "apply_unions u ufe = ufe_union ?c x2 y2" 
    by (simp add: \<open>xy = (x2, y2)\<close>)
  obtain l1 u1 a1 where ufe: "?c = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  have "x2 < length (uf_list ?c) \<and> y2 < length (uf_list ?c)"
    by (metis Suc.prems(2) un' xy apply_unions_length_uf_list fst_conv length_append_singleton lessI nth_append_length snd_conv)
  with * c union_ufe_valid_invar ufe show ?case 
    by simp
qed

paragraph \<open>\<open>ufe_valid_invar\<close> implies \<open>ufa_invar\<close>.\<close>

lemma ufe_valid_invar_imp_ufa_invar_aux: 
  "ufa_invar (uf_list ufe) \<Longrightarrow> valid_unions u (length (uf_list ufe)) \<Longrightarrow> ufa_invar (uf_list (apply_unions u ufe))"
proof(induction u ufe rule: apply_unions.induct)
  case (1 p)
  then show ?case by auto
next
  case (2 x y u p)
  from 2(3) have x: "x < length (uf_list p)" and y: "y < length (uf_list p)" by force+
  with 2(2) ufa_union_invar ufe_union2_uf_list have *: "rep_of (uf_list p) x \<noteq> rep_of (uf_list p) y 
\<Longrightarrow> ufa_invar (uf_list (ufe_union p x y))"
    by presburger
  from x y 2(2) ufe_union1_uf_list have "rep_of (uf_list p) x = rep_of (uf_list p) y 
\<Longrightarrow> ufa_invar (uf_list (ufe_union p x y))"
    by presburger
  with * 2 ufe_union_length_uf_list have "ufa_invar (uf_list (apply_unions u (ufe_union p x y)))"
    by (metis Suc_less_eq2 length_Cons nth_Cons_Suc)
  then show ?case 
    by simp
qed

lemma ufe_valid_invar_initial: "ufe_valid_invar (initial_ufe n)"
  by simp

theorem ufe_valid_invar_imp_ufa_invar: "ufe_valid_invar ufe \<Longrightarrow> ufa_invar (uf_list ufe)"
  by (metis apply_unions_length_uf_list ufa_init_invar ufe_data_structure.select_convs(1) ufe_valid_invar_imp_ufa_invar_aux)

paragraph \<open>Induction rule on the union find algorithm.\<close>
lemma apply_unions_induct[consumes 1, case_names initial union]:
  assumes "ufe_valid_invar ufe"
  assumes "P (initial_ufe (length (uf_list ufe)))"
  assumes "\<And>pufe x y. ufe_valid_invar pufe \<Longrightarrow> x < length (uf_list pufe) \<Longrightarrow> y < length (uf_list pufe)
    \<Longrightarrow> P pufe \<Longrightarrow> P (ufe_union pufe x y)"
  shows "P ufe"
  using assms proof(induction "length (unions ufe)" arbitrary: ufe)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain x2 y2 un where u: "unions ufe =  un @ [(x2,y2)]" 
    by (metis length_0_conv neq_Nil_rev_conv replicate_0 replicate_Suc_conv_snoc surjective_pairing)
  with Suc(3) have un_valid: "valid_unions un (length (uf_list ufe))" 
    by (metis length_append_singleton nat_less_le neq_Nil_rev_conv nth_append_first upt_Suc upt_rec)
  obtain pufe where pufe: "pufe = apply_unions un (initial_ufe (length (uf_list ufe)))"
    by simp
  then have pufe2: "ufe_union pufe x2 y2 = ufe" 
    by (metis Suc.prems(1) apply_unions.simps(1,2) apply_unions_append u)
  then show ?case
  proof(cases "rep_of (uf_list pufe) x2 = rep_of (uf_list pufe) y2")
    case True
    obtain l1 u1 a1 where ufe: "ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    obtain l2 u2 a2 where pufe3: "pufe = \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>" 
      using ufe_data_structure.cases by blast
    with True have "rep_of l2 x2 = rep_of l2 y2" by auto
    with True pufe2 ufe pufe3 have "pufe = ufe_union pufe x2 y2"  
      by simp
    then have "pufe = ufe" 
      by (simp add: pufe2)
    then have ufe2: "u2 = u1" using ufe pufe2 pufe
      by (metis pufe3 ufe_data_structure.ext_inject)
    with pufe apply_unions_length_unions have "length (unions pufe) \<le> length un"
      by (metis ab_semigroup_add_class.add.commute gen_length_code(1) gen_length_def ufe_data_structure.select_convs(2))
    moreover from u ufe2 have "length (unions ufe) = length un + 1"
      by simp
    ultimately have "False" 
      using \<open>pufe = ufe\<close> by auto
    then show ?thesis by simp
  next
    case False
    with Suc(2) u ufe_union_length_uf_list have "x = length (unions pufe)" 
      by (metis Suc_eq_plus1 add_right_cancel pufe2 ufe_union_length_unions_Suc)
    have length_eq: "length (uf_list pufe) = length (uf_list ufe)" 
      using pufe2 ufe_union_length_uf_list by auto
    then have "ufe_valid_invar pufe" 
      using apply_unions_ufe_valid_invar length_uf_list_initial pufe ufe_valid_invar_initial un_valid by presburger
    with Suc have "P pufe" 
      using \<open>x = length (unions pufe)\<close> length_eq by fastforce
    from Suc(3) u have "x2 < length (uf_list pufe)" "y2 < length (uf_list pufe)"
       apply (metis length_eq fst_conv length_Suc_rev_conv lessI nth_append_length)
      by (metis Suc(3) u length_eq snd_conv length_Suc_rev_conv lessI nth_append_length)
    with Suc show ?thesis 
      using \<open>P pufe\<close> \<open>ufe_valid_invar pufe\<close> pufe2 by blast
  qed
qed

paragraph \<open>Properties of some functions when \<open>ufe_valid_invar\<close> holds.\<close>

lemma no_redundant_unions:
  assumes invar: "ufe_valid_invar a"
    and unions_a: "unions a = p @ [(x, y)] @ t"
    and l: "l = apply_unions p (initial_ufe (length (uf_list a)))"
  shows "rep_of (uf_list l) x \<noteq> rep_of (uf_list l) y"
proof
  assume same_rep: "rep_of (uf_list l) x = rep_of (uf_list l) y"
  obtain l1 u1 a1 where "l = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with same_rep have "ufe_union l x y = l"
    by auto
  then have 1: "apply_unions (p @ [(x,y)]) (initial_ufe (length (uf_list a))) = l" 
    by (metis l apply_unions.simps apply_unions_append)
  then have "apply_unions (p @ [(x,y)] @ t) (initial_ufe (length (uf_list a))) = a" 
    using invar unions_a by auto
  then have "length (unions a) \<le> length (p  @ t)"
    by (metis 1 l add_cancel_left_left apply_unions_append length_append apply_unions_length_unions list.size(3) ufe_data_structure.select_convs(2))
  then show "False"
    by (simp add: unions_a)
qed

text \<open>(au ! i = None) iff i is a root.\<close>

lemma au_none_iff_root_initial: 
  assumes initial: "\<lparr>uf_list = l, unions = u, au = a\<rparr> = initial_ufe (length l)" 
    and i: "i < length l"
  shows "a ! i = None \<longleftrightarrow> l ! i = i"
proof-
  from initial have "l = [0..<length l]"
    by blast
  with i have *: "l ! i = i" 
    by (metis add_cancel_left_left nth_upt)
  from initial have "length a = length l" 
    by force
  with i initial have "a ! i = None" 
    by simp
  with i * show ?thesis
    by simp
qed

lemma au_none_iff_root_union:
  assumes "a ! i = None \<longleftrightarrow> l ! i = i"
    and "i < length l"
    and "x < length l"
    and "y < length l"
    and "ufe_valid_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
  shows "(au (ufe_union ufe x y)) ! i = None \<longleftrightarrow> (uf_list (ufe_union ufe x y)) ! i = i"
proof
  assume prem: "au (ufe_union ufe x y) ! i = None"
  with assms(6) have i: "rep_of l x \<noteq> rep_of l y \<Longrightarrow> a[rep_of l x := Some (length u)] ! i = None"
    by simp
  from assms rep_of_less_length_l ufe_valid_invar_imp_ufa_invar have "rep_of l x < length l" 
    by (metis ufe_data_structure.select_convs(1))
  from length_au assms have "length a = length l" 
    by (metis ufe_data_structure.select_convs(1,3))
  then have "a[rep_of l x := Some (length u)] ! rep_of l x = Some (length u)"
    by (simp add: length_au assms \<open>rep_of l x < length l\<close>)
  with i have "rep_of l x \<noteq> rep_of l y \<Longrightarrow> rep_of l x \<noteq> i"
    by auto
  then show "uf_list (ufe_union ufe x y) ! i = i"
    using prem assms(1,6) i by auto
next 
  assume prem:"uf_list (ufe_union ufe x y) ! i = i"
  with assms ufe_union2_uf_list have "rep_of l x \<noteq> rep_of l y \<Longrightarrow> i \<noteq> rep_of l x" 
    by force
  with assms ufe_union1 show "au (ufe_union ufe x y) ! i = None" 
    by (metis nth_list_update_neq nth_list_update_neq prem ufe_data_structure.select_convs(1,3) ufe_union.simps)
qed

lemma au_none_iff_root:
  assumes "ufe_valid_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    and "i < length l"
  shows "a ! i = None \<longleftrightarrow> l ! i = i"
  using assms proof(induction arbitrary: l u a rule: apply_unions_induct)
  case initial 
  then show ?case by auto
next
  case (union pufe x y)
  obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with union have "a1 ! i = None \<longleftrightarrow> l1 ! i = i"
    by (metis (full_types) ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  have "length l = length l1" 
    by (metis pufe ufe_data_structure.select_convs(1) ufe_union_length_uf_list union.prems(1))
  with union pufe au_none_iff_root_union ufe_union_length_uf_list ufe_data_structure.select_convs(1-3)
  show ?case by metis
qed

lemma au_Some_if_not_root:
  assumes "ufe_valid_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    and "i < length l"
    and "l ! i \<noteq> i"
  obtains k where "a ! i = Some k"
proof-
  from assms au_none_iff_root have "a ! i \<noteq> None" 
    by blast
  then obtain k where "a ! i = Some k" 
    by auto
  then show ?thesis 
    by (simp add: that)
qed

paragraph \<open>Lemmata about invariants wrt. \<open>ufe_union\<close>.\<close>

lemma rep_of_ufa_union_invar:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "x2 < length l"
    and "y2 < length l"
    and "rep_of l x = rep_of l y"
  shows "rep_of (ufa_union l x2 y2) x = rep_of (ufa_union l x2 y2) y"
  using assms ufa_union_aux by simp

lemma rep_of_ufe_union_invar:
  assumes "ufe_valid_invar ufe"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
    and "x2 < length (uf_list ufe)"
    and "y2 < length (uf_list ufe)"
    and "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y"
  shows "rep_of (uf_list (ufe_union ufe x2 y2)) x = rep_of (uf_list (ufe_union ufe x2 y2)) y"
proof-
  obtain l1 u1 a1 where ufe: "ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with assms(1) ufe_valid_invar_imp_ufa_invar have "ufa_invar l1" 
    by (metis ufe_data_structure.select_convs(1))
  with assms rep_of_ufa_union_invar 
  have "rep_of (ufa_union l1 x2 y2) x = rep_of (ufa_union l1 x2 y2) y" 
    by (metis ufe ufe_data_structure.select_convs(1))
  then show ?thesis 
    using assms(6) ufe by auto
qed

lemma au_ufe_union_Some_invar:
  "ufe_valid_invar ufe \<Longrightarrow> (au ufe) ! i = Some k 
    \<Longrightarrow> x < length (uf_list ufe) \<Longrightarrow> y < length (uf_list ufe)
    \<Longrightarrow> (au (ufe_union ufe x y)) ! i = Some k"
proof(cases "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y")
  case True
  then have *: "au (ufe_union ufe x y) = au ufe" 
    by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
  assume "(au ufe) ! i = Some k"
  with * show ?thesis 
    by simp
next
  case False
  assume "(au ufe) ! i = Some k" and invar: "ufe_valid_invar ufe"
    and x: "x < length (uf_list ufe)" and y: "y < length (uf_list ufe)"
  obtain l1 u1 a1 where ufe:"ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with False have *:
"au (ufe_union \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> x y) = a1[rep_of l1 x := Some (length u1)]" 
    by auto
  then show ?thesis
  proof(cases "i = rep_of l1 x")
    case True
    from invar ufe_valid_invar_imp_ufa_invar have "ufa_invar l1" 
      by (metis ufe ufe_data_structure.select_convs(1))
    with rep_of_root x have "l1 ! rep_of l1 x = rep_of l1 x" 
      by (metis ufe ufe_data_structure.select_convs(1))
    from True ufe have "i < length l1" 
      using \<open>ufa_invar l1\<close> rep_of_less_length_l x by auto
    with au_none_iff_root have "au ufe!i = None" 
      using True \<open>l1 ! rep_of l1 x = rep_of l1 x\<close> invar ufe by auto
    then have "False" 
      by (simp add: \<open>au ufe ! i = Some k\<close>)
    then show ?thesis by simp
  next
    case False
    with * have "au (ufe_union \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> x y) ! i = a1 ! i" 
      by simp
    then show ?thesis 
      using \<open>au ufe ! i = Some k\<close> ufe by fastforce
  qed
qed

lemma no_root_ufe_union_invar:
  assumes invar: "ufe_valid_invar ufe"
    and ufe: "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and no_root: "l ! i \<noteq> i" and x: "x < length l" and y: "y < length l"
  shows "(uf_list (ufe_union ufe x y)) ! i = l ! i"
proof(cases "rep_of l x = rep_of l y")
  case True
  then have *: "uf_list (ufe_union ufe x y) = l" 
    using assms(2) by auto
  with * show ?thesis 
    by simp
next
  case False
  with False have *:
    "uf_list (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y) = l[rep_of l x := rep_of l y]" 
    by auto
  then show ?thesis
  proof(cases "i = rep_of l x")
    case True
    from invar ufe_valid_invar_imp_ufa_invar have "ufa_invar l" 
      by (metis ufe ufe_data_structure.select_convs(1))
    with rep_of_root x have "l ! rep_of l x = rep_of l x" 
      by simp
    then show ?thesis 
      using True no_root ufe by fastforce
  next
    case False
    then show ?thesis 
      by (simp add: ufe)
  qed
qed

lemma path_from_rep_ufa_union1:
  assumes "ufa_invar l" and  "x < length l"
    and "rep_of l x \<noteq> rep_of l x2"
    and "x2 < length l" and "y2 < length l"
  shows "path_from_rep (ufa_union l x2 y2) x = path_from_rep l x"
  using assms proof(induction rule: rep_of_induct)
  case (base i)
  then show ?case 
    by (metis length_list_update path_no_cycle path_path_from_rep rep_of_refl ufa_union_aux ufa_union_invar)
next
  case (step i)
  then have "rep_of l (l ! i) \<noteq> rep_of l x2" 
    using rep_of_idx by presburger
  with step have *: "path_from_rep (ufa_union l x2 y2) (l ! i) = path_from_rep l (l ! i)" by auto
  have "path_from_rep_dom (l, i)" 
    using path_from_rep_domain step.hyps(1) step.hyps(2) ufa_invarD(1) by auto
  with step * show ?case 
    by (metis length_list_update nth_list_update_neq path_from_rep.psimps path_from_rep_domain rep_of_idem ufa_invarD(1) ufa_union_invar)
qed

lemma path_from_rep_ufa_union2:
  assumes "ufa_invar l" and  "x < length l"
    and "rep_of l x = rep_of l x2"
    and "x2 < length l" and "y2 < length l"
    and "rep_of l x2 \<noteq> rep_of l y2"
  shows "path_from_rep (ufa_union l x2 y2) x = [rep_of l y2] @ path_from_rep l x"
  using assms proof(induction rule: rep_of_induct)
  case (base i)
  then have base_path:"path_from_rep l i = [i]"
    by (metis path_no_cycle path_path_from_rep rep_of_refl)
  from base have union: "ufa_union l x2 y2 ! i = rep_of l y2"
    by (simp add: rep_of_refl)
  with base have "path_from_rep (ufa_union l x2 y2) i = path_from_rep (ufa_union l x2 y2) ((ufa_union l x2 y2)!i)@[i]"
    by (metis length_list_update path_snoc path_path_from_rep path_unique rep_of_bound rep_of_idx rep_of_refl ufa_union_invar)
  with base base_path union show ?case 
    by (metis append_same_eq length_list_update path_no_cycle path_path_from_rep rep_of_idx rep_of_less_length_l ufa_union_aux ufa_union_invar)   
next
  case (step i)
  let ?new_l = "ufa_union l x2 y2"
  let ?path_root_i = "path_from_rep ?new_l i"
  let ?path_root_l_i = "path_from_rep ?new_l (?new_l ! i)"
  from step have *: "rep_of l (l ! i) = rep_of l x2" 
    by (metis rep_of_step)
  have 1: "path ?new_l (rep_of ?new_l i) ?path_root_i i"
    by (simp add: path_path_from_rep step ufa_union_invar)
  from step have 2: "path ?new_l (rep_of ?new_l i) (?path_root_l_i @ [i]) i"
    by (metis "1" path_nodes_lt_length_l path_snoc path_path_from_rep rep_of_idx ufa_invarD(2) ufa_union_invar ufa_union_root)
  from 1 2 path_unique step have "?path_root_i = ?path_root_l_i @ [i]" 
    using ufa_union_invar by blast
  with step show ?case 
    by (metis Cons_eq_appendI * empty_append_eq_id nth_list_update_neq path_snoc path_path_from_rep path_unique rep_of_min ufa_invarD(2))
qed

lemma ufa_lca_ufa_union_invar:
  assumes "ufa_invar l" and "rep_of l x = rep_of l y"
    and "x < length l" and "y < length l" 
    and "x2 < length l" and "y2 < length l"
  shows "ufa_lca (ufa_union l x2 y2) x y = ufa_lca l x y"
proof(cases "rep_of l x2 = rep_of l x")
  case True
  then show ?thesis 
  proof(cases "rep_of l x2 = rep_of l y2")
    case True
    then show ?thesis 
      by (metis assms(1,5) list_update_id rep_of_root)
  next
    case False
    then have "path_from_rep (ufa_union l x2 y2) y = [rep_of l y2] @ path_from_rep l y"
      using assms path_from_rep_ufa_union2 True by auto
    moreover have "path_from_rep (ufa_union l x2 y2) x = [rep_of l y2] @ path_from_rep l x"
      using assms path_from_rep_ufa_union2 True False by auto 
    ultimately 
    have *: "longest_common_prefix (path_from_rep (ufa_union l x2 y2) x) (path_from_rep (ufa_union l x2 y2) y)
            = [rep_of l y2] @ longest_common_prefix (path_from_rep l x) (path_from_rep l y)"
      by simp
    from path_path_from_rep have hd_x: "hd (path_from_rep l x) = rep_of l x" 
      using assms(1) assms(3) path_hd by blast
    moreover from path_path_from_rep have hd_y: "hd (path_from_rep l y) = rep_of l x" 
      using assms(1) assms(4) path_not_empty by (metis assms(2) path_hd)
    ultimately 
    have "hd (longest_common_prefix (path_from_rep l x) (path_from_rep l y)) = rep_of l x" 
      by (metis list.collapse list.distinct(1) longest_common_prefix.simps)
    with assms path_path_from_rep hd_x hd_y * show ?thesis 
      by (metis last_appendR list.sel(1) longest_common_prefix.simps(1) ufa_lca.simps neq_Nil_conv path_not_empty)
  qed
next
  case False
  then show ?thesis 
    using assms path_from_rep_ufa_union1 by auto
qed

lemma ufa_lca_ufe_union_invar:
  assumes "ufe = \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and "ufe_valid_invar ufe" and "rep_of l x = rep_of l y"
    and "x < length l" and "y < length l" 
    and "x2 < length l" and "y2 < length l"
  shows "ufa_lca (uf_list (ufe_union ufe x2 y2)) x y = ufa_lca l x y"
proof-
  from assms(1,2) have "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_valid_invar_imp_ufa_invar)
  then show ?thesis 
    using assms ufa_lca_ufa_union_invar by auto
qed

lemma find_newest_on_walk_dom_ufe_union:
  assumes "path l y p x" 
    and "ufe_valid_invar ufe" and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l"
    and "y < length l"
    and "x2 < length l"
    and "y2 < length l"
  shows "path (uf_list (ufe_union ufe x2 y2)) y p x"
  using assms proof(induction arbitrary: ufe a u rule: path.induct)
  case (single n l3)
  then have "path (uf_list (ufe_union ufe x2 y2)) n [n] n" 
    by (metis path.single ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  with single show ?case by auto
next
  case (step r l3 u3 p3 v)
  then have p:"path (uf_list (ufe_union ufe x2 y2)) u3 p3 v"
    using path_nodes_lt_length_l by blast
  with step have *: "(uf_list (ufe_union ufe x2 y2)) ! u3 = l3 ! u3" 
    by (metis nth_list_update_neq rep_of_min ufe_data_structure.select_convs(1) ufe_valid_invar_imp_ufa_invar ufe_union1_uf_list ufe_union2_uf_list)
  with step have "r < length (uf_list (ufe_union ufe x2 y2))" 
    by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  with p path.step have "path (uf_list (ufe_union ufe x2 y2)) r (r # p3) v" 
    using * step.hyps(2) step.hyps(3) by auto
  with step show ?case by simp
qed

lemma find_newest_on_walk_ufe_union_invar:
  assumes "path l y p x" 
    and "ufe_valid_invar ufe" and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l" and "y < length l" 
    and "x2 < length l" and "y2 < length l"
  shows "find_newest_on_walk (uf_list (ufe_union ufe x2 y2)) (au (ufe_union ufe x2 y2)) x y = find_newest_on_walk l a x y"
proof-
  from assms have *:"ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_valid_invar_imp_ufa_invar)
  then have "find_newest_on_walk_dom(l, a, x, y)" 
    using assms find_newest_on_walk_domain by auto
  then show ?thesis
    using assms * proof(induction arbitrary: ufe p rule: find_newest_on_walk.pinduct)
    case (1 l3 a3 x3 y3)
    let ?l2 = "uf_list (ufe_union ufe x2 y2)"
      and ?a2 = "au (ufe_union ufe x2 y2)"
    from 1 find_newest_on_walk_dom_ufe_union have path: "path ?l2 y3 p x3" 
      by (metis (no_types, lifting))
    with 1 find_newest_on_walk_domain have dom:"find_newest_on_walk_dom (?l2, ?a2, x3, y3)" 
      by (metis path_nodes_lt_length_l ufe_data_structure.select_convs(1) ufe_valid_invar_imp_ufa_invar union_ufe_valid_invar)
    then show ?case 
    proof(cases "x3 = y3")
      case True
      with 1 dom show ?thesis 
        using find_newest_on_walk.domintros find_newest_on_walk.psimps by presburger
    next
      case False
      with 1(3) path_root have "l3 ! x3 \<noteq> x3" by blast
      with au_Some_if_not_root obtain k where "a3 ! x3 = Some k" 
        using "1.prems" by blast
      with 1 have *:"a3 ! x3 = (au (ufe_union ufe x2 y2)) ! x3" 
        by (metis au_ufe_union_Some_invar ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
      have "?l2 ! x3 = (uf_list (ufe_union ufe x2 y2)) ! x3" 
        by (simp add: "1.prems"(2))
      have "path l3 y3 (butlast p) (l3 ! x3)"
        using "1.prems"(1) False path_butlast by auto
      with 1 have **:"find_newest_on_walk ?l2 ?a2 (l3 ! x3) y3 = find_newest_on_walk l3 a3 (l3 ! x3) y3"
        using False path_nodes_lt_length_l by blast
      have "find_newest_on_walk ?l2 ?a2 x3 y3 = max (?a2 ! x3) (find_newest_on_walk ?l2 ?a2 (?l2 ! x3) y3)"
        by (simp add: False dom find_newest_on_walk.psimps)
      with 1 False dom find_newest_on_walk.psimps * show ?thesis 
        by (metis ** no_root_ufe_union_invar)
    qed
  qed
qed

lemma unions_ufe_union_invar:
  assumes "ufe_valid_invar ufe" and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "i < length u" and "x2 < length l" and "y2 < length l"
  shows "u ! i = (unions (ufe_union ufe x2 y2)) ! i"
proof(cases "rep_of l x2 = rep_of l y2")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  with assms have "unions (ufe_union ufe x2 y2) = u @ [(x2,y2)]" 
    by fastforce
  with assms show ?thesis 
    by simp
qed

lemma path_ufe_union_invar: 
  assumes "path (uf_list ufe) a p b"
    and "ufe_valid_invar ufe"
    and "x2 < length (uf_list ufe)" and "y2 < length (uf_list ufe)"
  shows "path (uf_list (ufe_union ufe x2 y2)) a p b"
  using assms proof(induction "(uf_list ufe)" a p b rule: path.induct)
  case (single n)
  then show ?case 
    using path.single ufe_union_length_uf_list by presburger
next
  case (step r u p v)
  then have "uf_list (ufe_union ufe x2 y2) ! u = r" 
    by (metis nth_list_update_neq rep_of_root ufe_valid_invar_imp_ufa_invar ufe_union_uf_list)
  with step show ?case 
    using path.step ufe_union_length_uf_list by presburger
qed

paragraph \<open>Lemmata about validity of au and find_newest_on_walk\<close>

lemma au_Some_valid:
  assumes "ufe_valid_invar ufe"
    and "i < length (au ufe)"
    and "au ufe ! i = Some x"
  shows "x < length (unions ufe)"
proof-
  from assms(1) have "apply_unions (unions ufe) (initial_ufe (length (uf_list ufe))) = ufe"
    by simp
  with assms show ?thesis
  proof(induction arbitrary: x rule: apply_unions_induct)
    case initial
    then show ?case by auto
  next
    case (union pufe x2 y)
    then show ?case 
    proof(cases "au pufe ! i")
      case None
      then show ?thesis 
      proof(cases "rep_of (uf_list pufe) x2 = rep_of (uf_list pufe) y")
        case True
        have "au (ufe_union pufe x2 y) = au pufe"
          by (metis (full_types) True old.unit.exhaust ufe_data_structure.surjective ufe_union1)
        with None have "au (ufe_union pufe x2 y)! i = None"
          by simp
        with union have "False" by auto
        then show ?thesis by simp
      next
        case False
        obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
          using ufe_data_structure.cases by blast
        with False have rep_of_neq: "rep_of l1 x2 \<noteq> rep_of l1 y"
          by simp
        with pufe have au:
          "au (ufe_union pufe x2 y) = a1[rep_of l1 x2 := Some (length u1)]"
          by simp
        with None pufe have i: "i = rep_of l1 x2" 
          by (metis not_None_eq nth_list_update_neq ufe_data_structure.select_convs(3) union.prems(2))
        from pufe have "unions (ufe_union pufe x2 y) = u1 @ [(x2,y)]" 
          by (simp add: rep_of_neq)
        with union show ?thesis 
          by (simp add: i nth_list_update' pufe rep_of_neq)
      qed
    next
      case (Some a)
      with union have *: "a < length (unions pufe)"
        by (metis Some ufe_union_length_au)
      with ufe_union_length_unions_le * have length_a: "a < length (unions (ufe_union pufe x2 y))"
        apply(cases "rep_of (uf_list pufe) x2 = rep_of (uf_list pufe) y")
        using ufe_union2_unions ufe_union1_unions by auto
      from au_ufe_union_Some_invar have "a = x" 
        using Some union by auto
      then show ?thesis 
        using length_a by blast
    qed
  qed
qed

lemma au_valid:
  assumes "ufe_valid_invar ufe"
    and "i < length (au ufe)"
  shows "au ufe ! i < Some (length (unions ufe))"
  apply(cases "au ufe ! i")
  using assms au_Some_valid by auto

lemma find_newest_on_walk_Some:
  assumes path: "path l y p x"
    and invar: "ufe_valid_invar \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and xy: "x \<noteq> y"
  obtains k where "find_newest_on_walk l a x y = Some k \<and> k < length un"
proof-
  assume a: "\<And>k. find_newest_on_walk l a x y = Some k \<and> k < length un \<Longrightarrow> thesis"
  from invar have 1: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_valid_invar_imp_ufa_invar)
  from path have 2: "x < length l" 
    by (simp add: path_nodes_lt_length_l)
  from path xy path_no_root have no_root: "l ! x \<noteq> x" 
    by auto
  show ?thesis
    using 1 2 assms no_root a proof(induction arbitrary: p thesis rule: rep_of_induct)
    case (base i)
    then show ?case by auto
  next
    case (step v)
    then have "v < length l" 
      using path_nodes_lt_length_l by presburger
    with au_none_iff_root have *: "a ! v \<noteq> None"
      using step by auto
    with * step apply_unions_length_au au_Some_valid have valid_au: "the (a ! v) < length un"
      by (metis \<open>v < length l\<close> option.exhaust_sel ufe_data_structure.select_convs(1-3) length_replicate)    
    then show ?case
    proof(cases "y = l ! v")
      case True
      from step have dom:"find_newest_on_walk_dom (l, a, (l ! v), y)" 
        using True find_newest_on_walk.domintros 
        by presburger
      then have "find_newest_on_walk l a (l ! v) y = None" 
        using step True find_newest_on_walk.psimps 
        by metis
      then have result: "find_newest_on_walk l a v y = a ! v"
        using True dom find_newest_on_walk.domintros find_newest_on_walk.psimps step.prems(3) 
        by fastforce
      from step * show ?thesis 
        using True valid_au result 
        by fastforce
    next
      case False
      from step have path_y_l_v: "path l y (butlast p) (l ! v) " 
        using path_butlast by blast
      with step path_no_root False have "l ! (l ! v) \<noteq> l ! v" 
        by presburger
      with path_y_l_v step False obtain k where 
        IH: "find_newest_on_walk l a (l ! v) y = Some k \<and> k < length un" 
        by blast
      from step have dom: "find_newest_on_walk_dom (l, a, (l ! v), y)"
        using  find_newest_on_walk.domintros 
        by (metis find_newest_on_walk_domain find_newest_on_walk_dom' path_nodes_lt_length_l)
      from \<open>v \<noteq> y\<close> max_def have "find_newest_on_walk l a v y = find_newest_on_walk l a (l ! v) y \<or> 
                               find_newest_on_walk l a v y = a ! v" 
        by (metis dom find_newest_on_walk.domintros find_newest_on_walk.psimps)
      then show ?thesis 
        using "*" IH valid_au step.prems(5) by force
    qed
  qed
qed

paragraph \<open>Additional properties of \<open>find_newest_on_walk\<close>.\<close>

lemma find_newest_on_walk_if_Some:
  assumes "find_newest_on_walk_dom (l, a, x, y)"
    and "find_newest_on_walk l a x y = Some i"
    and "x < length l"
    and  "ufa_invar l"
  shows "l ! x \<noteq> x \<and> x \<noteq> y"
  using assms proof(induction arbitrary: i rule: find_newest_on_walk.pinduct)
  case (1 l a x y)
  then show ?case 
  proof(cases "x = y")
    case True
    have "False" 
      using 1 True find_newest_on_walk.psimps by auto
    then show ?thesis by simp
  next
    case False
    have "l ! x < length l" 
      by (simp add: 1 ufa_invarD(2))
    have "max (a ! x) (find_newest_on_walk l a (l!x) y) = Some i" 
      using 1 False find_newest_on_walk.psimps by force
    then have "find_newest_on_walk l a (l ! x) y = Some i \<or> a ! x = Some i" 
      by (metis max_def)
    then show ?thesis 
    proof
      show ?thesis 
        using 1 False path_root by force
    next
      assume ax: "a ! x = Some i"
      then show ?thesis 
        using 1 False \<open>l ! x < length l\<close> by auto
    qed
  qed
qed

lemma find_newest_on_walk_if_None:
  assumes path: "path l y p x"
    and invar: "ufe_valid_invar \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and None: "find_newest_on_walk l a x y = None"
  shows "x = y"
proof-
  have "\<nexists> k. find_newest_on_walk l a x y = Some k \<and> k < length un"
    by (simp add: None)
  with find_newest_on_walk_Some show ?thesis 
    by (metis invar path)
qed

lemma find_newest_on_walk_valid:
  assumes path: "path l y p x"
    and invar: "ufe_valid_invar \<lparr>uf_list = l, unions = un, au = a\<rparr>"
  shows "find_newest_on_walk l a x y < Some (length un)"
proof(cases "x = y")
  case True
  then have "find_newest_on_walk_dom (l, a, x, y)" 
    using find_newest_on_walk.domintros by blast
  with find_newest_on_walk_if_Some have "find_newest_on_walk l a x y = None" 
    using True find_newest_on_walk.psimps by auto
  then show ?thesis by simp
next
  case False
  with assms find_newest_on_walk_Some obtain k where "find_newest_on_walk l a x y = Some k" and "k < length un"
    by metis
  then show ?thesis by simp
qed

lemma find_newest_x_neq_None_or_find_newest_y_neq_None:
  assumes "x \<noteq> y"
    and "ufe_valid_invar  \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and "x < length l"
    and "y < length l"
    and "rep_of l x = rep_of l y"
  shows "find_newest_on_walk l a y (ufa_lca l x y) \<noteq> None
          \<or> find_newest_on_walk l a x (ufa_lca l x y) \<noteq> None"
proof(rule ccontr)
  from ufe_valid_invar_imp_ufa_invar have "ufa_invar l" 
    by (metis assms(2) ufe_data_structure.select_convs(1))
  with is_lca_ufa_lca assms ufe_valid_invar_imp_ufa_invar obtain pLcaX pLcaY 
    where pLcaX: "path l (ufa_lca l x y) pLcaX x" and pLcaY:"path l (ufa_lca l x y) pLcaY y"
    by presburger
  then have dom_y: "find_newest_on_walk_dom(l, a, y, (ufa_lca l x y))"
    and dom_x: "find_newest_on_walk_dom(l, a, x, (ufa_lca l x y))"
    using \<open>ufa_invar l\<close> find_newest_on_walk_domain path_nodes_lt_length_l by auto
  assume assm:"\<not> (find_newest_on_walk l a y (ufa_lca l x y) \<noteq> None \<or>
                find_newest_on_walk l a x (ufa_lca l x y) \<noteq> None)"
  then have "find_newest_on_walk l a x (ufa_lca l x y) = None" by simp
  with dom_x assms pLcaX
    find_newest_on_walk_if_None have x: "x = ufa_lca l x y" 
    by blast
  with dom_y assms pLcaY
    find_newest_on_walk_if_None have "y = ufa_lca l x y" 
    using assm by blast
  then show "False" 
    using x assms(1) by linarith
qed
*)

end