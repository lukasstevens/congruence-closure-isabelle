section \<open>Correctness of merge and \<open>are_congruent\<close>: \<close>
theory CC_Abstraction
  imports CC_Helper_Functions
begin

subsection \<open>Abstract formalisation of congruence closure\<close>


text \<open>S is the set of input equations.
The Congruence Closure is the smallest relation that includes S and is closed under reflexivity,
symmetry, transitivity, and under function application.
Source: \<^url>\<open>https://drops.dagstuhl.de/opus/volltexte/2021/14253/pdf/LIPIcs-FSCD-2021-15.pdf\<close>\<close>

inductive_set Congruence_Closure :: "equation set \<Rightarrow> equation set" for S
  where
    base: "eqt \<in> S \<Longrightarrow> eqt \<in> Congruence_Closure S"
  | reflexive: "(a \<approx> a) \<in> Congruence_Closure S"
  | symmetric: "(a \<approx> b) \<in> Congruence_Closure S \<Longrightarrow> (b \<approx> a) \<in> Congruence_Closure S"
  | transitive1:
    "(a \<approx> b) \<in> Congruence_Closure S \<Longrightarrow> (b \<approx> c) \<in> Congruence_Closure S  
    \<Longrightarrow> (a \<approx> c) \<in> Congruence_Closure S"
  | transitive2:
    "(F a\<^sub>1 a\<^sub>2 \<approx> b) \<in> Congruence_Closure S \<Longrightarrow> (b \<approx> c) \<in> Congruence_Closure S  
    \<Longrightarrow> (F a\<^sub>1 a\<^sub>2 \<approx> c) \<in> Congruence_Closure S"
  | transitive3:
    "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> Congruence_Closure S
    \<Longrightarrow> (a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure S \<Longrightarrow> (a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure S
    \<Longrightarrow> (F b\<^sub>1 b\<^sub>2 \<approx> a) \<in> Congruence_Closure S"
  | monotonic:
    "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> Congruence_Closure S \<Longrightarrow> (F a\<^sub>1 a\<^sub>2 \<approx> b) \<in> Congruence_Closure S 
    \<Longrightarrow> (a \<approx> b) \<in> Congruence_Closure S"

declare Congruence_Closure.intros[intro]

definition CC_union :: "equation set \<Rightarrow> equation \<Rightarrow> equation set" where
  "CC_union CC eq' = Congruence_Closure (CC \<union> {eq'})"

lemma Congruence_Closure_union:
  "Congruence_Closure S \<subseteq> Congruence_Closure (S \<union> S')"
proof
  fix x 
  show "x \<in> Congruence_Closure S \<Longrightarrow> x \<in> Congruence_Closure (S \<union> S')"
    apply(induction rule: Congruence_Closure.induct)
    by auto
qed

lemma Congruence_Closure_union':
  "Congruence_Closure S \<subseteq> Congruence_Closure (S' \<union> S)"
  by (metis Congruence_Closure_union sup_commute)

lemma Congruence_Closure_split_rule:
  assumes "k \<notin> B \<Longrightarrow> k \<in> Congruence_Closure A"
  shows "k \<in> Congruence_Closure (A \<union> B)"
  using assms Congruence_Closure_union by blast

lemma CC_union_correct: 
  "CC_union (Congruence_Closure S) eq' = Congruence_Closure (S \<union> {eq'})"
proof
  show "CC_union (Congruence_Closure S) eq' \<subseteq> Congruence_Closure (S \<union> {eq'})"
  proof
    fix x
    show "x \<in> CC_union (Congruence_Closure S) eq' \<Longrightarrow> x \<in> Congruence_Closure (S \<union> {eq'})"
      unfolding CC_union_def
      apply(induction x rule: Congruence_Closure.induct)
      using base Congruence_Closure_union by blast+
  qed
next
  show "Congruence_Closure (S \<union> {eq'}) \<subseteq> CC_union (Congruence_Closure S) eq'"
  proof
    fix x 
    show "x \<in> Congruence_Closure (S \<union> {eq'}) \<Longrightarrow> x \<in> CC_union (Congruence_Closure S) eq'"
      apply(induction x rule: Congruence_Closure.induct)
      unfolding CC_union_def 
      by auto
  qed
qed

lemma Congruence_Closure_not_empty_F:
  "(F a b \<approx> c) \<in> Congruence_Closure A \<Longrightarrow> A \<noteq> {}"
  apply(induction "(F a b \<approx> c)" arbitrary: a b c rule: Congruence_Closure.induct)
  by auto

lemma Congruence_Closure_not_empty:
  "(a \<approx> b) \<in> Congruence_Closure A \<Longrightarrow> a \<noteq> b \<Longrightarrow> A \<noteq> {}"
  apply(induction "(a \<approx> b)" arbitrary: a b rule: Congruence_Closure.induct)
  using Congruence_Closure_not_empty_F by auto

lemma Congruence_Closure_empty_aux:
  "x \<in> Congruence_Closure A \<Longrightarrow> A = {} \<Longrightarrow> (\<exists> a . x = (a \<approx> a))"
  apply(induction x arbitrary: rule: Congruence_Closure.induct)
  by auto

lemma Congruence_Closure_empty:
  "x \<in> Congruence_Closure {} \<longleftrightarrow> (\<exists> a . x = (a \<approx> a))"
proof
  from Congruence_Closure_empty_aux show "x \<in> Congruence_Closure {} \<Longrightarrow> \<exists>a. x = (a \<approx> a)" 
    by blast
  from Congruence_Closure.intros show "\<exists>a. x = (a \<approx> a) \<Longrightarrow> x \<in> Congruence_Closure {}"
    by blast
qed

lemma Congruence_Closure_imp: 
  assumes "x \<in> Congruence_Closure A" "\<And> a. a \<in> A \<Longrightarrow> a \<in> Congruence_Closure B"
  shows "x \<in> Congruence_Closure B"
  using assms apply(induction x rule: Congruence_Closure.induct)
  by auto

lemma Congruence_Closure_monotonic:
  "S \<subseteq> S' \<Longrightarrow> Congruence_Closure S \<subseteq> Congruence_Closure S'"
proof
  fix x 
  assume subset: "S \<subseteq> S'"
  show "x \<in> Congruence_Closure S \<Longrightarrow> x \<in> Congruence_Closure S'"
    apply(rule Congruence_Closure_imp)
    using subset by blast+
qed

text \<open>Rule to find if the congruence closure of two sets is equal\<close>
lemma Congruence_Closure_eq[case_names left right]:
  assumes "\<And> a. a \<in> A \<Longrightarrow> a \<in> Congruence_Closure B"
    "\<And> b. b \<in> B \<Longrightarrow> b \<in> Congruence_Closure A"
  shows "Congruence_Closure A = Congruence_Closure B"
proof(standard)
  show "Congruence_Closure A \<subseteq> Congruence_Closure B"
  proof
    fix x 
    assume CC_A: "x \<in> Congruence_Closure A"
    show "x \<in> Congruence_Closure B"
      using CC_A Congruence_Closure_imp assms(1) by blast
  qed
next 
  show "Congruence_Closure B \<subseteq> Congruence_Closure A"
  proof
    fix x
    assume CC_B: "x \<in> Congruence_Closure B"
    show "x \<in> Congruence_Closure A"
      using CC_B Congruence_Closure_imp assms(2) by blast
  qed
qed

fun valid_vars :: "equation \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_vars (a \<approx> b) n = (a < n \<and> b < n)"
| "valid_vars (F a b \<approx> c) n = (a < n \<and> b < n \<and> c < n)"

fun valid_vars_pending :: "pending_equation \<Rightarrow> nat list \<Rightarrow> bool" where
  "valid_vars_pending (One (a \<approx> b)) l = (valid_vars (a \<approx> b) (length l))"
| "valid_vars_pending (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) l = 
    (valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (length l) \<and> valid_vars (F b\<^sub>1 b\<^sub>2 \<approx> b) (length l) \<and>
    rep_of l a\<^sub>1 = rep_of l b\<^sub>1 \<and> rep_of l a\<^sub>2 = rep_of l b\<^sub>2)"
| "valid_vars_pending _ _ = False"

lemma valid_vars_pending_iff: 
  "valid_vars_pending a l \<longleftrightarrow> (\<exists> b c . b < length l \<and> c < length l \<and> a = (One (b \<approx> c))) \<or>
(\<exists> b c d e f g . b < length l \<and> c < length l \<and> d < length l \<and> e < length l \<and> f < length l
 \<and> g < length l \<and> a = (Two (F b c \<approx> d) (F e f \<approx> g))
\<and> rep_of l b = rep_of l e \<and> rep_of l c = rep_of l f)"
  (is "?P \<longleftrightarrow> ?Q")
proof
  show "?P \<Longrightarrow> ?Q" apply(cases a) 
    using valid_vars_pending.elims(2) apply fastforce 
    using valid_vars_pending.elims by (metis pending_equation.distinct(1) valid_vars.simps(2))
  show "?Q \<Longrightarrow> ?P"
    apply(cases a) 
    by auto
qed

lemma valid_vars_pending_cases[consumes 1, case_names One Two]:
  assumes "valid_vars_pending eq l"
  obtains a b where "eq = One (a \<approx> b)" "a < length l" "b < length l"
  | a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b where "eq = Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "a < length l" "b\<^sub>1 < length l" "b\<^sub>2 < length l" "b < length l"
    "rep_of l a\<^sub>1 = rep_of l b\<^sub>1" "rep_of l a\<^sub>2 = rep_of l b\<^sub>2"
  using assms valid_vars_pending_iff by force

abbreviation nr_vars :: "cc_state \<Rightarrow> nat" where
  "nr_vars ccs \<equiv> length (cc_list ccs)"

abbreviation cc_list_set :: "nat list \<Rightarrow> equation set" where
  "cc_list_set l \<equiv> {a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a}"

abbreviation lookup_entries_set :: "cc_state \<Rightarrow> equation set" where
  "lookup_entries_set ccs \<equiv>
    {F a' b' \<approx> rep_of (cc_list ccs) c | a' b' c c\<^sub>1 c\<^sub>2.
      a' < nr_vars ccs \<and> b' < nr_vars ccs \<and> c < nr_vars ccs \<and>
      cc_list ccs ! a' = a' \<and> cc_list ccs ! b' = b' \<and>
      lookup ccs ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)}"

definition representativeE :: "cc_state \<Rightarrow> equation set" where
  "representativeE ccs = cc_list_set (cc_list ccs) \<union> lookup_entries_set ccs"

text \<open>Converts the list of pending equations to a set of pending equations.\<close>
fun pending_set :: "pending_equation list \<Rightarrow> equation set" where
  "pending_set [] = {}"
| "pending_set (a # xs) = {left a \<approx> right a} \<union> pending_set xs"

lemma pending_set_empty_iff_pending_empty:
  "pending_set pe = {} \<longleftrightarrow> pe = []"
proof
  show "pending_set pe = {} \<Longrightarrow> pe = []"
    apply(induction pe rule: pending_set.induct)
    by (simp_all)
  show "pe = [] \<Longrightarrow> pending_set pe = {}" by simp
qed

lemma pending_set_union: 
  "pending_set (xs @ ys) = pending_set xs \<union> pending_set ys"
  apply(induction xs rule: pending_set.induct)
  by simp_all

lemma pending_set_Cons: 
  "pending_set (x # ys) = pending_set [x] \<union> pending_set ys"
  by (metis append.left_neutral append_Cons pending_set_union)

lemma pending_set_union':
  "a \<in> pending_set (xs @ ys) \<longleftrightarrow> a \<in> pending_set xs \<or> a \<in> pending_set ys" 
  by (simp add: pending_set_union)

lemma pending_set_Constant:
  assumes "eq \<in> pending_set pe"
  obtains a b where "eq = (a \<approx> b)"
  using assms apply(induction rule: pending_set.induct)
  by auto

subsection \<open>Invariants  definitions\<close>
text \<open>As described in the paper\<close>

text \<open>For \<open>cc_list_invar\<close> we use \<open>ufa_invar\<close>\<close>

definition cc_list_invar :: "cc_state \<Rightarrow> bool" where
  "cc_list_invar ccs = ufa_invar (cc_list ccs)"

text \<open>for each representative i, UseList (i) is a list of input equations \<open>f(b\<^sub>1, b\<^sub>2)=b\<close>
such that i is the representative of \<open>b\<^sub>1\<close> or of \<open>b\<^sub>2\<close> (or of both).\<close>
abbreviation use_list_valid_element where
  "use_list_valid_element u_i_j l i \<equiv> \<exists>b\<^sub>1 b\<^sub>2 b.
    u_i_j = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
    (i = rep_of l b\<^sub>1 \<or> i = rep_of l b\<^sub>2) \<and>
    (b\<^sub>1 < length l \<and> b\<^sub>2 < length l \<and> b < length l)"

definition use_list_invar :: "cc_state \<Rightarrow> bool" where
  "use_list_invar ccs \<equiv> \<forall>i < nr_vars ccs.
    cc_list ccs ! i = i \<longrightarrow> (\<forall>j < length (use_list ccs ! i). 
      use_list_valid_element (use_list ccs ! i ! j) (cc_list ccs) i)"

text \<open>for all pairs of representatives (i, j), Lookup(i, j) is some input equation
\<open>f(a\<^sub>1, a\<^sub>2)=a\<close> such that i and j are the current respective representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> whenever
such an equation exists. Otherwise, Lookup(i, j) is \<open>\<bottom>\<close>\<close>
abbreviation lookup_invar_correctness :: "cc_state \<Rightarrow> bool" where
  "lookup_invar_correctness ccs \<equiv> \<forall> i < nr_vars ccs. \<forall>j < nr_vars ccs.
    (cc_list ccs) ! i = i \<and> (cc_list ccs) ! j = j \<longrightarrow> 
      lookup_valid_element (lookup ccs) (cc_list ccs) i j"

text \<open>Lookup is also a square matrix.\<close>
definition lookup_invar :: "cc_state \<Rightarrow> bool" where
  "lookup_invar ccs \<equiv> lookup_invar_correctness ccs \<and> quadratic_table (lookup ccs)"

text \<open>This invariant is needed for the termination proof of \<open>add_edge\<close>:\<close>

definition proof_forest_invar :: "cc_state \<Rightarrow> bool" where
  "proof_forest_invar ccs \<equiv> ufa_invar (proof_forest ccs)"

text \<open>The equations in pending can only be of these specific forms:\<close>

definition pending_invar :: "cc_state \<Rightarrow> bool" where
  "pending_invar ccs \<equiv> \<forall>i < length (pending ccs). 
    valid_vars_pending (pending ccs ! i) (cc_list ccs)"

lemma pending_invar_Cons:
  assumes "pending ccs = pe # xs"
  shows "pending_invar ccs \<longleftrightarrow>
         pending_invar (ccs\<lparr> pending := xs \<rparr>) \<and> valid_vars_pending pe (cc_list ccs)"
  (is "?left \<longleftrightarrow> ?right")
proof
  from assms show "?right \<Longrightarrow> ?left"
    unfolding pending_invar_def using less_Suc_eq_0_disj
    by (cases ccs) force
qed (use assms in \<open>auto simp: pending_invar_def\<close>)

lemma pending_left_right_valid': 
  assumes valid: "valid_vars_pending pe l"
  shows "right pe < length l \<and> left pe < length l"
proof(cases pe)
  case (One x1)
  with One valid obtain x11 x12 where Constants: "x1 = (x11 \<approx> x12)" 
    by (metis equation.exhaust valid_vars_pending.simps(3))
  with One have "left pe = x11" by simp
  with Constants One valid show ?thesis by auto
next
  case (Two x21 x22)
  with valid obtain x211 x212 x213 x221 x222 x223 
    where Function: "x21 = (F x211 x212 \<approx> x213)"  "x22 = (F x221 x222 \<approx> x223)" 
    by (metis Two equation.exhaust valid_vars_pending.simps(4) valid_vars_pending.simps(5))
  then show ?thesis using Two valid by auto
qed

lemma pending_left_right_valid: 
  assumes "pending_invar ccs"
  assumes "pending ccs = pe # pes"
  shows "right pe < length (cc_list ccs) \<and> left pe < length (cc_list ccs)"
  using assms pending_left_right_valid' 
  unfolding pending_invar_def by (cases ccs) auto

text \<open>The second invariant from the article, very important for the correctness proof.\<close>

definition correctness_invar :: "cc_state \<Rightarrow> bool" where
  "correctness_invar ccs \<equiv> 
    Congruence_Closure (representativeE ccs \<union> pending_set (pending ccs)) =
    Congruence_Closure (input ccs)"

text \<open>The union find data structure and the proof forest have the same equivalence classes. \<close>
definition same_eq_classes_invar :: "cc_state \<Rightarrow> bool" where
  "same_eq_classes_invar ccs \<equiv>
    let l = cc_list ccs; pf = proof_forest ccs in
      \<forall>i < length pf. \<forall>j < length pf.
        rep_of l i = rep_of l j \<longleftrightarrow> rep_of pf i = rep_of pf j"

lemma same_eq_classes_invarD: 
  assumes "i < length (proof_forest ccs)" "j < length (proof_forest ccs)"
      and "same_eq_classes_invar ccs"
    shows "rep_of (cc_list ccs) i = rep_of (cc_list ccs) j \<longleftrightarrow>
           rep_of (proof_forest ccs) i = rep_of (proof_forest ccs) j"
  using assms unfolding same_eq_classes_invar_def Let_def by blast

text \<open>The lists in the data structure all have the same length.\<close>
definition same_length_invar :: "cc_state \<Rightarrow> nat \<Rightarrow> bool" where
  "same_length_invar ccs n \<equiv> 
    nr_vars ccs = n \<and> length (use_list ccs) = n \<and> length (lookup ccs) = n \<and> 
    length (proof_forest ccs) = n \<and> length (pf_labels ccs) = n"


text \<open>The following two invariants are important for the proofs about correctness_invar:\<close>
text \<open>All equations in the lookup table are also present in both relevant use_lists.\<close>

abbreviation contains_similar_equation where
  "contains_similar_equation cc a' c\<^sub>1 c\<^sub>2 c \<equiv> \<exists>b\<^sub>1 b\<^sub>2 b.
    (F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> set (use_list cc ! a') \<and>
    rep_of (cc_list cc) b\<^sub>1 = rep_of (cc_list cc) c\<^sub>1 \<and>
    rep_of (cc_list cc) b\<^sub>2 = rep_of (cc_list cc) c\<^sub>2 \<and>
    (b \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list cc) \<union> pending_set (pending cc))"

definition lookup_invar2 :: "cc_state \<Rightarrow> bool" where
  "lookup_invar2 ccs \<equiv> \<forall>a' b' c c\<^sub>1 c\<^sub>2.
    a' < nr_vars ccs \<and> b' < nr_vars ccs \<and>
    cc_list ccs ! a' = a' \<and> cc_list ccs ! b' = b' \<and>
    lookup ccs ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)
    \<longrightarrow> contains_similar_equation ccs a' c\<^sub>1 c\<^sub>2 c \<and>
        contains_similar_equation ccs b' c\<^sub>1 c\<^sub>2 c"

text \<open>All equations in the use list are also in the lookup table.\<close>
definition use_list_invar2' :: "cc_state \<Rightarrow> equation list \<Rightarrow> bool" where
  "use_list_invar2' ccs u_a \<equiv> \<forall>a' c\<^sub>1 c\<^sub>2 c.
    a' < nr_vars ccs \<and> cc_list ccs ! a' = a' \<and> (F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (use_list ccs ! a')
    \<longrightarrow> 
      (\<exists> b\<^sub>1 b\<^sub>2 b.
        lookup_entry (lookup ccs) (cc_list ccs) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
        (b \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ccs) \<union> pending_set (pending ccs))
        \<or>
        (F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> set u_a \<and>
        rep_of (cc_list ccs) b\<^sub>1 = rep_of (cc_list ccs) c\<^sub>1 \<and>
        rep_of (cc_list ccs) b\<^sub>2 = rep_of (cc_list ccs) c\<^sub>2 \<and>
        (b \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ccs) \<union> pending_set (pending ccs))
      )"

abbreviation use_list_invar2 :: "cc_state \<Rightarrow> bool" where
  "use_list_invar2 ccs \<equiv> use_list_invar2' ccs []"

lemma use_list_invar2_def:
  "use_list_invar2 ccs = (\<forall> a' c\<^sub>1 c\<^sub>2 c.
    a' < nr_vars ccs \<and> cc_list ccs ! a' = a' \<and> (F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (use_list ccs ! a')
    \<longrightarrow> 
      (\<exists>b\<^sub>1 b\<^sub>2 b.
        lookup_entry (lookup ccs) (cc_list ccs) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
        (b \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ccs) \<union> pending_set (pending ccs))
      )
  )"
  unfolding use_list_invar2'_def by simp

text \<open>Invariants needed for the correctness proof of \<open>cc_explain\<close>\<close>

text \<open>The labels of the proof forest are added from the pending list, therefore the 
\<open>valid_vars_pending\<close> invariant holds for them too. Additionally, the variables in the label 
of an edge correspond to the vertices connected by the edge. \<close>
abbreviation valid_labels_invar ::
  "pending_equation option list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "valid_labels_invar pfl pf l \<equiv> \<forall>n < length pf.
    if pf ! n \<noteq> n
      then
        (\<exists>a a\<^sub>1 a\<^sub>2 b b\<^sub>1 b\<^sub>2.
          (pfl ! n = Some (One (a \<approx> b)) \<or> pfl ! n = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))) \<and>
          (a = pf ! n \<and> b = n \<or> a = n \<and> b = pf ! n) \<and>
          valid_vars_pending (the (pfl ! n)) l
        )
      else pfl ! n = None"

definition pf_labels_invar :: "cc_state \<Rightarrow> bool" where
  "pf_labels_invar ccs \<equiv> valid_labels_invar (pf_labels ccs) (proof_forest ccs) (cc_list ccs)"

abbreviation cc_invar :: "cc_state \<Rightarrow> bool" where
  "cc_invar ccs \<equiv>
      cc_list_invar ccs \<and> use_list_invar ccs \<and> lookup_invar ccs \<and>
      proof_forest_invar ccs \<and> correctness_invar ccs \<and> same_eq_classes_invar ccs \<and>
      same_length_invar ccs (nr_vars ccs) \<and> pending_invar ccs \<and> lookup_invar2 ccs \<and>
      use_list_invar2 ccs \<and> pf_labels_invar ccs"

text \<open>
(1) Prove that it works for the \<open>"mini_step"\<close>.
(2) Prove that the invariant is preserved by the two cases of \<open>propagate_loop\<close>.
\<close>
lemma propagate_step_induct[consumes 3, case_names base update_pending update_lookup]:
  assumes "ufa_invar l" "a < length l" "b < length l"
  assumes base:
    "P \<lparr> cc_list = ufa_union l a b
       , use_list = u[rep_of l a := []]
       , lookup = t
       , pending = pe
       , proof_forest = add_edge pf a b
       , pf_labels = add_label pfl pf a eq
       , input = ip
       \<rparr>"
  assumes update_pending:
    "\<And>ccs u1.
      \<lbrakk> P ccs; lookup_Some (lookup ccs) (cc_list ccs) u1 \<rbrakk>
      \<Longrightarrow> P (ccs\<lparr> pending := link_to_lookup (lookup ccs) (cc_list ccs) u1 # pending ccs \<rparr>)"
  assumes update_lookup:
    "\<And>ccs u1 rep_b.
      \<lbrakk> P ccs; \<not> lookup_Some (lookup ccs) (cc_list ccs) u1; rep_of (cc_list ccs) b = rep_b \<rbrakk>
      \<Longrightarrow> P (ccs \<lparr> use_list := (use_list ccs)[rep_b := u1#(use_list ccs ! rep_b)]
                 , lookup := update_lookup (lookup ccs) (cc_list ccs) u1
                 \<rparr>)"
  shows "P (propagate_step \<lparr> cc_list = l, use_list = u, lookup = t, pending = pe
                           , proof_forest = pf, pf_labels = pfl, input = ip 
                           \<rparr> a b eq)"
proof -
  have loop: "P (propagate_loop rep_b urest ccs)"
    if "P ccs" "rep_of (cc_list ccs) b = rep_b" for ccs rep_b urest
    using that
  proof(induction rep_b urest ccs rule: propagate_loop.induct)
    case (1 rep_b u1 urest ccs)
    then show ?case
      by (auto dest: update_pending update_lookup)
  qed simp
  moreover have "rep_of l b = rep_of (ufa_union l a b) b" 
    using assms ufa_union_aux by auto
  ultimately show ?thesis 
    using base by force
qed

subsection \<open>Lemmata for \<open>Congruence_Closure\<close> with our \<open>congruence_closure\<close> data structure\<close>

lemma a_eq_rep_of_a_in_CC_cc_list_set:
  assumes "a < length l"
  shows
    "(a \<approx> rep_of l a) \<in> Congruence_Closure (cc_list_set l)"
    "(rep_of l a \<approx> a) \<in> Congruence_Closure (cc_list_set l)"
proof-
  have *: "rep_of l a = a \<Longrightarrow> (a \<approx> rep_of l a) \<in> Congruence_Closure (cc_list_set l)" 
    by auto
  have "rep_of l a \<noteq> a \<Longrightarrow> (a \<approx> rep_of l a) \<in> (cc_list_set l)" 
    unfolding representativeE_def using assms rep_of_refl by force
  then have "rep_of l a \<noteq> a \<Longrightarrow> (a \<approx> rep_of l a) \<in> Congruence_Closure (cc_list_set l)" 
    by auto
  with * show "(a \<approx> rep_of l a) \<in> Congruence_Closure (cc_list_set l)" 
    by blast
  with symmetric show "(rep_of l a \<approx> a) \<in> Congruence_Closure (cc_list_set l)" 
    by simp
qed

lemma a_eq_rep_of_a_in_CC:
  assumes "a < length (cc_list ccs)"
  shows
    "(a \<approx> rep_of (cc_list ccs) a) \<in> Congruence_Closure (representativeE ccs)"
    "(rep_of (cc_list ccs) a \<approx> a) \<in> Congruence_Closure (representativeE ccs)"
  unfolding representativeE_def using assms Congruence_Closure_union a_eq_rep_of_a_in_CC_cc_list_set
  by blast+

lemma CC_F_rep_of_a_imp_F_a:
  assumes "(F (rep_of (cc_list ccs) a) (rep_of (cc_list ccs) b) \<approx> (rep_of (cc_list ccs) c))
            \<in> Congruence_Closure (representativeE ccs)"
      and "a < nr_vars ccs" "b < nr_vars ccs" "c < nr_vars ccs"
    shows "(F a b \<approx> c) \<in> Congruence_Closure (representativeE ccs)"
proof-
  from assms a_eq_rep_of_a_in_CC have 
    "(rep_of (cc_list ccs) a \<approx> a) \<in> Congruence_Closure (representativeE ccs)"
    "(rep_of (cc_list ccs) b \<approx> b) \<in> Congruence_Closure (representativeE ccs)"
    "(rep_of (cc_list ccs) c \<approx> c) \<in> Congruence_Closure (representativeE ccs)"
    by blast+
  with assms show ?thesis by blast
qed

lemma CC_rep_of_a_imp_a:
  assumes "(rep_of (cc_list ccs) a \<approx> rep_of (cc_list ccs) c)
            \<in> Congruence_Closure (representativeE ccs) "
      and "a < nr_vars ccs" "c < nr_vars ccs"
    shows "(a \<approx> c) \<in> Congruence_Closure (representativeE ccs)"
proof-
  from assms a_eq_rep_of_a_in_CC have 
    "(rep_of (cc_list ccs) a \<approx> a) \<in> Congruence_Closure (representativeE ccs)"
    "(rep_of (cc_list ccs) c \<approx> c) \<in> Congruence_Closure (representativeE ccs)"
    by blast+
  with assms show ?thesis by blast 
qed

lemma CC_lookup_entry_in_CC:
  assumes "lookup_invar ccs"
      and "cc_list ccs ! a = a" "cc_list ccs ! b = b"
      and "lookup ccs ! a ! b = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
      and "a < nr_vars ccs" "b < nr_vars ccs" "c < nr_vars ccs"
    shows "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> Congruence_Closure (representativeE ccs)"
proof-
  from assms base have base: 
    "(F a b \<approx> rep_of (cc_list ccs) c) \<in> Congruence_Closure (representativeE ccs)"
    unfolding representativeE_def 
    by simp
  from assms have "c\<^sub>1 < nr_vars ccs" "c\<^sub>2 < nr_vars ccs" "c < nr_vars ccs"
    unfolding lookup_invar_def by fastforce+
  with assms a_eq_rep_of_a_in_CC have rep:
    "(rep_of (cc_list ccs) c\<^sub>1 \<approx> c\<^sub>1) \<in> Congruence_Closure (representativeE ccs)"
    "(rep_of (cc_list ccs) c\<^sub>2 \<approx> c\<^sub>2) \<in> Congruence_Closure (representativeE ccs)"
    "(rep_of (cc_list ccs) c \<approx> c) \<in> Congruence_Closure (representativeE ccs)"
    by blast+
  from assms have a_b: "rep_of (cc_list ccs) c\<^sub>1 = a" "rep_of (cc_list ccs) c\<^sub>2 = b"
    unfolding lookup_invar_def by fastforce+
  then have "(F c\<^sub>1 c\<^sub>2 \<approx> rep_of (cc_list ccs) c) \<in> Congruence_Closure (representativeE ccs)" 
    using base rep by blast
  with assms rep show ?thesis
    by fast
qed

lemma CC_same_rep_cc_list_set:
  assumes "rep_of l a = rep_of l b"
      and "a < length l" "b < length l"
    shows "(a \<approx> b) \<in> Congruence_Closure (cc_list_set l)"
proof-
  have
    "(a \<approx> rep_of l a) \<in> Congruence_Closure (cc_list_set l)"
    "(rep_of l b \<approx> b) \<in> Congruence_Closure (cc_list_set l)"
    using assms by (auto dest: a_eq_rep_of_a_in_CC_cc_list_set)
  then show ?thesis 
    using assms(1) by auto
qed

lemma CC_same_rep:
  assumes "rep_of (cc_list cc) a = rep_of (cc_list cc) b"
      and "a < nr_vars cc" "b < nr_vars cc"
    shows "(a \<approx> b) \<in> Congruence_Closure (representativeE cc)"
  using CC_same_rep_cc_list_set assms Congruence_Closure_union
  unfolding representativeE_def 
  by blast

lemma pending_a_b_in_Congruence_Closure:
  assumes "valid_vars_pending eq (cc_list cc)" "a = left eq" "b = right eq" 
    shows "(a \<approx> b) \<in> Congruence_Closure (representativeE cc \<union> pending_set [eq])"
  using assms by (induction rule: valid_vars_pending_cases) auto

lemma pending_a_b_in_Congruence_Closure':
  assumes "a = left eq" "b = right eq" 
    shows "(a \<approx> b) \<in> Congruence_Closure (representativeE cc \<union> pending_set (eq # pe))"
  using UnI1 assms by auto

subsection \<open>These functions preserve the length of the parameters.\<close>

lemma add_edge_preserves_length:
  "add_edge_dom (pf, a, b) \<Longrightarrow> length (add_edge pf a b) = length pf"
  by (induction pf a b rule: add_edge.pinduct) (simp add: add_edge.psimps)

lemma add_edge_preserves_length':
  assumes "ufa_invar pf" "a < length pf" "b < length pf" "rep_of pf a \<noteq> rep_of pf b" 
    shows "length (add_edge pf a b) = length pf"
  using add_edge_domain add_edge_preserves_length assms by blast

lemma add_label_preserves_length:
  "add_label_dom (pfl, pf, a, eq) \<Longrightarrow> length (add_label pfl pf a eq) = length pfl"
  by (induction pfl pf a eq rule: add_label.pinduct) (simp add: add_label.psimps)

lemma add_label_preserves_length':
  assumes "ufa_invar pf" "a < length pf"  
    shows "length (add_label pfl pf a eq) = length pfl"
  using add_label_domain add_label_preserves_length assms by blast

lemma update_lookup_preserves_length:
  shows "length (update_lookup t l eq) = length t"
  by (cases eq) auto

lemma add_edge_same_eq_classes_invar_invar:  
  assumes  "pf_l_same_eq_classes pf l" "ufa_invar pf" "ufa_invar l"
    "a < length l" "b < length l"
    "rep_of l a \<noteq> rep_of l b" "length pf = length l"
  shows "pf_l_same_eq_classes (add_edge pf a b) (ufa_union l a b)"
proof(standard, standard, standard, standard)
  fix i j 
  assume i_j: "i < length (add_edge pf a b)" "j < length (add_edge pf a b)"
  from assms have "add_edge_dom (pf, a, b)" 
    using add_edge_domain by auto
  then have "length (add_edge pf a b) = length pf" 
    by (simp add: add_edge_preserves_length)
  then show "(rep_of (ufa_union l a b) i = rep_of (ufa_union l a b) j) =
           (rep_of (add_edge pf a b) i = rep_of (add_edge pf a b) j)" 
    using assms i_j rep_of_add_edge_aux ufa_union_aux by auto
qed

subsection \<open>Additional helper lemmata\<close>

lemma update_lookup_unchanged:
  assumes "rep_of l c\<^sub>1 \<noteq> a' \<or> rep_of l c\<^sub>2 \<noteq> b'"
    shows "update_lookup t l (F c\<^sub>1 c\<^sub>2 \<approx> c) ! a' ! b' = t ! a' ! b'"
  using assms unfolding update_lookup.simps 
  by (metis nth_list_update_eq nth_list_update_neq nth_update_invalid)


lemma update_lookup_unchanged':
  assumes "\<not> lookup_Some t l (F d\<^sub>1 d\<^sub>2 \<approx> d)"
      and "lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba)"
    shows "lookup_entry (update_lookup t l (F d\<^sub>1 d\<^sub>2 \<approx> d)) l c\<^sub>1 c\<^sub>2 = lookup_entry t l c\<^sub>1 c\<^sub>2"
proof(cases "rep_of l c\<^sub>1 = rep_of l d\<^sub>1 \<and> rep_of l c\<^sub>2 = rep_of l d\<^sub>2")
  case False
  with assms show ?thesis
    using update_lookup_unchanged by metis
qed (use assms in simp)

lemma lookup_step_unchanged_step:
  assumes "ufa_invar l" "a < length l" "b < length l"
      and "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    shows "(lookup (propagate_step l u t pe pf pfl ip a b eq)) ! a' ! b' = t ! a' ! b'"
  using assms
proof(induction rule: propagate_step_induct)
  case base
  then show ?case 
    by simp
next
  case (update_pending l u t pe pf pfl ip u1)
  then show ?case 
    by auto
next
  case (update_lookup l u t pe pf pfl ip u1 rep_b)
  then show ?case proof(cases u1)
    case (Constants x11 x12)
    then show ?thesis 
      using update_lookup.IH update_lookup.prems by auto
  next
    case (Function x21 x22 x23)
    then show ?thesis 
      by (metis congruence_closure.select_convs(3) is_none_code(2) lookup_Some.simps(1) update_lookup.IH update_lookup.hyps(1) update_lookup.prems update_lookup_unchanged)
  qed
qed

lemma use_list_invar_function: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l" "j < length (u ! i)" "l ! i = i"
  obtains a\<^sub>1 a\<^sub>2 a where "(u ! i) ! j = (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  using assms unfolding use_list_invar_def by fastforce

lemma use_list_invar_less_n: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe,  proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l" "j < length (u ! i)" "l ! i = i" "(u ! i) ! j = (F a b \<approx> c)"
  shows "a < length l" "b < length l" "c < length l"
  using assms unfolding use_list_invar_def by fastforce+

lemma use_list_invar_less_n_in_set: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe,  proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l" "(F a b \<approx> c) \<in> set (u ! i)" "l ! i = i"
  shows "a < length l" "b < length l" "c < length l"
  using assms use_list_invar_less_n by (metis in_set_conv_nth)+

lemma use_list_invar_less_n_in_set': 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe,  proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l" "i < length l" "eq \<in> set (u ! rep_of l i)" 
  obtains a\<^sub>1 a\<^sub>2 a where "eq = (F a\<^sub>1 a\<^sub>2 \<approx> a)" "a\<^sub>1 < length l" "a\<^sub>2 < length l" "a < length l"
proof-
  have "rep_of l i < length l" "l ! rep_of l i = rep_of l i"
     apply (simp add: assms(2) assms(3) rep_of_bound)
    by (simp add: assms(2) assms(3) rep_of_root)
  with assms that show ?thesis unfolding use_list_invar_def
    by (metis congruence_closure.select_convs(1,2) in_set_conv_nth)
qed

lemma use_list_invar_rep_eq_i: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l"  "l ! i = i" "(F a b \<approx> c) \<in> set (u ! i)"
  shows "rep_of l a = i \<or> rep_of l b = i"
proof-
  from assms(4) obtain j where "j < length (u ! i)" "u ! i ! j = (F a b \<approx> c)"
    by (metis in_set_conv_nth)
  with assms show ?thesis unfolding use_list_invar_def by fastforce
qed

lemma lookup_invar_less_n:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "(t ! i) ! j = Some (F f g \<approx> h)" "i < length l" "j < length l" "l ! i = i" "l ! j = j"
  shows "f < length l" "g < length l" "h < length l"
  using assms unfolding lookup_invar_def by fastforce+

lemma lookup_invar_valid:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "(t ! i) ! j = Some (F f g \<approx> h)" "i < length l" "j < length l" "l ! i = i" "l ! j = j"
  shows "i = rep_of l f" "j = rep_of l g" 
  using assms unfolding lookup_invar_def by fastforce+

lemma longest_common_prefix_concat: 
  "longest_common_prefix (a @ b) (a @ c) = a @ longest_common_prefix b c"
proof(induction "(a @ b)" "(a @ c)" arbitrary: a b rule: longest_common_prefix.induct)
  case (1 x xs y ys)
  then show ?case 
    apply(cases a)
    by auto
qed auto

lemma lowest_common_ancestor_fun_upd:
  assumes "ufa_invar l" "x < length l" "y < length l"
    "l ! a = a" "rep_of l a \<noteq> rep_of l b" "rep_of l x = rep_of l y"
    "a < length l" "b < length l"
  shows "lowest_common_ancestor l x y = lowest_common_ancestor (l[a := b]) x y"
proof-
  have a_root: "a = rep_of l a" 
    by (simp add: assms rep_of_refl)
  then show ?thesis
  proof(cases "rep_of l x = rep_of l a")
    case True
    then have *: "path_to_rep (l[a := b]) x = path_to_rep l b @ path_to_rep l x"
      "path_to_rep (l[a := b]) y = path_to_rep l b @ path_to_rep l y"
      using a_root assms path_to_rep_fun_upd_root 
      by metis+
    then have *: "longest_common_prefix (path_to_rep (l[a := b]) x) (path_to_rep (l[a := b]) y)
= path_to_rep l b @
longest_common_prefix (path_to_rep l x) (path_to_rep l y)" unfolding * 
      by (simp add: longest_common_prefix_concat)
    have "hd (path_to_rep l x) = rep_of l x" "hd (path_to_rep l y) = rep_of l y"
      using assms path_hd path_path_to_rep by blast+
    with assms have "(path_to_rep l x) = [rep_of l x]@tl(path_to_rep l x)"
      "(path_to_rep l y) = [rep_of l y]@tl(path_to_rep l y)"
      by (metis Cons_eq_appendI  empty_append_eq_id len_greater_imp_nonempty list.collapse path_to_rep_length)+
    then have "longest_common_prefix (path_to_rep l x) (path_to_rep l y) = 
[rep_of l x] @ longest_common_prefix (tl(path_to_rep l x)) (tl(path_to_rep l y)) "
      using longest_common_prefix_concat by (metis assms(6))
    then have "longest_common_prefix (path_to_rep l x) (path_to_rep l y) \<noteq> []"
      by simp
    then show ?thesis 
      using * by fastforce
  next
    case False
    then have "path_to_rep (l[a := b]) x = path_to_rep l x"
      "path_to_rep (l[a := b]) y = path_to_rep l y" 
      by (auto simp add: assms path_to_rep_fun_upd' ufa_invar_fun_upd')
    then show ?thesis 
      by fastforce
  qed
qed

end