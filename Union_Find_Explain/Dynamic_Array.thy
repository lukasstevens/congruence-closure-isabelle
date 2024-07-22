theory Dynamic_Array
  imports "Separation_Logic_Imperative_HOL.Sep_Main"
    "HOL-Library.Code_Target_Nat" "HOL-Library.Code_Target_Int"
begin

datatype 'a dyn_array = Dyn_Array (len: nat) (array: "'a array")

fun is_dyn_array_raw :: "'a::heap list \<times> nat \<Rightarrow> 'a dyn_array \<Rightarrow> assn" where
  "is_dyn_array_raw (xs, n) (Dyn_Array m a) = (a \<mapsto>\<^sub>a xs * \<up>(m = n) * \<up>(n \<le> length xs))"
declare is_dyn_array_raw.simps[simp del]

context
begin

qualified definition new :: "'a \<Rightarrow> 'a::heap dyn_array Heap" where
  "new d \<equiv> do {
    p \<leftarrow> Array.new 5 d; 
    return (Dyn_Array 0 p)
  }"

qualified definition capacity :: "'a::heap dyn_array \<Rightarrow> nat Heap" where
  "capacity da \<equiv> Array.len (array da)"

qualified definition length :: "'a::heap dyn_array \<Rightarrow> nat Heap" where
  "length da = return (len da)"

lemma capacity_raw_rule[sep_heap_rules]:
  "<is_dyn_array_raw (xs, n) da> capacity da
    <\<lambda>r. is_dyn_array_raw (xs, n) da * \<up>(r = List.length xs)>"
  unfolding capacity_def
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps)

lemma length_raw_rule[sep_heap_rules]:
  "<is_dyn_array_raw (xs, n) da> length da
    <\<lambda>r. is_dyn_array_raw (xs, n) da * \<up>(r = n)>"
  unfolding length_def
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps)

qualified definition reserve :: "'a::heap dyn_array \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a dyn_array Heap" where
  "reserve da def newc \<equiv> do {
    c \<leftarrow> capacity da;
    if newc \<le> c then return da
    else do {
      len \<leftarrow> length da;
      xs \<leftarrow> Array.freeze (array da);
      a' \<leftarrow> Array.of_list (xs @ replicate (newc - c) def);
      return (Dyn_Array len a')
    }
  }"

lemma freeze_rule[sep_heap_rules]:
  "<is_dyn_array_raw (xs, n) da > Array.freeze (array da)
    <\<lambda>r. is_dyn_array_raw (xs, n) da * \<up>(r = xs)>"
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps)

lemma reserve_raw_rule_if_leq_length:
  assumes "c \<le> List.length xs"
  shows "<is_dyn_array_raw (xs, n) da> reserve da def c
    <\<lambda>r. is_dyn_array_raw (xs, n) da * \<up>(r = da)>"
  using assms unfolding reserve_def
  by sep_auto

lemma reserve_raw_rule_if_gt_length:
  assumes "c > List.length xs"
  shows "<is_dyn_array_raw (xs, n) da> reserve da def c
    <\<lambda>r. is_dyn_array_raw (xs, n) da *
      is_dyn_array_raw (xs @ replicate (c - List.length xs) def, n) r>"
  using assms unfolding reserve_def
  apply (sep_auto)
   apply(cases da; sep_auto simp: is_dyn_array_raw.simps)
  done

lemma reserve_raw_rule:
  "<is_dyn_array_raw (xs, n) da> reserve da def c
    <is_dyn_array_raw (xs @ replicate (c - List.length xs) def, n)>\<^sub>t"
  apply(cases "c \<le> List.length xs")
  subgoal
    supply reserve_raw_rule_if_leq_length[sep_heap_rules]
    by sep_auto
  subgoal
    supply reserve_raw_rule_if_gt_length[sep_heap_rules]
    by sep_auto
  done


qualified definition nth :: "'a::heap dyn_array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "nth da n \<equiv> Array.nth (array da) n"

lemma nth_raw_rule[sep_heap_rules]:
  assumes "i < n"
  shows "<is_dyn_array_raw (xs, n) da> nth da i <\<lambda>r. is_dyn_array_raw (xs, n) da * \<up>(r = xs ! i)>"
  using assms
  unfolding nth_def 
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps)

qualified definition push' :: "'a::heap dyn_array \<Rightarrow> 'a \<Rightarrow> 'a dyn_array Heap" where
  "push' da x \<equiv> do {
    a' \<leftarrow> Array.upd (len da) x (array da);
    return (Dyn_Array (Suc (len da)) a')
   }"

qualified definition push :: "'a::heap dyn_array \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a dyn_array Heap" where
  "push da def x \<equiv> do {
    c \<leftarrow> capacity da;
    len \<leftarrow> length da;
    da' \<leftarrow> (if len \<ge> c then reserve da def (2 * c + 1) else return da);
    push' da' x
  }"

lemma push'_raw_rule[sep_heap_rules]:
  assumes "n < List.length xs"
  shows "<is_dyn_array_raw (xs, n) da> push' da x
    <is_dyn_array_raw (xs[n := x], Suc n)>"
  using assms unfolding push'_def
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps)

lemma push_raw_rule_if_lt_length:
  assumes "n < List.length xs"
  shows "<is_dyn_array_raw (xs, n) da> push da def x
    <is_dyn_array_raw (list_update xs n x, Suc n)>"
  using assms unfolding push_def by sep_auto

lemma push_raw_rule_if_eq_length:
  notes reserve_raw_rule_if_gt_length[sep_heap_rules]
  assumes "n = List.length xs"
  shows "<is_dyn_array_raw (xs, n) da> push da def x
    <\<lambda>r. is_dyn_array_raw (xs, n) da *
      is_dyn_array_raw (xs @ x # replicate (List.length xs) def, Suc n) r>"
  using assms unfolding push_def
  by sep_auto


definition "is_dyn_array xs da \<equiv> case da of Dyn_Array m a \<Rightarrow>
   (\<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(xs = take m xs') * \<up>(m \<le> List.length xs'))"

lemma is_dyn_array_raw_entails_len_eq:
  "is_dyn_array_raw (xs, n) da \<Longrightarrow>\<^sub>A \<up>(len da = n) * is_dyn_array_raw (xs, n) da"
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps)

lemma is_dyn_array_raw_entails_is_dyn_array:
  "is_dyn_array_raw (xs, n) da \<Longrightarrow>\<^sub>A is_dyn_array (take n xs) da"
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps is_dyn_array_def)

lemma is_dyn_array_entails_is_dyn_array_raw:
  "is_dyn_array xs da \<Longrightarrow>\<^sub>A
    (\<exists>\<^sub>Axs' n. is_dyn_array_raw (xs', n) da * \<up>(xs = take n xs') * \<up>(n \<le> List.length xs'))"
  by (cases da) (sep_auto simp: is_dyn_array_raw.simps is_dyn_array_def)

lemma is_dyn_array_def':
  "is_dyn_array xs da =
    (\<exists>\<^sub>Axs' n. is_dyn_array_raw (xs', n) da * \<up>(xs = take n xs') * \<up>(n \<le> List.length xs'))"
  using is_dyn_array_raw_entails_is_dyn_array is_dyn_array_entails_is_dyn_array_raw
  using ent_pure_pre_iff by (intro ent_iffI ent_ex_preI) blast+

lemma new_rule[sep_heap_rules]:
  "<emp> new d <is_dyn_array []>"
  unfolding new_def is_dyn_array_def by sep_auto

lemma length_rule[sep_heap_rules]:
  "<is_dyn_array xs da> length da <\<lambda>r. is_dyn_array xs da * \<up>(r = List.length xs)>"
  unfolding is_dyn_array_def'
  by sep_auto

lemma reserve_rule[sep_heap_rules]:
  notes reserve_raw_rule[sep_heap_rules]
  shows "<is_dyn_array xs da> reserve da def c <is_dyn_array xs>\<^sub>t"
  unfolding is_dyn_array_def' by sep_auto

lemma nth_rule[sep_heap_rules]:
  assumes "i < List.length xs"
  shows "<is_dyn_array xs da> nth da i <\<lambda>r. is_dyn_array xs da * \<up>(r = xs ! i)>"
  using assms unfolding is_dyn_array_def'
  by sep_auto

lemma push_rule[sep_heap_rules]:
  "<is_dyn_array xs da> push da def x <is_dyn_array (xs @ [x])>\<^sub>t"
  unfolding is_dyn_array_def'
  apply(vcg)
  subgoal for xs' n
    apply(cases "n < List.length xs'")
    subgoal supply push_raw_rule_if_lt_length[sep_heap_rules]
      by (sep_auto simp: take_update_last)
    subgoal supply push_raw_rule_if_eq_length[sep_heap_rules]
      by sep_auto
    done
  done

end

end