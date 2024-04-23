theory Test
  imports "Refine_Monadic.Refine_Monadic" "HOL-Library.Mapping"
begin

definition "lookup (m :: 'a \<rightharpoonup> 'b) x = RETURN (m x)"

definition "lookup_impl m x = RETURN (Mapping.lookup m x)"

term pcr_mapping
find_theorems name: mapping
find_theorems "_ _ Mapping.lookup"

term p2rel
term relAPP
find_consts "(('a \<rightharpoonup> 'b) \<times> ('a, 'b) mapping) set"
term "\<lambda> m m'. p2rel (pcr_mapping (rel2p K) (rel2p V)) m' m"

lemma test:
  assumes "(m, m') \<in> p2rel (\<lambda>m m'. cr_mapping m' m)" 
  assumes "(v, v') \<in> Id"
  shows "lookup_impl m v \<le> \<Down>(\<langle>Id\<rangle> option_rel) (lookup m' v')"
  using assms
  unfolding lookup_def lookup_impl_def
  apply(refine_vcg)
  apply (auto simp: cr_mapping_def  lookup.rep_eq dest!: p2relD)
  done

export_code lookup checking SML_imp

end