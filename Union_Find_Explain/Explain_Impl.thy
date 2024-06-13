theory Explain_Impl
  imports Explain_Correctness Union_Find_Rank_Int
begin

record ufe_ds_impl =
  uf_ds :: ufri
  au_ds :: "nat \<rightharpoonup> nat"
  unions :: "(nat \<times> nat) list"

context
  includes ufa.lifting ufr.lifting
begin

lift_definition ufe_union_impl :: "(ufr \<times> (nat \<rightharpoonup> nat) \<times> (nat \<times> nat) list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ufe_ds_impl" is
  "\<lambda>((ufa, r), au, us). undefined" .


end