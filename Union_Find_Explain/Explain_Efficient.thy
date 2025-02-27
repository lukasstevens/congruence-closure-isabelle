theory Explain_Efficient
  imports 
    "HOL-Library.Sublist"
    "HOL-Library.Option_ord"
    "UFA_Forest"
    "UFA_LCA"
    "Equality_Proof"
begin

abbreviation "ufe_lca ufe \<equiv> ufa_lca (uf_ds ufe)"
abbreviation "ufe_forest_of ufe \<equiv> ufa_forest_of (uf_ds ufe)"

context
  fixes ufe :: ufe
begin

function (domintros) find_newest_on_path :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_newest_on_path y x =
    (if y = x then None
    else max (au_ds ufe x) (find_newest_on_path y (ufe_parent_of ufe x)))"
  by pat_completeness auto

lemma find_newest_on_path_if_eq[simp]:
  "find_newest_on_path x x = None"
  by (meson find_newest_on_path.domintros find_newest_on_path.psimps)

function (domintros) explain' :: "nat \<Rightarrow> nat \<Rightarrow> nat eq_prf" where
  "explain' x y =
    (if x = y then ReflP x
    else 
      let
        lca = ufe_lca ufe x y;
        newest_x = find_newest_on_path lca x;
        newest_y = find_newest_on_path lca y
      in
        if newest_x \<ge> newest_y then
          let (ax, bx) = unions ufe ! the newest_x
          in TransP
            (TransP (explain' x ax) (AssmP (the newest_x)))
            (explain' bx y)
        else
          let (ay, by) = unions ufe ! the newest_y
          in TransP
            (TransP (explain' x by) (SymP (AssmP (the newest_y))))
            (explain' ay y))"
  by pat_completeness auto

lemma explain'_refl[simp]:
  "explain' x x = ReflP x"
  using explain'.domintros explain'.psimps by fastforce

end

end