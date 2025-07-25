theory Document
  imports Main "Union_Find_Explain.Explain_Imp" LaTeXsugar 
begin

text_raw \<open>
\renewcommand{\isakeyword}[1]{\ensuremath{\mathsf{#1}}}
\renewcommand{\isacommand}[1]{\isakeywordONE{#1}}
%\renewcommand{\isakeywordONE}[1]{\isakeyword{\color[RGB]{0,102,153}#1}}
%\renewcommand{\isakeywordTWO}[1]{\isakeyword{\color[RGB]{0,153,102}#1}}
%\renewcommand{\isakeywordTHREE}[1]{\isakeyword{\color[RGB]{0,153,255}#1}}
\renewcommand{\isaconst}[1]{\ensuremath{\mathsf{#1}}}
\newlength{\funheadersep}
\setlength{\funheadersep}{2pt}
\setenumerate[0]{label=(\arabic*)}
\newcommand{\Cpp}[0]{C\texttt{++}}
\newcommand{\Gpp}[0]{g\texttt{++}}
\<close>

(*<*)
declare [[show_question_marks=false]] 

notation (latex output) TransP (infixl "\<^latex>\<open>\\ensuremath{\\bigtriangledown}\<close>" 70)

syntax (output)
  "_with_proj" :: "'a pair_pre_digraph \<Rightarrow> ('a, 'a) pre_digraph"
translations
  "_with_proj" <= "CONST with_proj"
  "g" <= "_with_proj g"

syntax (latex output)
  "_proves_eq_mf" :: "('a \<times> 'a) list \<Rightarrow> 'a eq_prf \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" ("(_ \<turnstile>\<^sub>= _ : _)")
translations
  "_proves_eq_mf as p a" <= "CONST proves_eq as p a"

notation (latex output) proves_eq ("\<turnstile>\<^sub>=")

syntax (latex output)
  "pverts" :: "ident" ("verts")
  "parcs" :: "ident" ("arcs")

abbreviation (reachable_from output) "reachable_from y x G \<equiv> reachable G x y"

notation (latex output)
  reachable_from  (\<open>_/ \<^latex>\<open>{\normalsize \,\<close>is reachable from\<^latex>\<open>\,}\<close>/ _ \<^latex>\<open>{\normalsize \,\<close>in\<^latex>\<open>\,}\<close>/ _\<close>)

no_notation induce_subgraph (infix \<open>\<restriction>\<close> 67)

abbreviation find_newest_on_path_ufe_lca_left ("'(_ \<upharpoonleft> _')\<^bsub>_\<^esub>") where
  "find_newest_on_path_ufe_lca_left x y ufe \<equiv> find_newest_on_path ufe (ufe_lca ufe x y) x"

abbreviation find_newest_on_path_ufe_lca_right ("'(_ \<restriction> _')\<^bsub>_\<^esub>") where
  "find_newest_on_path_ufe_lca_right x y ufe \<equiv> find_newest_on_path ufe (ufe_lca ufe x y) y"

notation (latex output) Relation.Image (infixr "(``\<^latex>\<open>\\:\<close>)" 90)

translations
  "CONST Id" <= "CONST nat_rel"

(*>*)

text \<open>\maketitle\<close>

text \<open>
\begin{abstract}
Using Isabelle/HOL, we verify a union-find data structure with an explain operation due to @{cite \<open>congcl_proofs using citeauthor\<close>}.
We devise a simpler, more naive version of the explain operation whose soundness and completeness is easy to verify.
Then, we prove the original formulation of the explain operation to be equal to our version.
Finally, we refine this data structure to Imperative HOL, enabling us to export efficient imperative code.
The formalisation provides a stepping stone towards the verification of proof-producing congruence closure algorithms which are a core ingredient of \acrfull{smt} solvers.

\keywords{Equivalence closure \and Interactive theorem proving \and Satisfiability modulo theories \and Proof-producing decision procedure}
\end{abstract}
\<close>

text \<open>
%\todo[inline]{Move question marks to ROOT}
%\todo[inline]{Rename au\_ds to au and uf\_ds to uf?}
%\todo[inline]{Use cref when sensible (e.g.\ when referring to current section)}
%\todo[inline]{Think about @{const defeq} vs @{const Pure.eq}}
\<close>

section \<open>Introduction\<close>

text \<open>
The \acrfull{uf} data structure maintains the equivalence closure of a relation,
which is given as a sequence of pairs or, in terms of the \acrshort{uf} data structure, \opunion{} operations.
It is fundamental to efficiently implement well-known graph algorithms such as @{cite \<open>mst using citeauthor\<close>}'s~@{cite \<open>mst\<close>} minimum spanning-tree algorithm. 
There, it tracks which vertices belong to the same connected component and are, in that sense, equivalent.
Beyond graph algorithms, its applicability extends to the domain of theorem proving as it routinely forms the basis of congruence closure algorithms, which are widely used by \acrfull{smt} solvers.
To increase their trustworthiness, current \acrshort{smt} solvers such as
cvc5~@{cite \<open>cvc5\<close>}, E~@{cite \<open>eprover\<close>}, Vampire~@{cite \<open>vampire\<close>}, veriT~@{cite \<open>verit\<close>}, and Z3~@{cite \<open>z3_proofs\<close>}
can output detailed proofs when they determine an input formula to be unsatisfiable.
To produce these proofs, it is crucial to have congruence closure algorithms that efficiently explain why they consider two terms to be equal.
The first such algorithm was presented by @{cite \<open>congcl_proofs using citeauthor\<close>}~@{cite \<open>congcl_proofs and congcl_fast_extensions\<close>}, 
who extended the \acrshort{uf} data structure with an \opexplain{} operation to obtain a \acrfull{ufe} data structure.
Verifying this data structure in Isabelle/HOL is the focus of our paper.

Why, then, should we verify a data structure that already produces proofs?
Our answer is three-fold.
\begin{enumerate*}[label=(\arabic*)]
\item While the data structure's proofs guarantee soundness, we also prove its completeness.
\item Executing code exported from Isabelle depends on a substantial \acrfull{tcb}, including the target language's compiler and runtime.
\item Whereas \acrshort{smt} solvers typically operate with a large \acrshort{tcb},
adding to the \acrshort{tcb} of interactive theorem provers is usually discouraged.
Proof-producing algorithms --- such as those introduced in earlier work by the first author~@{cite \<open>orders\<close>} --- enable integration without increasing the \acrshort{tcb}.
\end{enumerate*}
\<close>

subsection \<open>Contributions\<close>
text \<open>
We present, to our knowledge, the first formalisation of the \acrshort{ufe} data structure as introduced by @{cite \<open>congcl_proofs using citeauthor\<close>}.
In their work, they present two variants of this data structure.
Here, we only formalise the first variant, leaving the other for future work.
We devise a simpler, more naive version of the \opexplain{} operation, for which soundness and completeness is easier to prove. 
Then, we prove the original version of the \opexplain{} operation to be extensionally equal to the simple one.
Based on an existing formalisation of the \acrshort{uf} data structure by @{cite \<open>uf_isabelle using citeauthor\<close>}~@{cite \<open>uf_isabelle\<close>},
we develop a more abstract formalisation of the data structure, hiding implementation details. 
Finally, we refine the \acrshort{ufe} data structure to Imperative HOL~@{cite \<open>imperative_hol\<close>} using @{cite \<open>uf_isabelle using citeauthor\<close>}'s~@{cite \<open>uf_isabelle\<close>} separation logic framework,
enabling generation of efficient imperative code.

The formalisation is available online.\footnote{\<^url>\<open>https://doi.org/10.5281/zenodo.15557955\<close>}
Since everything is verified, we omit proofs and focus on outlining the structure of the formalisation.
\<close>

subsection \<open>Related Work\<close>
text \<open>
Efficient implementations of the \acrshort{uf} data structure have been known for a long time.
In particular, @{cite \<open>uf_by_size using citeauthor\<close>}~@{cite \<open>uf_by_size\<close>} represent the data structure as a forest of rooted trees
and propose the union-by-size heuristic,
which gives $\mathcal{O}(\log n)$ running time for \opunion{} and \opfind{} for a data struture over $n$ elements.
Another heuristic, called path compression, was presented by @{cite \<open>uf_compress using citeauthor\<close>}~@{cite \<open>uf_compress\<close>}.
Analysing the complexity of the data structure when combining both heuristics turned out to be challenging,
but @{cite \<open>uf_ub using citeauthor\<close>}~@{cite \<open>uf_ub\<close>} and @{cite \<open>uf_ub_improved using citeauthor\<close>}~@{cite \<open>uf_ub_improved\<close>}
eventually proved an amortised running time of $\mathcal{O}(n + m\, \alpha(m + n, n))$
for a sequence of at most $n - 1$ \opunion{} and $m$ \opfind{} operations where $\alpha$ is the inverse Ackermann function. 
This means that any one operation runs in almost constant time, amortised.

While the paper on the \acrshort{ufe} data structure~@{cite \<open>congcl_proofs\<close>} is widely cited,
there is limited follow-up literature on this data structure.
It does, however, form the basis of proof-producing congruence closure algorithms, which are crucial in the field of \acrshort{smt} solving.
There, they remain an active area of research;
for example, when we are interested in efficiently finding small proofs~@{cite \<open>congcl_small_proofs\<close>}.

The literature of verified algorithms and data structures is vast so we refer to a survey~@{cite \<open>algorithms_survey\<close>} for an overview.
Focusing on the \acrshort{uf} data structure, there is a formalisation in Coq~@{cite \<open>uf_coq\<close>}, where
the amortised complexity is analysed by @{cite \<open>uf_coq_time using citeauthor\<close>}~@{cite \<open>uf_coq_time\<close>} in a separation logic with time credits.
Similarly, in Isabelle, there is a formalisation of the data structure~@{cite \<open>uf_isabelle\<close>}
that was later extended with a complexity analysis by @{cite \<open>uf_isabelle_time using citeauthor\<close>}~@{cite \<open>uf_isabelle_time\<close>}.
More recently, there is formalisation by @{cite \<open>uf_isabelle_algebraic using citeauthor\<close>}~@{cite \<open>uf_isabelle_algebraic\<close>} taking a relation-algebraic view.
\<close>

subsection \<open>Notation\<close>
text \<open>
Isabelle/HOL~@{cite \<open>isabelle\<close>} conforms to everyday mathematical notation for the most part.
We establish notation and in particular some essential data types together with their primitive operations that are specific to Isabelle/HOL.

We write @{term_type \<open>t :: 'a\<close>} to specify that the term @{term t} has the type @{typ \<open>'a\<close>} and @{typ \<open>'a \<Rightarrow> 'b\<close>} for the space of total functions from type @{typ 'a} to type @{typ 'b}.

Sets with elements of type @{typ 'a} have the type @{typ \<open>'a set\<close>}.
The cardinality of a set @{term \<open>A :: 'a set\<close>} is denoted by @{term \<open>card (A :: 'a set)\<close>}.

We use @{typ \<open>'a list\<close>} to describe the type of lists, which are constructed using the empty list @{const Nil}
or the infix cons constructor @{const \<open>Cons\<close>},
and are appended with the infix operator @{const List.append}.
The length of list @{term xs} is denote by @{term \<open>length xs\<close>}.
The function @{const List.set} converts a list into a set.
We write @{term \<open>(xs :: 'a list) ! i\<close>} to access the @{term \<open>i :: nat\<close>}-th element of the list @{term \<open>xs :: 'a list\<close>}.

To represent partial values of type @{typ 'a}, we use the type @{typ \<open>'a option\<close>} with the constructors @{const None} and @{const Some}.
We also define an order on this type by letting @{const None} be smaller than @{const Some}
and lifting the order on the underlying type @{typ 'a},
i.e.\ we have that @{lemma \<open>Some x \<le> Some y \<longleftrightarrow> x \<le> y\<close> by simp}.

Relations are denoted with the type synonym @{typ \<open>'a rel\<close>}, which expands to @{typ \<open>('a \<times> 'a) set\<close>}.
For a relation @{term \<open>r :: 'a rel\<close>}, @{term \<open>Field r\<close>} are those elements that occur as a component of a pair @{term \<open>p \<in> (r :: 'a rel)\<close>}.
Furthermore, we use @{term \<open>r\<inverse>\<close>} to denote the inverse and @{term \<open>r\<^sup>*\<close>} to denote the reflexive transitive closure of @{term \<open>r :: 'a rel\<close>}.

Throughout our formalisation we employ \<^emph>\<open>locales\<close>~@{cite \<open>locales\<close>},
which are named contexts of types, constants and assumptions about them.
\<close>

section \<open>Basic Union-Find\<close>
subsection \<open>Background\label{sec:uf_background}\<close>
text \<open>
Given a set of $n$ elements $A = \{a_1, \ldots, a_n\}$, the \acrshort{uf} data structure keeps track of a partition of $A$ into disjoint sets $A_1, \ldots, A_k$, i.e.\ $A = A_1 \uplus \cdots \uplus A_k$.
Equivalently, one can view the partition as a partial equivalence relation with the equivalence classes $A_1, \ldots, A_k$.
The equivalence relation is partial because @{term_type \<open>A :: 'a set\<close>} might only be a subset of the type @{typ 'a}.
We initialise the data structure by partitioning $A$ into singleton sets of elements,
so we have that $A = \{a_1\} \uplus \cdots \uplus \{a_n\}$.
Those sets are merged by subsequent \opunion{} operations where $\opunion{}~a_i~a_j$ merges the set containing $a_i$ with the one that contains $a_j$.
Each set in the partition contains one particular element that serves as its representative.
We will denote the representative of an element @{term \<open>a :: nat\<close>}
in the \acrshort{uf} data structure @{term \<open>uf :: nat list\<close>}
as @{term \<open>rep_of uf a\<close>}.
Accordingly, two elements have the same representative exactly when they belong to the same set in the partition.
For any element @{term \<open>a\<^sub>i :: nat\<close>}, the \opfind{} operation returns its representative @{term \<open>rep_of uf a\<^sub>i\<close>}.

The data structure can be implemented as a forest of rooted trees
where each tree encodes an equivalence class.
The edges of a tree in the forest are directed towards the root,
which is the representative of the corresponding equivalence class.
To preserve this invariant, we initialise the forest with $n$ vertices but without any edges
and, for every \opunion{} of $a_i$ and $a_j$,
we add a directed edge from @{term \<open>rep_of uf a\<^sub>i\<close>} to @{term \<open>rep_of uf a\<^sub>j\<close>} to the forest.

We encode such a forest as a list @{term \<open>l :: nat list\<close>} of length @{term n},
where at each index @{term i} of @{term l}, we save the index of the parent of the element @{term a\<^sub>i}, denoted by @{term \<open>l ! i\<close>}.
If @{term a\<^sub>i} is a root, then the list stores @{term i} itself at index @{term i},
i.e. @{term \<open>l ! i = i\<close>}.
\<close>

subsection \<open>In Isabelle/HOL\label{sec:uf_hol}\<close>
text \<open>
The \acrshort{uf} algorithm was formalised in Isabelle/HOL by @{cite \<open>uf_isabelle using citeauthor\<close>}~@{cite \<open>uf_isabelle\<close>}.
The code can be found in an entry~@{cite \<open>uf_isabelle_afp\<close>} of the \acrfull{afp}.\footnote{The code is in the theory file \texttt{Examples/Union\_Find.thy}.}
@{cite \<open>uf_isabelle using citeauthor\<close>} defines a function @{const rep_of},
which, as described above, follows the parent pointers until we arrive at the root,
where the parent pointer is self-referential.
\begin{flushleft}
@{fun (concl) rep_of [rep_of.psimps[where uf=l]]}
\end{flushleft}
Looking closely at this definition, we see that this function is only well-defined for some inputs @{term l} and @{term a}:
for every element @{term \<open>a < length l\<close>}, its parent must be in the list, i.e.\ we must have @{prop \<open>l ! a < length l\<close>},
and the parent pointers must be cycle-free in order for the function to terminate.
Functions in Isabelle/HOL must be total, so Isabelle introduces a constant @{const_typ rep_of_dom}
that characterises the inputs for which @{const rep_of} terminates.
Then, it adds @{prop \<open>rep_of_dom (l, a)\<close>} as a premise to the defining equation of @{term rep_of}. 
The intuition above is cast into a predicate @{const ufa_invar} that defines such well-formed lists @{term l}.
\begin{flushleft}
@{def \<open>ufa_invar\<close> [ufa_invar_def[where uf=l]]}
\end{flushleft}
Building on the formalisation,
we define the \acrfull{adt} @{typ ufa} as the set of all @{term_type \<open>l :: nat list\<close>}
that satisfy @{term \<open>ufa_invar l\<close>}.
\begin{flushleft}
@{command typedef}~@{typ ufa}~$=$~@{term \<open>{l. ufa_invar l}\<close>}.
\end{flushleft}
This introduces a new type without any predefined operations.
To equip it with functionality,
we lift the operations on the underlying list due to @{cite \<open>uf_isabelle using citeauthor\<close>}~@{cite \<open>uf_isabelle\<close>}
to the \acrshort{adt} using Isabelle's lifting infrastructure~@{cite \<open>lifting_transfer\<close>},
yielding
\begin{enumerate*}
  \item @{const_typ ufa_\<alpha>},
  \item @{const_typ ufa_rep_of},
  \item @{const_typ ufa_init}, and
  \item @{const_typ ufa_union}.
\end{enumerate*}
Their meaning is the following:
\begin{enumerate}
  \item @{term \<open>ufa_\<alpha> uf\<close>} is the partial equivalence relation represented by @{term \<open>uf\<close>},
  \item @{term \<open>ufa_rep_of uf x\<close>} is the representative of the equivalence class containing @{term x},
  \item @{term \<open>ufa_init n\<close>} initialises the data structure with @{term n} elements
    with each element being its own representative, and
  \item @{term \<open>ufa_union uf x y\<close>} returns a \acrshort{uf} data structure
    where the equivalence classes of @{term x} and @{term y} are merged.
    This is implemented by updating the underlying list at index @{term \<open>rep_of l x\<close>} to @{term \<open>rep_of l y\<close>}.
\end{enumerate}
Formally, the above operations fulfil the properties stated below:
\begin{itemize}
  \item @{thm [mode=iffSpace] (concl) ufa_rep_of_eq_iff_in_ufa_\<alpha>} if @{prop \<open>{x, y} \<subseteq> Field (ufa_\<alpha> uf)\<close>},
  \item @{thm ufa_\<alpha>_ufa_init}, and
  \item @{thm ufa_\<alpha>_ufa_union_eq_per_union_ufa_\<alpha>}
\end{itemize}
where @{term \<open>per_union R x y\<close>} is the equivalence relation
that results from merging the respective equivalence classes in the relation @{term R} that @{term x} and @{term y} belong to.

But what happens if @{term x} or @{term y} is not an element of the partial equivalence relation @{term R}?
In that case, the equivalence relation is unchanged, which means that @{prop \<open>per_union R x y = R\<close>}.
This, however, can be seen as a misuse of the \acrshort{uf} data structure,
since we initialise it with a fixed set of elements @{term A}
and expect the user to only work with these elements.
Therefore, we introduce the following definitions that characterise valid union(s) with regard to this initial set.
\begin{flushleft}
@{def valid_union} \\[0.75em]
@{def valid_unions}
\end{flushleft}
\<close>

section \<open>Simple Certifying Union-Find Algorithm\label{sec:ufe_simple}\<close>
text \<open>
Building on the \acrshort{uf} \acrshort{adt}, we now develop a simple \opexplain{} operation that,
for a given list of equations @{term_type \<open>us :: ('a \<times> 'a) list\<close>}, takes two elements @{term \<open>x\<close>} and @{term \<open>y\<close>}
and produces a certificate that @{term \<open>x = y\<close>} modulo @{term \<open>us\<close>}.
The certificate is given in terms of a data type @{type \<open>eq_prf\<close>}
with its corresponding system @{const proves_eq} of inference rules as seen in \cref{fig:eq_prf}.
As expected, we have inference rules that utilise the reflexivity, symmetry, and transitivity of equality as well as an assumption rule.
To improve readability, we use the infix operator $\bigtriangledown$ to denote the proof term for transitivity.
\begin{figure}[b]
  \begin{gather*}
    \inferrule{@{thm (prem 1) Equality_Proof.assm[of _ us]} \\
       @{thm (prem 2) Equality_Proof.assm[of _ us]}}{@{thm (concl) Equality_Proof.assm[of _ us]}} \qquad
    @{thm [mode=Axiom] Equality_Proof.refl[of us]} \\
    @{thm [mode=Rule] Equality_Proof.sym[of us]} \qquad
    \inferrule{@{thm (prem 1) Equality_Proof.trans[of us p\<^sub>1 _ _ p\<^sub>2]} \\
       @{thm (prem 2) Equality_Proof.trans[of us p\<^sub>1 _ _ p\<^sub>2]}}{@{thm (concl) Equality_Proof.trans[of us p\<^sub>1 _ _ p\<^sub>2]}}
  \end{gather*}
  \caption{%
    The system of inference rules @{const proves_eq} on the data type @{type eq_prf} of proofs.\label{fig:eq_prf}
    We write @{term \<open>us \<turnstile>\<^sub>= p : (x, y)\<close>} to say that @{term p} proves @{term \<open>x = y\<close>} assuming the equalities @{term us}.
  }
\end{figure}

We prove that @{const proves_eq} is sound and complete with respect to the equivalence relation induced by @{term \<open>us\<close>},
i.e.\ the equivalence closure of @{term \<open>us\<close>}.
In Isabelle, we define
\begin{flushleft}
\begin{minipage}{0.485\linewidth}
@{def [names_short] Equality_Proof.symcl :: \<open>'a rel \<Rightarrow> 'a rel\<close>}
\end{minipage}
\hfill
\begin{minipage}{0.485\linewidth}
@{def [names_short] equivcl :: \<open>'a rel \<Rightarrow> 'a rel\<close>}
\end{minipage}
\end{flushleft}
and prove the theorem below.
\begin{theorem}[Soundness and Completeness of @{const proves_eq}]
@{thm [mode=IfThen] proves_eq_sound[of us]}
Conversely, @{thm [mode=IfThen] proves_eq_complete[of _ _ us]}
\end{theorem}

Our goal is to implement the \opexplain{} operation using a \acrshort{uf} data structure,
so we fix an initial \acrshort{uf} data structure @{term uf}.
For a list of equations @{term \<open>us\<close>} or, in terms of the \acrshort{uf} data structure, \opunion{} operations,
the current state of the \acrshort{uf} data structure is then equal to @{term \<open>ufa_unions uf us\<close>}
where we define
\begin{flushleft}
@{def ufa_unions}.
\end{flushleft}
Here, we require the unions @{term us} to be valid unions with respect to @{term uf}.
Moreover, it must hold that @{prop \<open>ufa_\<alpha> uf \<subseteq> Id\<close>}
because the only way to justify an equality from an empty list of equations using @{const proves_eq} is by reflexivity.
Finally, we also constrain @{term us} to be \<^emph>\<open>effective\<close> unions
meaning that no union shall be redundant with respect to the unions preceeding it.
Note that redundant unions have no effect on the state of the \acrshort{uf} data structure anyways
so there is no need to record them.
We formalise effectiveness with the following definitions.
\begin{flushleft}
@{def eff_union} \\[0.75em]
@{fun [mode=iffSpace] eff_unions}
\end{flushleft}
Similarly to @{typ ufa}, we encapsulate pairs @{term \<open>(uf, us)\<close>}
that are well-formed with respect to the constraints above by an \acrshort{adt} @{typ ufe}.
We choose this simple representation of the \acrshort{ufe} data structure to ease formal reasoning,
while a more efficient implementation is described in \cref{sec:imperative_hol}.

\begin{flushleft}
@{command typedef}~@{typ ufe}~$=$~@{term \<open>{(uf, us). ufa_\<alpha> uf \<subseteq> Id \<and> eff_unions uf us}\<close>}
\end{flushleft}
We lift operations on such pairs @{term \<open>(uf, us)\<close>} to obtain
\begin{enumerate*}
  \item @{const_typ unions},
  \item @{const_typ uf_ds},
  \item @{const_typ ufe_init}, and
  \item both @{const_typ ufe_union} and its dual
  \item @{const_typ rollback}.
\end{enumerate*}
The meaning of these operations is the following:
\begin{enumerate*}
  \item @{term \<open>unions ufe\<close>} is the list of unions @{term us},
  \item @{term \<open>uf_ds ufe\<close>} represents the current state of the \acrshort{uf} data structure, i.e.\ @{term \<open>ufa_unions uf us\<close>},
  \item @{term \<open>ufe_init n\<close>} initialises the data structure with @{term n} elements and an empty list of unions,
  \item @{term \<open>ufe_union ufe a b\<close>} appends an effective union @{term \<open>(a, b)\<close>} to @{term us}, and
  \item @{term \<open>rollback ufe\<close>} removes the last union from @{term us}.
\end{enumerate*}
Furthermore, we lift the remaining operations on @{typ ufa} to @{typ ufe} via @{const uf_ds},
replacing the prefix \textsf{ufa} by \textsf{ufe}.
For example, we lift @{const ufa_rep_of} by letting @{abbrev \<open>ufe_rep_of ufe\<close>}.

\begin{figure*}
\begin{flushleft}
@{fun explain} \\[0.75em]
@{def explain_partial}
\end{flushleft}
  \caption{A simple implementation of the \opexplain{} operation.\label{fig:explain}
  }
\end{figure*}

At last, we implement the \opexplain{} operation as depicted in \cref{fig:explain}.
The algorithm assumes that the given elements @{term \<open>x\<close>} and @{term \<open>y\<close>} are equal modulo @{term \<open>unions ufe\<close>}.

If @{prop \<open>unions ufe = []\<close>}, then @{term \<open>x\<close>} and @{term \<open>y\<close>} must be equal which we certify with @{term \<open>ReflP x\<close>}.

Otherwise, we distinguish between two cases:
\begin{enumerate*}
  \item The elements @{term \<open>x\<close>} and @{term \<open>y\<close>} are already equal modulo @{term \<open>unions (rollback ufe)\<close>},
    so we proceed recursively with @{term \<open>rollback ufe\<close>}.
  \item In the case where the most recent equation @{prop \<open>a = b\<close>} is necessary for @{prop \<open>x = y\<close>} to hold,
    we either have @{prop \<open>x = a\<close>} and @{prop \<open>b = y\<close>}
    or @{prop \<open>x = b\<close>} and @{prop \<open>a = y\<close>} modulo @{term \<open>unions (rollback ufe)\<close>}.
    Assuming the former holds --- the other case is symmetric ---
    we recursively construct the certificates for @{prop \<open>x = a\<close>} and @{prop \<open>b = y\<close>}.
    Together with the assumption @{prop \<open>a = b\<close>}, we obtain @{prop \<open>x = y\<close>} by transitivity.
\end{enumerate*}
The termination of @{const \<open>explain\<close>} is easily proven
because the length of @{term \<open>unions ufe\<close>} decreases in each recursive call.
Dually, this termination argument gives rise to the following induction principle.
\begin{lemma}[Induction on @{typ ufe}]\label{thm:ufe_induct}
In order to prove @{thm (concl) ufe_induct} for all @{term ufe},
we have two inductive cases, both fixing an arbitrary @{term ufe}:
\begin{enumerate*}
  \item Assume @{prop \<open>ufe_\<alpha> ufe \<subseteq> Id\<close>} as well as @{prop \<open>unions ufe = []\<close>}
    and show @{prop \<open>P ufe\<close>}.
  \item Assume @{prop \<open>eff_union (uf_ds ufe) a b\<close>} as well as @{prop \<open>P ufe\<close>}
    and show @{prop \<open>P (ufe_union ufe a b)\<close>}.
\end{enumerate*}
\end{lemma}

We condense the intuition above into the completeness \lcnamecref{thm:explain_complete} below,
which we prove using the induction principle from \cref{thm:ufe_induct}.
\begin{theorem}[Completeness of @{const explain}\label{thm:explain_complete}]
@{thm [mode=IfThen] explain_complete}
\end{theorem}

The @{const \<open>explain\<close>} function is not sound, though.
This is because it always returns a certificate, even if @{term \<open>x\<close>} and @{term \<open>y\<close>} are not equal modulo @{term \<open>us\<close>}.
To account for this case, we wrap @{const \<open>explain\<close>} into a partial function @{const \<open>explain_partial\<close>} (cf.\ \cref{fig:explain})
that fails if @{prop \<open>x = y\<close>} is not provable.
Soundness and completeness can then be lifted from the soundness of @{const proves_eq} and the completeness of @{const \<open>explain\<close>}, respectively.
Note that membership of @{const \<open>equivcl\<close>} can actually be implemented using \acrshort{uf} operations as the following \lcnamecref{thm:equivcl_iff} demonstrates.
Moreover, it holds that @{prop [mode=iffSpace] \<open>x \<in> Field (ufa_\<alpha> uf) \<longleftrightarrow> x < n\<close>} where @{term n} is the length of the list representing @{term uf}.
\begin{lemma}\label{thm:equivcl_iff}
We have @{thm (lhs) in_equivcl_iff_eq_or_ufe_rep_of_eq} \<^emph>\<open>iff\<close>
@{thm (rhs) in_equivcl_iff_eq_or_ufe_rep_of_eq}.
\end{lemma}
\<close>

section \<open>Efficient Certifying Union-Find Algorithm\label{sec:ufe_efficient}\<close>
text \<open>
In the previous section, we developed an \opexplain{} operation that iteratively removes the most recent union from a list of unions,
identifying which of them, when viewed as equalities, are necessary to prove the input arguments equal.
Iterating through all equalities seems inefficient, though.
Intuitively, we aim to return only those on the path between the arguments,
viewing the equalities as an undirected graph.
To realise this, @{cite \<open>congcl_proofs using citeauthor\<close>}~@{cite \<open>congcl_proofs\<close>} use a \acrshort{uf} data structure
represented as forest of rooted trees as described in \cref{sec:uf_background}.
They modify the data structure such that, for each union between @{term \<open>a\<close>} and @{term \<open>b\<close>},
the newly added edge in the forest gets annotated with @{term \<open>(a, b)\<close>}.
To understand why this allows for a more efficient implementation of the \opexplain{} operation,
suppose that we want to certify that @{term \<open>x\<close>} is equal to @{term \<open>y\<close>}.
Clearly, only the edges of the subtree rooted at the \acrfull{lca} of @{term \<open>x\<close>} and @{term \<open>y\<close>},
as illustrated in \cref{fig:explain'_abs}, are relevant to explain why @{term \<open>x\<close>} is equal to @{term \<open>y\<close>}.
Furthermore, let @{term \<open>(a, b)\<close>} be the most recent union on either of the paths from the \acrshort{lca}
to @{term \<open>x\<close>} or @{term \<open>y\<close>}.
Here, we assume w.l.o.g.\ that @{term \<open>(a, b)\<close>} is on the path to @{term \<open>x\<close>}.
The corresponding edge separates the tree rooted at the \acrshort{lca} into two subtrees as indicated by the patterns, 
one containing @{term \<open>a\<close>} and the other one @{term \<open>b\<close>}.
Moreover, the paths from the \acrshort{lca} can't overlap, so @{term \<open>x\<close>} and @{term \<open>y\<close>} also belong to different subtrees.
Ultimately, to certify the equality of @{term \<open>x\<close>} and @{term \<open>y\<close>},
we recursively prove that @{term \<open>x\<close>} is equal to @{term \<open>a\<close>} and @{term \<open>y\<close>} to @{term \<open>b\<close>}.
Then, we put everything together using transitivity and the equality @{term \<open>a = b\<close>}.
This terminates since @{term \<open>(a, b)\<close>} is the most recent union and we only consider less recent unions in the recursive steps.
All in all, this gives a $\mathcal{O}(k \log n)$ \opexplain{} operation on a \acrshort{uf} data structure with union-by-size,
where $k$ is the number of unions required for an explanation~@{cite \<open>congcl_proofs\<close>}.
This is an improvement over the naive algorithm where we iterate over all (up to $n - 1$) unions.
\begin{figure}
  \centering
  \begin{tikzpicture}[
    >=latex, node distance=0.5cm,
    aside/.append style={pattern=north east lines, pattern color=gray!65},
    bside/.append style={pattern={Dots[radius=0.65pt]}, pattern color=gray!65}
    ]
    \node[draw, circle, preaction={fill, white}, style=bside] (lca) {\acrshort{lca}};
    \begin{pgfonlayer}{background}
      \begin{scope}[shape=isosceles triangle, shape border rotate=90, minimum height=1.3cm, minimum width=1.85cm]
        \node[draw, anchor=north, below left=1.35cm and 3cm of lca.south west, aside] (l) {};
        \path (l.north) -- node[pos=0.54, draw, anchor=north, bside] (m) {} (lca.west);
        \node[draw, anchor=north, yshift=0.25cm, bside] (r) at (lca.south) {};
      \end{scope}
    \end{pgfonlayer}

    \node[draw, circle, above right=0.18cm and 0.05cm of l.south west] (x) {@{term \<open>x\<close>}};
    \node[draw, circle, left=0.1cm of l.east] (a) {@{term \<open>a\<close>}};
    \node[draw, circle, above left=of r.south east] (y) {@{term \<open>y\<close>}};
    \node[draw, circle, above right=of m.south west] (b) {@{term \<open>b\<close>}};
    
    \draw[->] (l.north) -- node[above, sloped] {@{term \<open>(a,b)\<close>}} (m.north);
    \draw[->, dashed] (m.north) -- (lca.west);
    \draw[solid] (lca.north) -- ++(0,0.1);
    \draw[dashed] (lca.north) ++(0,0.1) -- ++(0,0.4);
  \end{tikzpicture}
  \caption{%
    For arguments @{term x} and @{term y},
    @{const \<open>explain'\<close>} considers an edge annotated with @{term \<open>(a, b)\<close>} that separates the subtree
    rooted at the \acrshort{lca} of @{term x} and @{term y} into two subtrees:
    one containing @{term x} and @{term a} and the other one containing @{term y} and @{term b}.\label{fig:explain'_abs}
  }
\end{figure}

To achieve optimal almost constant running time for \opunion{} and \opfind{},
we need path compression in addition to union-by-size.
Path compression, however, is incompatible with the \opexplain{} operation,
so @{cite \<open>congcl_proofs using citeauthor\<close>}~@{cite \<open>congcl_proofs\<close>} propose to maintain two copies of the \acrshort{uf} data structure,
one with and one without path compression.
\<close>

subsection \<open>Implementation\<close>

text \<open>
To obtain an efficient \opexplain{} operation,
we leverage the structure of the \acrshort{uf} data structure,
which is a forest of rooted trees.
We make this structure accessible by defining a function @{const_typ ufa_parent_of} via lifting,
where @{term \<open>ufa_parent_of uf x\<close>} returns the parent of @{term x}.
This function is related to @{const ufa_rep_of} in the obvious way, i.e.\ we have
@{thm [mode=iffText] (concl) ufa_rep_of_refl_iff_ufa_parent_of_refl[where i=x]}
for @{thm (prem 1) ufa_rep_of_refl_iff_ufa_parent_of_refl[where i=x]}.
With this, we formalise the concept of \acrshort{ufe} forests,
define the notion of associated unions within this forest,
and introduce the two auxiliary functions that are the ingredients to the efficient \opexplain{} operation.
\<close>

subsubsection \<open>\acrshort{ufe} forests\<close>
text \<open>
It is often useful to view the forest of rooted trees underpinning the \acrshort{uf} data structure as a graph.
For this purpose,
we use the graph theory library~@{cite \<open>graph_theory\<close>} due to @{cite \<open>graph_theory using citeauthor\<close>},
which is available as an entry of the \acrshort{afp}~@{cite \<open>graph_theory_afp\<close>}.
The library allows us to represent a graph as a record with the fields @{term verts} and @{term arcs}
for its vertices and edges,
where edges are pairs of vertices.
The forest induced by a \acrshort{uf} data structure is then defined as follows.
\begin{flushleft}
@{def_no_typ ufa_forest_of}\\[0.75em]
@{abbrev \<open>ufe_forest_of ufe\<close>}
\end{flushleft}
Note that we choose (somewhat arbitrarily) to direct the edges away from the root
because it aligns more naturally with the notion of a directed rooted tree.
Additionally, this choice ensures compatibility with the @{locale directed_forest} locale,
which we implemented on top of the graph library.
For brevity, we omit the details here and direct the reader to the formalisation,
but suffice it to say that typical properties of forests,
e.g.\ the absence of cycles,
are proved in this locale.
To collect facts that are specific to \acrshort{uf} forests,
we define a locale @{locale ufa_forest} fixing a \acrshort{uf} data structure @{term uf}.
In the context of this locale,
we show that @{term \<open>ufa_forest_of uf\<close>} fulfils the requirements of a @{locale directed_forest},
meaning that the facts in the latter locale transfer over to the former.
Similarly, we introduce the locale @{locale ufe_forest} fixing a \acrshort{ufe} data structure @{term ufe},
where @{term \<open>uf_ds ufe\<close>} is a @{locale ufa_forest}.
\<close>

subsubsection \<open>Associated unions\<close>
text \<open>
As illustrated by \cref{fig:explain'_abs},
we annotate each edge of the \acrshort{ufe} forest with the union that caused its creation,
i.e.\, for an effective union @{term \<open>(a, b)\<close>},
we annotate the newly created edge @{term e} between the @{term \<open>ufe_rep_of ufe a\<close>} and @{term \<open>ufe_rep_of ufe b\<close>}
with @{term \<open>(a, b)\<close>}.
We say that @{term \<open>(a, b)\<close>} is the \<^emph>\<open>associated union\<close> of @{term \<open>e\<close>}.
Since the underlying \acrshort{uf} data structure is expressed in terms of parent pointers,
we actually associate the union @{term \<open>(a, b)\<close>} with @{term \<open>ufe_rep_of ufe a\<close>}.
Furthermore, we use an index into @{term \<open>unions ufe\<close>} rather than storing the union @{term \<open>(a, b)\<close>} directly.
This concept is formalised in the constant @{const_typ au_ds}
whose specific implementation we skip over here;
instead, we only state its characteristic properties:
\begin{itemize}
  \item @{thm [mode=IfThen] au_ds_if_unions_eq_Nil}
  \item For an effective union @{term \<open>(a, b)\<close>}, i.e\ if we have @{thm (prem 1) au_ds_ufe_union_eq_if_eff_union[of _ a b]},
     it holds that @{thm (concl) au_ds_ufe_union_eq_if_eff_union[of _ a b]},
     where @{lemma \<open>(f(x \<mapsto> y)) z = (if z = x then Some y else f z)\<close> by simp}.
\end{itemize}
\<close>

subsubsection \<open>Determining the \acrshort{lca} in a \acrshort{ufe} forest\<close>

lemma %invisible lca_ufa_lca: 
  \<open>{x, y} \<subseteq> Field (ufa_\<alpha> uf) \<Longrightarrow> ufa_rep_of uf x = ufa_rep_of uf y
  \<Longrightarrow> pre_digraph.lca (ufa_forest_of uf) (ufa_lca uf x y) x y\<close>
  by (use ufa_forest.lca_ufa_lca in \<open>unfold verts_ufa_forest_of, simp\<close>)

lemma %invisible ufa_lca_ufa_union:
\<open>eff_union uf a b \<Longrightarrow> {x, y} \<subseteq> Field (ufa_\<alpha> uf) \<Longrightarrow>
  ufa_rep_of (ufa_union uf a b) x = ufa_rep_of (ufa_union uf a b) y \<Longrightarrow>
(ufa_lca (ufa_union uf a b) x y =
  (if ufa_rep_of uf x = ufa_rep_of uf y then ufa_lca uf x y
  else ufa_rep_of uf b))
\<close> by (use ufa_lca_ufa_union in simp_all)

text \<open>
The first auxiliary functions lists the elements on the path from the representative to some element.
Similarly to @{const \<open>ufa_rep_of\<close>}, this function is only well-defined for elements @{term \<open>x \<in> Field (ufa_\<alpha> uf)\<close>} of a given \acrshort{uf} data structure @{term uf}.
Now, let @{term \<open>px\<close>} be the path from the representative of @{term x} to @{term \<open>x\<close>}
and @{term \<open>py\<close>} be the path from @{term \<open>y\<close>}'s representative to @{term \<open>y\<close>}.
Then, every element of a common prefix of @{term \<open>px\<close>} and @{term \<open>py\<close>} is a common ancestor of @{term \<open>x\<close>} and @{term \<open>y\<close>} and
the \acrshort{lca} is exactly the last element of the longest common prefix of @{term \<open>px\<close>} and @{term \<open>py\<close>}. 
\begin{flushleft}
@{fun_input (concl) \<open>awalk_verts_from_rep\<close> [awalk_verts_from_rep.psimps]} \\[0.75em]
@{def ufa_lca}
\end{flushleft}
Again, we abbreviate @{abbrev \<open>ufe_lca ufe\<close>}.
It holds that @{const \<open>ufa_lca\<close>} is indeed an \acrshort{lca}
provided that the arguments share the same representative
and thus are in the same tree of the forest.
For brevity, we omit the definition of @{const [names_short] \<open>pre_digraph.lca\<close>} here and refer to the formalisation instead.
\begin{lemma}\label{thm:lca_ufa_lca}
If @{thm (prem 1) lca_ufa_lca} and @{thm (prem 2) lca_ufa_lca}, then @{thm [names_short] (concl) lca_ufa_lca}.
\end{lemma}
We later prove key properties of \opexplain{} using the induction principle from \cref{thm:ufe_induct},
making it essential to understand how the auxiliary functions behave under effective unions.
The lemma below shows that @{const \<open>ufa_lca\<close>} is invariant under a union @{term \<open>(a, b)\<close>} 
if its arguments share the same representative beforehand.
Otherwise, the union introduces an edge from the representative of @{term \<open>a\<close>} to that of @{term \<open>b\<close>},
connecting the trees that @{term \<open>x\<close>} and @{term \<open>y\<close>} belong to at their respective roots.
Due to the orientation of this new edge,
we know that the \acrshort{lca} of @{term \<open>x\<close>} and @{term \<open>y\<close>} must be the representative of @{term \<open>b\<close>} after performing the union.
\begin{lemma}\label{thm:ufa_lca_ufa_union}
Assume @{thm (prem 1) ufa_lca_ufa_union} and @{thm (prem 2) ufa_lca_ufa_union}.
If @{thm (prem 3) ufa_lca_ufa_union} then @{thm (concl) ufa_lca_ufa_union}.
\end{lemma}
\<close>

subsubsection \<open>Finding the most recent union on a path\<close>
text \<open>
For the second auxiliary function,
we walk the path from the second argument @{term \<open>x\<close>} to the first argument @{term \<open>y\<close>}
and return the most recent associated union, i.e.\ the maximum index with respect to @{term \<open>unions ufe\<close>} on that path.
In Isabelle, we define the following function.
\begin{flushleft}
@{fun_input (concl) find_newest_on_path [find_newest_on_path.psimps]}\\[1em]
\end{flushleft}
As explained earlier, we only use this function on an element in conjunction with its \acrshort{lca} relative to another element.
Thus, there is a path between the two arguments and the function is well-defined for such inputs.
The path, however, can be empty, in which we return @{const \<open>None\<close>}, making the function partial.

As before, we are interested in how the function behaves under effective unions.
Since unions only join trees at their roots, existing paths in the tree are unchanged by unions,
so, for elements in the same equivalence class, the function is invariant under unions.
If, on the other hand, two elements only become part of the same equivalence class as a result of a union @{term \<open>(a, b)\<close>},
then @{term \<open>(a, b)\<close>} must be on the path between those elements
and, as it is the most recent union, the function returns the index of that union.
\begin{lemma}\label{thm:find_newest_on_path_ufe_union_if_reachable}
Assume that @{thm (prem 1) find_newest_on_path_ufe_union_if_reachable}
and @{thm [mode=reachable_from] (prem 2) find_newest_on_path_ufe_union_if_reachable},
then it holds that @{thm (concl) find_newest_on_path_ufe_union_if_reachable}.
\end{lemma}
\<close>

subsubsection \<open>Explain\<close>
text \<open>
With the auxiliary functions in place, we are set to implement the efficient \opexplain{} operation as shown in \cref{fig:explain'}.

Given arguments @{term \<open>x\<close>} and @{term \<open>y\<close>}, we first check whether they are equal
and, if so, we justify their equality by reflexivity.

Otherwise, we determine the \acrshort{lca} of the two elements and the most recent associated union on both of the paths from the elements to the \acrshort{lca}.
Note that, if the \acrshort{lca} is equal to @{term \<open>x\<close>} or to @{term \<open>y\<close>},
the respective path to the \acrshort{lca} is empty;
nevertheless, it is impossible that both @{term \<open>x\<close>} and @{term \<open>y\<close>} are equal to the \acrshort{lca}
because we are in the case where @{prop \<open>x \<noteq> y\<close>}.
Consider, for the sake of an explanation, the case where the most recent union @{term \<open>(ax, bx)\<close>} is on the path to @{term \<open>x\<close>}.
This means, as illustrated in \cref{fig:explain'_abs}, that @{term \<open>x\<close>} and @{term \<open>ax\<close>}
as well as @{term \<open>y\<close>} and @{term \<open>bx\<close>}
are in the same subtree, respectively.
Thus, we call @{term \<open>explain'\<close>} recursively and, using transitivity,
combine the resulting proofs of @{prop \<open>x = ax\<close>} and @{prop \<open>bx = y\<close>} with the assumption that @{prop \<open>ax = bx\<close>}.

The last case, where the most recent union is on the path from @{term y} to the \acrshort{lca},
is symmetric, which, accordingly, requires us to apply the symmetry rule after using the assumption rule on the most recent union.

As we will show below, @{const \<open>explain'\<close>} only terminates for specific inputs.
The domain on which the function is well-defined is again characterised by a domain predicate
@{const_typ explain'_dom}.
\begin{figure*}[t]
\begin{flushleft}
@{fun_input [mode=let_break] (concl) explain' [explain'.psimps]}
\end{flushleft}
  \caption{Efficient version of the \opexplain{} operation.\label{fig:explain'}}
\end{figure*}
\<close>

subsection \<open>Correctness\label{sec:explain'_correct}\<close>
(*<*)
context
  fixes x y :: nat and ufe :: ufe
  assumes in_Field_ufe_\<alpha>[simp]: "x \<in> Field (ufe_\<alpha> ufe)" "y \<in> Field (ufe_\<alpha> ufe)"
  assumes ufe_rep_of_eq: "ufe_rep_of ufe x = ufe_rep_of ufe y"
begin
(*>*)

text \<open>
Verifying the functional correctness of @{const \<open>explain'\<close>} requires
proving termination as well as soundness and completeness.
We prove termination directly, while we obtain soundness and completeness
by showing extensional equality of @{const \<open>explain'\<close>} and @{const \<open>explain\<close>}.
As @{const \<open>explain'\<close>}, like @{const \<open>explain\<close>}, does not validate its input,
we assume for the remainder of this \lcnamecref{sec:explain'_correct} that
\begin{enumerate*}
  \item @{lemma \<open>{x, y} \<subseteq> Field (ufe_\<alpha> ufe)\<close> by simp} and
  \item @{thm ufe_rep_of_eq}.
\end{enumerate*}

To establish termination of @{const \<open>explain'\<close>},
we first prove that termination remains invariant under an effective union
using the invariance of @{term find_newest_on_path} and @{const ufe_lca} under an effective union (see \cref{thm:ufa_lca_ufa_union,thm:find_newest_on_path_ufe_union_if_reachable}).
From this, the termination of @{const explain'} follows by induction on @{typ ufe}.
\begin{lemma}\label{thm:explain'_dom_ufe_union}
Assume @{thm (prem 1) explain'_dom_ufe_union[OF _ in_Field_ufe_\<alpha> ufe_rep_of_eq]}
and @{thm (prem 2) explain'_dom_ufe_union[OF _ in_Field_ufe_\<alpha> ufe_rep_of_eq]},
then it holds that
@{thm (concl) explain'_dom_ufe_union[OF _ in_Field_ufe_\<alpha> ufe_rep_of_eq]}.
\end{lemma}
\begin{theorem}[Termination]\label{thm:explain'_dom}
@{thm explain'_dom_if_ufe_rep_of_eq[OF in_Field_ufe_\<alpha> ufe_rep_of_eq]}
\end{theorem}
By \cref{thm:explain'_dom} and the invariance of the auxiliary functions under effective unions,
we deduce that @{const \<open>explain'\<close>} is also invariant under effective unions.
\begin{lemma}\label{thm:explain'_ufe_union}
@{thm [mode=IfThen] explain'_ufe_union[OF in_Field_ufe_\<alpha> ufe_rep_of_eq]}
\end{lemma}
Given the definition of @{const explain},
we now understand the behaviour of both @{const explain} and @{const explain'} under effective unions.
Thus we conclude, by induction on @{typ ufe}, that @{const explain} is extensionally equal to @{const explain'}.
\begin{theorem}[Correctness]\label{thm:explain_eq_explain'}
@{thm explain_eq_explain'[OF in_Field_ufe_\<alpha> ufe_rep_of_eq]}
\end{theorem}
\<close>

(*<*) end (*>*)
  
section \<open>Refinement to an Efficiently Executable Specification\label{sec:refinement}\<close>
text \<open>
In the previous section, we described a refined recursion scheme for \opexplain{} that avoids iterating through all input equalities.
To turn this into an efficiently executable specification, we refine two aspects of the \acrshort{ufe} data structure.

First, we employ the union-by-size heuristic~@{cite \<open>uf_by_size\<close>},
i.e.\ we always attach the tree with fewer elements to the one with more elements during a \opunion{}. 
This ensures that all trees in the \acrshort{uf} data structure have height at most $\mathcal{O}(\log n)$
where $n$ is the number of elements of the data structure.
This yields $\mathcal{O}(\log n)$ running time for \opunion{} and \opfind{} as well as $\mathcal{O}(k \log n)$ for \opexplain{}.

Then, we take this functional \acrshort{ufe} data structure
and refine it to an imperative specification, thereby giving a concrete implementation.
In doing that, we are careful to refine lists by arrays,
guaranteeing constant time access to e.g.\ the parent of an element in the \acrshort{uf} data structure.
Additionally, we maintain a copy of the \acrshort{uf} data structure with path compression
as described in \cref{sec:ufe_efficient},
improving the performance of \opunion{} and \opfind{} to almost constant running time.
\<close>

subsection \<open>Union-by-size Heuristic\<close>
text \<open>
As mentioned in \cref{sec:uf_hol}, our formalisation of the \acrshort{uf} data structure extends a formalisation by @{cite \<open>uf_isabelle using citeauthor\<close>}~@{cite \<open>uf_isabelle and uf_isabelle_afp\<close>}.
The latter formalisation already introduces the union-by-size heuristic,
but it does so during the refinement to Imperative HOL.
We raise the union-by-size heuristic to the purely functional level of HOL,
which lets us exploit Isabelle's lifting and transfer infrastructure~@{cite \<open>lifting_transfer\<close>}.
In addition, we introduce another optimisation: we represent the \acrshort{uf} data structure as a single list of integers,
eliminating the data structure recording the size information.

As a prerequisite for the union-by-size heuristic,
we define a function that determines the equivalence class of an element @{term \<open>x\<close>} in the data structure @{term \<open>uf\<close>}.
More specifically, we use the relational image operator @{term \<open>(``)\<close>} on the equivalence relation @{term \<open>ufa_\<alpha> uf\<close>}
to obtain all the elements that are equivalent to @{term \<open>x\<close>}.
The associated size of an element is then the cardinality of its equivalence class.
\begin{flushleft}
\begin{minipage}{0.48\linewidth}
@{def ufa_eq_class [ufa_eq_class_def[where i=x]]}
\end{minipage}
\hfill
\begin{minipage}{0.48\linewidth}
@{def ufa_size [ufa_size_def[where i=x]]}
\end{minipage}
\end{flushleft}
With this, we perform the \opunion{} operation such that the element with the smaller size is always passed as the first argument. 
The underlying implementation of the data structure always updates the parent pointer of the representative of the first argument to the representative of the second argument,
thus yielding a \opunion{} operation that attaches smaller trees in the \acrshort{uf} forest to larger trees.
\begin{flushleft}
@{def ufa_union_size}
\end{flushleft}
Looking closely at the definition,
we see that @{const \<open>ufa_size\<close>} is only ever used on the representative of an element.
Moreover, in the representation of @{typ \<open>ufa\<close>} as a list of natural numbers,
the representatives are exactly those where the parent pointer is self-referential.
Ultimately, we integrate both insights and encode the \acrshort{uf} data structure
as an \acrshort{adt} @{typ ufsi}, which is implemented by a list of integers:
we use a negative number to indicate that a parent pointer is self-referential,
using the absolute value of the number as the size at the same time.
The other parent pointers are encoded as non-negative numbers as before.
\<close>

subsection \<open>From Functional to Imperative Specification\label{sec:imperative_hol}\<close>
text \<open>
To obtain an imperative specification,
we formulate a refined version of the \opexplain{} operation in the heap monad provided by the Imperative HOL~@{cite \<open>imperative_hol\<close>} framework.
This framework comes with an extension to Isabelle's code generator allowing us to generate imperative code in several target languages including \acrlong{sml}. 
Since Imperative HOL only comes with limited capabilities to analyse programs in its heap monad, 
we bring in @{cite \<open>uf_isabelle using citeauthor\<close>}'s~@{cite \<open>uf_isabelle\<close>} separation logic framework for Imperative HOL.
The framework lets us reason about the state of the heap using heap assertions,
which describe data stored on the heap and their properties.
All our data structures are ultimately represented as arrays on the heap,
so we ensure with heap assertions that the content of the arrays represents our data structures throughout the operations we perform on them. 

With the automation provided by @{cite \<open>uf_isabelle using citeauthor\<close>}'s framework,
it is straightforward to implement the operations and prove their correctness.
The process is similar to the refinement of the \acrshort{uf} data structure~@{cite \<open>uf_isabelle\<close>}.
Thus, we forgo a discussion of how individual functions are refined and refer to the formalisation instead.

The only remaining noteworthy detail is the representation of the \acrshort{ufe} data structure in Imperative HOL.
Our implementation consists of a \acrshort{uf} data structure,
a partial function recording the associated union of each parent pointer,
and the chronological list of unions.
The \acrshort{uf} data structure is represented as an array of integers.
For the associated unions, we use an array of options to represent the partial function.
This works as the domain is actually fixed,
i.e.\ the domain of the partial function is exactly the elements of the \acrshort{uf} data structure,
which, in our case, are the natural numbers up to some fixed @{term \<open>n\<close>}.
Lastly, we represent the list of unions as a dynamic array using the type @{type \<open>array_list\<close>}.
The type wraps an array together with a natural number indicating how many cells of the array,
counting from the first position,
are occupied.
We can then grow the array dynamically by pushing elements to the end,
doubling its size each time it becomes fully occupied.
Hence, we achieve amortised constant running time for adding new unions and constant time random access,
which are the operations required by the \opexplain{} operation. 
We assemble these components into a record type @{typ ufe_imp}.
Finally, we extend @{typ ufe_imp} with a \acrshort{uf} data structure with path compression,
thus obtaining the record type @{typ ufe_c_imp}.

We define a heap assertion @{const_typ is_ufe}
that relates instances of the \acrshort{adt} @{typ \<open>ufe\<close>} with instances of @{typ ufe_imp}.
The assertion just relates the components of @{typ \<open>ufe_imp\<close>} with the corresponding functions on @{typ ufe},
so we omit it for brevity.
The only aspect requiring further explanation is the natural number @{term \<open>n\<close>} in the first argument.
Its purpose is to ensure that the elements of the initial \acrshort{uf} data structure
and the domain of the associated unions are both the numbers up to @{term \<open>n\<close>}.
To obtain the assertion @{const_typ is_ufe_c},
we additionally require that the representatives in the \acrshort{uf} data structure with path compression
corresponds to the representatives in the \acrshort{ufe} data structure.

Again, refining the operations on @{typ ufe_c_imp} is routine;
so, we only show the final correctness theorem for @{const \<open>explain_partial_imp\<close>},
an imperative version of @{const \<open>explain'\<close>} that ensures soundness
following the approach of @{const \<open>explain_partial\<close>} in \cref{sec:ufe_simple}.
\begin{theorem}
We prove the following Hoare triple, which entails total correctness in the Separation Logic Framework~@{cite \<open>uf_isabelle_afp\<close>}:
@{thm explain_partial_imp_rule}
\end{theorem}
\<close>

section \<open>Benchmarking the Exported Code\<close>
(*<*)
definition wide :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "wide n \<equiv> [(x, x + 1). x \<leftarrow> [0..<2^n - 1]]"

fun balanced :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "balanced 0 = []"
| "balanced (Suc n) =
    [(2 * x, 2 * x + 1). x \<leftarrow> [0..<2^n]] @
    [(2 * x, 2 * y). (x, y) \<leftarrow> balanced n]"

(*>*)

text \<open>
In the previous section, we obtained an executable imperative specification of the \acrshort{ufe} data structure,
from which we can export code to functional target languages while
utilising their respective support for imperative programming like destructive array updates in \acrfull{sml}.
This raises the question whether exporting imperative code to a functional language is a good fit, performance wise. 
In addition, \acrshort{smt} solvers are usually implemented in imperative language such as \Cpp{}.
Therefore, we compare the exported \acrshort{sml} code against
a hand-written \Cpp{} implementation of the executable specification.

We analyse the performance on two test cases:
\begin{enumerate*}
  \item in the former case, the the number of proof steps for an \opexplain{} operation is linear in the number of elements but the
    depth of the \acrshort{uf} forest is constant,
  \item while in the latter, the depth of the \acrshort{uf} forest as well as the number of proof steps
    is logarithmic in the number of elements.
\end{enumerate*}
For both cases, we choose a natural number $n$, initialise the \acrshort{ufe} data structure with
$2^n$ elements, perform \opunion{} operations that results in the desired \acrshort{uf} forest,
and finally perform a number (i.e.\ 1000 and 100000, respectively) of \opexplain{} operations with the arguments drawn from
the uniform distribution over $0,\ldots,2^n - 1$.
We identify the test cases by functions @{const wide} and @{const balanced},
which both have type @{typeof wide}.
\cref{fig:test_cases} illustrates the resulting \acrshort{uf} forests or, more specifically, trees.

\begin{figure}
\centering
\begin{subfigure}[b]{0.39\textwidth}
\centering
\begin{tikzpicture}[
  every node/.append style={draw, ellipse, minimum width=2em},
  sibling distance=1.2cm,
  >=stealth, edge from parent/.append style={draw, <-}]
  \node {$0$}
    child {node (1) {$1$}}
    child {node[draw=none] {$\ldots$}}
    child {node {$2^n - 1$}};
\end{tikzpicture}
\subcaption{\acrshort{uf} tree for @{term \<open>wide n\<close>}.}
\end{subfigure}
\hfill
\begin{subfigure}[b]{0.58\textwidth}
\centering
\begin{tikzpicture}[
  every node/.append style={draw, circle},
  sibling distance=0.9cm, level distance = 0.725cm,
  >=stealth, edge from parent/.append style={draw, <-}]
  \node (2) {$0$}
    child {node (21) {$1$}}
    child {node {$2$}
      child {node {$3$}}
      child[missing] {}
    }
    child {node {$4$}
      child {node {$5$}}
      child {node {$6$}
        child {node {$7$}}
        child[missing] {}
      }
    };
  \node[left=2cm of 2] (1) {$0$}
    child {node (11) {$1$}}
    child {node {$2$}
      child {node {$3$}}
      child[missing] {}
    };
  \node[left=1cm of 1] (0) {$0$}
    child {node (01) {$1$}}
    child[missing] {};
\end{tikzpicture}
\subcaption{\acrshort{uf} trees for @{term \<open>balanced n\<close>} where @{prop \<open>n \<in> {1::nat,2,3}\<close>}.}
\end{subfigure}
\caption{The \acrshort{uf} trees resulting from performing the \opunion{} operations with the arguments given by @{const wide} and @{const balanced}.\label{fig:test_cases}}
\end{figure}

To perform our measurements, we compiled the exported Standard ML code with MLton\footnote{\<^url>\<open>http://mlton.org\<close>} version \texttt{20210117},
and the \Cpp{} code with \Gpp{}\footnote{\<^url>\<open>https://gcc.gnu.org\<close>} version \texttt{13.3.0}.
The results are shown in \cref{tab:benchmark}.
The code export of Isabelle uses arbitrary sized integers to ensure soundness with respect to the executable specification
while the \Cpp{} uses machine integers,
so we also include a version of the exported code, annotated by (Int), that uses machine integers.

The observed running time overhead of using arbitrary sized integers is roughly a factor of 2--2.5,
matching that observed by @{cite \<open>refine_monadic using citeauthor\<close>}~@{cite \<open>refine_monadic\<close>}.
The difference between \acrshort{sml} with machine integers and \Cpp{} is
roughly a factor of 2 for the \opunion{} operations and
a factor of 1.5 for the \opexplain{} operations throughout both test cases.
The second test case exhibits some outliers:
notably, between $n = 23$ to $n = 24$ for \acrshort{sml} and
between $n = 24$ and $n = 25$ for \acrshort{sml} (Int).
This variance is due to garbage collection becoming a significant factor at large heap sizes,
e.g. for $n = 25$ the heap grows to above 5 gigabytes.
\begin{table}[t]
\centering
\begin{subtable}{\textwidth}
\centering
\begin{tabular}{l@ {\hskip 6pt} l@ {\hskip 6pt}l@ {\hskip 6pt}l@ {\hskip 6pt}l@ {\hskip 6pt}l}
\toprule
Impl. & 18 & 19 & 20 & 21 & 22\\
\midrule
SML & 0.025/18.428 & 0.075/36.129 & 0.072/70.696 & 0.157/140.209 & 0.393/280.684 \\
SML (Int) & 0.011/8.341 & 0.011/16.249 & 0.024/29.695 & 0.051/62.442 & 0.092/131.532 \\
\Cpp{} & 0.004/3.672 & 0.007/7.354 & 0.015/15.113 & 0.031/31.120 & 0.062/71.066 \\
\bottomrule
\end{tabular}
\subcaption{Running times for @{term \<open>wide n\<close>}.}
\end{subtable}

\begin{subtable}{\textwidth}
\centering
\begin{tabular}{l@ {\hskip 6pt}l@ {\hskip 6pt}l@ {\hskip 6pt}l@ {\hskip 6pt}l@ {\hskip 6pt}l}
\toprule
Impl. & 22 & 23 & 24 & 25 & 26\\
\midrule
SML & 0.722/1.879 & 0.899/2.583 & 1.552/2.082 & 4.770/2.396 & 14.610/3.014 \\
SML (Int) & 0.174/0.750 & 0.227/0.781 & 0.695/0.900 & 2.474/0.920 & 2.785/1.027 \\
\Cpp{} & 0.087/0.369 & 0.199/0.460 & 0.350/0.550 & 0.752/0.620 & 1.451/0.728 \\
\bottomrule
\end{tabular}
\subcaption{Running times for @{term \<open>balanced n\<close>}.}
\end{subtable}
\caption{
  Wall-clock running times in seconds as measured on an Intel Core i7 4790k.
  For each $n$, we recorded the running time for performing the \opunion{} operations and the \opexplain{} operations (separated by a slash). \label{tab:benchmark}}
\end{table}

Overall, we found that employing a functional language results in a modest performance overhead when working with machine integers.
We note that to soundly export such code,
it would be necessary to change the element type of the \acrshort{ufe} data structure from natural numbers to fixed-width words.
This is plausible future work, as the number of elements is fixed for any instance of the data structure,
and the only necessary operations on the elements are comparisons and indexing into arrays --- operations that fixed-width words also support.
\<close>

section \<open>Conclusion and Future Work\<close>
text \<open>
We developed a formalisation of the \acrshort{uf} data structure with an \opexplain{} operation 
based on a paper by @{cite \<open>congcl_proofs using citeauthor\<close>}~@{cite \<open>congcl_proofs\<close>}.
The formalisation includes a more naive version of the \opexplain{} operation than the one presented in the paper.
We proved their equivalence as well as their soundness, completeness, and termination.
Finally, we refined the functional representation of the data structure to an imperative one, allowing us to export efficient code.

In future work, we plan to verify the other variant of the \acrshort{ufe} data structure as presented by @{cite \<open>congcl_proofs using citeauthor\<close>}.
This variant also forms the basis of their congruence closure algorithm, which is the logical next step.
Ultimately, we want to work towards a verified, proof-producing version of the Nelson-Oppen algorithm~@{cite \<open>nelson_oppen\<close>} for the combination of theories.

\subsubsection*{Acknowledgements}
We thank Tobias Nipkow for reviewing a draft version of this paper and the anonymous referees for their thoughtful feedback.

{\fontsize{9}{15}\selectfont
\subsubsection*{\fontsize{9}{15}\selectfont Disclosure of Interests}
The authors have no competing interests to declare that are relevant to the content of this article.
}

\<close>

text \<open>
\bibliographystyle{splncs04nat}
\bibliography{root}
\<close>

end
