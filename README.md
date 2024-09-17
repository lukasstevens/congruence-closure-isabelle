# Formalisation of the Union-Find-Explain Algorithm
This directory contains the supplementary material for the paper, i.e. the formalisation of the Union-Find-Explain algorithm in Isabelle/HOL.
The formalisation is structured as follows:

- `Tree_Theory/`. We extend the `Graph_Theory` entry of the AFP with a definition of directed trees. Furthermore, we define the least common ancestor in a graph.
- `Union_Find/`. We formalise the basic Union-Find data structure including the union-by-size heuristic. Additionally, we define a version of the data structure that encodes the size information more efficiently using a list of integers. The operations are the data structure are refined to Imperative HOL such that efficient imperative code can be exported.
- `Union_Find_Explain/`. We formalise the Union-Find-Explain data structure by first formalising a simple, but inefficient, version of the explain operation and prove its soundness and completeness.
    Then, we formalise the more complicated recursive implementation from the original paper and show that it is extensionally equal to the simple version.
    Finally, we refine the explain operation to Imperative HOL in order to be able to export efficient imperative code.
    
    Additionally, we formalise dynamic arrays in Imperative HOL.

## Prerequisites
The formalisations uses Isabelle2024, which is available on the [official website](https://isabelle.in.tum.de/).

Since the formalisation relies on entries of the [*Archive of Formal Proofs* (AFP)](https://www.isa-afp.org), you need to download it as explained on the [website](https://www.isa-afp.org/download/).
Then, you need to register it as a component to make Isabelle aware of it.
Instructions for doing are on the [website](https://www.isa-afp.org/help/).

## Running the Formalisation
You can build the formalisation, which non-interactively checks all the proofs, by executing the command
```
isabelle build -d . Union_Find_Explain
```
If you want to open a theory file, e.g. `Union_Find_Explain/Explain_Imp.thy`, in interactively in the editor, you run the command
```
isabelle jedit -d . -R Union_Find Union_Find_Explain/Explain_Imp.thy
```
