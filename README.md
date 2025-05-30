# Formalisation of the Union-Find-Explain Algorithm
This directory contains the supplementary material for the paper, i.e. the formalisation of the Union-Find-Explain algorithm in Isabelle/HOL.
The formalisation is structured as follows:

- `Tree_Theory/`. We extend the `Graph_Theory` entry of the AFP with a definition of directed trees and forests. Furthermore, we define the least common ancestor in a graph.
- `Union_Find/`. We formalise the basic Union-Find data structure including union-by-size and path compression. Additionally, we define a version of the data structure that encodes the size information more efficiently using a list of integers. The operations are the data structure are refined to Imperative HOL such that efficient imperative code can be exported.
- `Union_Find_Explain/`. We formalise the Union-Find-Explain data structure by first formalising a simple, but inefficient, version of the explain operation and prove its soundness and completeness.
    Then, we formalise the more complex recursive implementation from the original paper and show that it is extensionally equal to the simple version.
    Finally, we refine the explain operation to Imperative HOL in order to be able to export efficient imperative code.
- `paper/CADE`. This directory contains the Isabelle theories that produce the paper.
- `performance`. This directory contains the files for generating the results of the benchmarking section. Execute `performance/bench.bash` to get the results.

## Prerequisites
The formalisations uses Isabelle2025, which can be obtained from the [Isabelle website](https://isabelle.in.tum.de/).
Furthermore it relies on entries of the [*Archive of Formal Proofs* (AFP)](https://www.isa-afp.org), which can be obtained as described on the [download page](https://www.isa-afp.org/download/).

## Running the Formalisation
Let `$AFP` be the path you downloaded the AFP to.
You can build the formalisation and the paper, which non-interactively checks all the proofs, by executing the command
```
$ isabelle build -d $AFP/thys -D . -v
```
After executing this command, the paper will be in `paper/CADE/build`.
In order to export the code from the imperative specification to the file `Union_Find_Explain/export/UFE.ML`, execute
```
$ isabelle build -d $AFP/thys -d . -e Union_Find_Explain
```
You can browse the theories interactively with the following command.
Here, we open the theory file that produces the paper so you directly see how the paper corresponds to the formalisation.
Note that jEdit displays the buffer of the ROOT file by default so you need to switch to the buffer `Document.thy`.
```
$ isabelle jedit -d $AFP/thys -d . -R Tree_Theory paper/CADE/Document.thy
```
You can also browse the Isabelle theories as HTML files.
To do this, execute the following command and open the directory that you see on the console with your browser.
```
$ isabelle build -d $AFP/thys -D . -o browser_info
```
