# Formalisation of the Union-Find-Explain Algorithm
This directory contains the supplementary material for the paper, i.e. the formalisation of the Union-Find-Explain algorithm in Isabelle/HOL.
The formalisation is structured as follows:

- `Tree_Theory/`. We extend the `Graph_Theory` entry of the AFP with a definition of directed trees and forests. Furthermore, we define the least common ancestor in a graph.
- `Union_Find/`. We formalise the basic Union-Find data structure including union-by-size and path compression. Additionally, we define a version of the data structure that encodes the size information more efficiently using a list of integers. The operations are the data structure are refined to Imperative HOL such that efficient imperative code can be exported.
- `Union_Find_Explain/`. We formalise the Union-Find-Explain data structure by first formalising a simple, but inefficient, version of the explain operation and prove its soundness and completeness.
    Then, we formalise the more complicated recursive implementation from the original paper and show that it is extensionally equal to the simple version.
    Finally, we refine the explain operation to Imperative HOL in order to be able to export efficient imperative code.
     
    Additionally, we formalise dynamic arrays in Imperative HOL.
- `paper/CADE`. This directory contains the Isabelle theories that produce the paper.

## Prerequisites
The formalisations uses Isabelle2025-RC2, which can be obtained as follows.
```
$ hg clone https://isabelle.in.tum.de/repos/isabelle isabelle
$ isabelle/Admin/init -r Isabelle2025-RC2 
```
Furthermore it relies on entries of the [*Archive of Formal Proofs* (AFP)](https://www.isa-afp.org), which can be obtained as follows.
```
$ hg clone https://foss.heptapod.net/isa-afp/afp-2025 afp-2025
```

## Running the Formalisation
Let `$ISABELLE` be the path that you cloned Isabelle to and `$AFP` be the path you cloned the AFP to.
You can build the formalisation and the paper, which non-interactively checks all the proofs, by executing the command
```
$ $ISABELLE/bin/isabelle build -d $AFP/thys -D . -v
```
After executing this command, the paper will be in `paper/CADE/build`.
In order to export the code from the imperative specification to the file `Union_Find_Explain/export/UFE.ML`, execute
```
$ $ISABELLE/bin/isabelle build -d $AFP/thys -d . -e Union_Find_Explain
```
You can browse the theories interactively with the following command.
Here, we open the theory file that produces the paper so you directly see how the paper corresponds to the formalisation.
Note that jEdit displays the buffer of the ROOT file by default so you need to switch to the buffer `Document.thy`.
```
$ $ISABELLE/bin/isabelle jedit -d $AFP/thys -d . -R Tree_Theory paper/CADE/Document.thy
```
You can also browse the Isabelle theories as HTML files.
To do this, execute the following command and open the directory that you see on the console with your browser.
```
$ $ISABELLE/bin/isabelle build -d $AFP/thys -D . -o browser_info
```
