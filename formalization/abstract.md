In the sum network creation game, each player pays a price $\alpha$ per edge
it purchases and the sum of its undirected distances to all other players.
An unreachable vertex contributes infinite distance. A Nash equilibrium is
stable under unilateral changes to the entire purchased edge set.

This development formalizes Dippel and Vetta's general tree theorem at
$\alpha>2n$. It proves that an equilibrium at $\alpha>n$ has girth at least
eight and that it is a tree for up to ten players. It also checks an improved
deletion bound for purchases into degree-two vertices of maximal cyclic
blocks, and a weighted addition inequality for block attachments.

The formal game definitions adapt the Apache-2.0 sources of
[lax-899194](https://laxarchive.org/lax-899194/index.html), originally developed
in [the upstream repository](https://github.com/clemenskuske/network-creation-tree-equilibria/tree/ab7c839f02a08a417dcf6ccbf6f447790ddd5db3).
The archive package changes the namespace and adds mathematical definitions
and proofs. OpenAI Codex assisted in developing and documenting the Lean
proofs and their computational certificates.

The full Tree Conjecture for all player counts at $\alpha>n$ is open in this
development. The attached repository also records mathematical arguments
with external integer checks for additive refinements of the general bound.
